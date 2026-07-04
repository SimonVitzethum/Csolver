//! MSIR types and the target data layout.
//!
//! Types carry exactly the information memory-safety reasoning needs: scalar
//! width, what a pointer points to (for element-size arithmetic), and
//! aggregate shape (for field offsets). Floating-point and vector types are
//! modelled as opaque scalars of a given byte size for now — they are never
//! pointers, so they do not affect spatial/temporal safety.

use std::fmt;

/// An MSIR type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// The zero-sized unit type.
    Unit,
    /// A boolean (`i1`); one byte in memory.
    Bool,
    /// An integer of the given bit width (`1..=128`).
    Int {
        /// Bit width.
        bits: u32,
    },
    /// An opaque scalar occupying `bytes` bytes (e.g. `f32`, `f64`, SIMD).
    Opaque {
        /// Size in bytes.
        bytes: u64,
        /// Alignment in bytes (a power of two).
        align: u64,
    },
    /// A typed pointer to `pointee`.
    Ptr {
        /// The pointed-to type (the unit of pointer arithmetic).
        pointee: Box<Type>,
    },
    /// A fixed-length array.
    Array {
        /// Element type.
        elem: Box<Type>,
        /// Number of elements.
        len: u64,
    },
    /// A struct with the given field types, laid out C-style with padding.
    Struct {
        /// Field types in declaration order.
        fields: Vec<Type>,
        /// `true` for a *packed* struct (`<{ … }>`): no inter-field padding and
        /// byte alignment. Modelling a packed struct as padded would oversize it
        /// and misplace its fields — a false-PASS hole — so the flag is honoured
        /// in the size/alignment/offset queries.
        packed: bool,
    },
}

impl Type {
    /// A pointer to `pointee`.
    pub fn ptr(pointee: Type) -> Type {
        Type::Ptr {
            pointee: Box::new(pointee),
        }
    }

    /// An integer type of the given width.
    pub fn int(bits: u32) -> Type {
        Type::Int { bits }
    }

    /// Whether this is a pointer type.
    pub fn is_ptr(&self) -> bool {
        matches!(self, Type::Ptr { .. })
    }

    /// The size of this type in bytes under `layout`, or `None` if it cannot be
    /// determined (which must degrade the verdict, never silently pass).
    pub fn size_bytes(&self, layout: &DataLayout) -> Option<u64> {
        Some(match self {
            Type::Unit => 0,
            Type::Bool => 1,
            Type::Int { bits } => (*bits as u64).div_ceil(8),
            Type::Opaque { bytes, .. } => *bytes,
            Type::Ptr { .. } => layout.pointer_size,
            Type::Array { elem, len } => {
                let stride = elem.stride_bytes(layout)?;
                stride.checked_mul(*len)?
            }
            Type::Struct { fields, packed } => {
                let mut offset: u64 = 0;
                let mut max_align: u64 = 1;
                for field in fields {
                    let a = if *packed { 1 } else { field.align_bytes(layout)? };
                    max_align = max_align.max(a);
                    offset = align_up(offset, a)?;
                    offset = offset.checked_add(field.size_bytes(layout)?)?;
                }
                // Tail-pad to the struct's own alignment (packed ⇒ align 1 ⇒ none).
                align_up(offset, max_align)?
            }
        })
    }

    /// The alignment of this type in bytes under `layout`.
    pub fn align_bytes(&self, layout: &DataLayout) -> Option<u64> {
        Some(match self {
            Type::Unit => 1,
            Type::Bool => 1,
            Type::Int { bits } => {
                let bytes = (*bits as u64).div_ceil(8).max(1).next_power_of_two();
                bytes.min(layout.max_int_align)
            }
            Type::Opaque { align, .. } => *align,
            Type::Ptr { .. } => layout.pointer_align,
            Type::Array { elem, .. } => elem.align_bytes(layout)?,
            Type::Struct { fields, packed } => {
                if *packed {
                    1
                } else {
                    let mut a = 1;
                    for f in fields {
                        a = a.max(f.align_bytes(layout)?);
                    }
                    a
                }
            }
        })
    }

    /// The stride between consecutive array elements: size rounded up to align.
    pub fn stride_bytes(&self, layout: &DataLayout) -> Option<u64> {
        let size = self.size_bytes(layout)?;
        let align = self.align_bytes(layout)?;
        align_up(size, align)
    }
}

/// Round `value` up to the next multiple of `align` (a power of two), or
/// `None` on overflow.
fn align_up(value: u64, align: u64) -> Option<u64> {
    debug_assert!(align.is_power_of_two(), "alignment must be a power of two");
    let mask = align - 1;
    value.checked_add(mask).map(|v| v & !mask)
}

/// Target-specific sizes and alignments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DataLayout {
    /// Pointer size in bytes.
    pub pointer_size: u64,
    /// Pointer alignment in bytes.
    pub pointer_align: u64,
    /// Maximum alignment any integer type receives (ABI cap).
    pub max_int_align: u64,
}

impl DataLayout {
    /// The layout for a 64-bit little-endian target (x86-64 / AArch64).
    pub const LP64: DataLayout = DataLayout {
        pointer_size: 8,
        pointer_align: 8,
        max_int_align: 8,
    };

    /// The layout for a 32-bit target.
    pub const ILP32: DataLayout = DataLayout {
        pointer_size: 4,
        pointer_align: 4,
        max_int_align: 8,
    };
}

impl Default for DataLayout {
    fn default() -> Self {
        DataLayout::LP64
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unit => f.write_str("()"),
            Type::Bool => f.write_str("i1"),
            Type::Int { bits } => write!(f, "i{bits}"),
            Type::Opaque { bytes, .. } => write!(f, "opaque{bytes}"),
            Type::Ptr { pointee } => write!(f, "*{pointee}"),
            Type::Array { elem, len } => write!(f, "[{elem}; {len}]"),
            Type::Struct { fields, packed } => {
                if *packed { f.write_str("<")?; }
                f.write_str("{")?;
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{field}")?;
                }
                f.write_str("}")?;
                if *packed { f.write_str(">")?; }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_sizes() {
        let l = DataLayout::LP64;
        assert_eq!(Type::Bool.size_bytes(&l), Some(1));
        assert_eq!(Type::int(32).size_bytes(&l), Some(4));
        assert_eq!(Type::int(64).size_bytes(&l), Some(8));
        assert_eq!(Type::int(1).size_bytes(&l), Some(1));
        assert_eq!(Type::ptr(Type::int(8)).size_bytes(&l), Some(8));
    }

    #[test]
    fn array_stride_and_size() {
        let l = DataLayout::LP64;
        let arr = Type::Array {
            elem: Box::new(Type::int(32)),
            len: 10,
        };
        assert_eq!(arr.size_bytes(&l), Some(40));
        assert_eq!(arr.align_bytes(&l), Some(4));
    }

    #[test]
    fn struct_layout_with_padding() {
        let l = DataLayout::LP64;
        // { i8, i32 } -> i8 at 0, pad to 4, i32 at 4, size 8, align 4.
        let s = Type::Struct {
            packed: false,
            fields: vec![Type::int(8), Type::int(32)],
        };
        assert_eq!(s.align_bytes(&l), Some(4));
        assert_eq!(s.size_bytes(&l), Some(8));

        // { i8, ptr } -> i8 at 0, pad to 8, ptr at 8, size 16, align 8.
        let s2 = Type::Struct {
            packed: false,
            fields: vec![Type::int(8), Type::ptr(Type::Unit)],
        };
        assert_eq!(s2.align_bytes(&l), Some(8));
        assert_eq!(s2.size_bytes(&l), Some(16));
    }
}
