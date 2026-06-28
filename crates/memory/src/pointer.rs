//! Symbolic pointers: a provenance plus a (possibly symbolic) byte offset.
//!
//! A pointer's *provenance* is the allocation it was derived from. CSolver
//! follows the Rust/LLVM provenance model: a pointer may only access the region
//! it has provenance for, and integer→pointer casts produce pointers with
//! [`Provenance::Unknown`] provenance unless re-established.

use crate::region::RegionId;
use std::fmt;

/// Where a pointer's authority to access memory comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Provenance {
    /// The null pointer: dereferencing it is a null-deref violation.
    Null,
    /// Derived from a specific region.
    Region(RegionId),
    /// Provenance lost (e.g. via `int -> ptr`): may not be safely dereferenced
    /// without an explicit assumption re-establishing it.
    Unknown,
    /// Known to be invalid (e.g. derived from a freed region's address by
    /// arithmetic that escaped the object).
    Invalid,
}

/// A pointer's offset from the base of its provenance region, in bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymOffset {
    /// A concrete signed byte offset.
    Exact(i128),
    /// A symbolic offset named by a solver variable.
    Symbolic(String),
    /// Unconstrained (any offset).
    Top,
}

impl SymOffset {
    /// The concrete offset, if known.
    pub fn as_exact(&self) -> Option<i128> {
        match self {
            SymOffset::Exact(n) => Some(*n),
            _ => None,
        }
    }
}

/// A symbolic pointer value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pointer {
    /// The allocation this pointer derives its authority from.
    pub provenance: Provenance,
    /// The byte offset from that allocation's base.
    pub offset: SymOffset,
    /// The statically-known alignment guarantee of this address, in bytes.
    pub align: u64,
}

impl Pointer {
    /// A pointer to the base of `region` with the given alignment.
    pub fn to_region(region: RegionId, align: u64) -> Pointer {
        Pointer {
            provenance: Provenance::Region(region),
            offset: SymOffset::Exact(0),
            align,
        }
    }

    /// The null pointer.
    pub fn null() -> Pointer {
        Pointer {
            provenance: Provenance::Null,
            offset: SymOffset::Exact(0),
            align: 1,
        }
    }

    /// Offset this pointer by `delta` bytes, keeping provenance. Alignment is
    /// reduced to the alignment implied by the offset when it is concrete.
    pub fn offset_bytes(&self, delta: i128) -> Pointer {
        let offset = match &self.offset {
            SymOffset::Exact(n) => SymOffset::Exact(n + delta),
            SymOffset::Symbolic(_) | SymOffset::Top => SymOffset::Top,
        };
        let align = align_after_offset(self.align, delta);
        Pointer {
            provenance: self.provenance.clone(),
            offset,
            align,
        }
    }
}

/// The largest alignment still guaranteed after adding `delta` to an address
/// known to be `base_align`-aligned: `gcd(base_align, |delta|)` (with `delta==0`
/// preserving `base_align`).
fn align_after_offset(base_align: u64, delta: i128) -> u64 {
    if delta == 0 {
        return base_align;
    }
    let d = delta.unsigned_abs() as u64;
    gcd(base_align, d).max(1)
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl fmt::Display for Pointer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.provenance {
            Provenance::Null => write!(f, "null"),
            Provenance::Region(r) => write!(f, "{r}+{:?}", self.offset),
            Provenance::Unknown => write!(f, "?+{:?}", self.offset),
            Provenance::Invalid => write!(f, "invalid"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_preserves_provenance_and_reduces_align() {
        let p = Pointer::to_region(RegionId(0), 8);
        let q = p.offset_bytes(4);
        assert_eq!(q.provenance, Provenance::Region(RegionId(0)));
        assert_eq!(q.offset, SymOffset::Exact(4));
        // 8-aligned base + 4 => gcd(8,4) = 4.
        assert_eq!(q.align, 4);
        // +2 from there in absolute terms: base+6 => gcd(8,6)=2.
        assert_eq!(p.offset_bytes(6).align, 2);
    }

    #[test]
    fn symbolic_offset_loses_alignment_knowledge() {
        let p = Pointer {
            provenance: Provenance::Region(RegionId(1)),
            offset: SymOffset::Symbolic("i".into()),
            align: 8,
        };
        let q = p.offset_bytes(8);
        assert_eq!(q.offset, SymOffset::Top);
    }
}
