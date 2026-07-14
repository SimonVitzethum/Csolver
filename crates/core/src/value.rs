//! Concrete machine values.
//!
//! [`BitVector`] is a fixed-width, two's-complement integer value used for
//! constants and for the assignments inside a [`crate::CounterExample`]. It is
//! intentionally concrete (not symbolic): symbolic values live in the
//! `csolver-solver` crate. Widths up to 128 bits are stored
//! inline; this covers every scalar that occurs in MIR/LLVM/x86-64/AArch64.

use std::fmt;

/// A fixed-width bit-vector value (`0 < width <= 128`).
///
/// The stored value is always reduced modulo `2^width`, so two `BitVector`s
/// with the same width and equal value are bit-for-bit identical.
///
/// The 128-bit payload is held as two little-endian `u64` words (`lo`, `hi`)
/// rather than a single `u128`. Semantically identical — [`BitVector::new`] and
/// [`BitVector::unsigned`] convert exactly — but it drops the type's alignment
/// from 16 to 8 bytes, which (via `Const` → `Operand`) shrinks the pervasive
/// [`crate::…`] `Inst` node and every `Vec` of them, improving cache locality on
/// the IR-iterating passes. No new allocation and only a shift/or per conversion,
/// so it neither weakens soundness (values are exact) nor scaling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitVector {
    width: u32,
    /// Little-endian payload: `words[0]` is bits 0..64, `words[1]` is bits 64..128.
    words: [u64; 2],
}

impl BitVector {
    /// Create a bit-vector of `width` bits holding `value` (reduced mod 2^width).
    ///
    /// # Panics
    /// Panics if `width == 0` or `width > 128`.
    pub fn new(width: u32, value: u128) -> Self {
        assert!(width > 0 && width <= 128, "bit-vector width out of range");
        BitVector {
            width,
            words: Self::split(value & Self::mask(width)),
        }
    }

    /// Split a `u128` into its little-endian `[lo, hi]` words.
    #[inline]
    fn split(v: u128) -> [u64; 2] {
        [v as u64, (v >> 64) as u64]
    }

    /// Reassemble the `u128` payload from its two words.
    #[inline]
    fn value(&self) -> u128 {
        (self.words[0] as u128) | ((self.words[1] as u128) << 64)
    }

    /// The all-zero bit-vector of the given width.
    pub fn zero(width: u32) -> Self {
        BitVector::new(width, 0)
    }

    /// The bit-mask `2^width - 1` for a given width.
    fn mask(width: u32) -> u128 {
        if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        }
    }

    /// The bit width.
    pub fn width(&self) -> u32 {
        self.width
    }

    /// The raw unsigned value (`0 <= v < 2^width`).
    pub fn unsigned(&self) -> u128 {
        self.value()
    }

    /// The value interpreted as a two's-complement signed integer.
    ///
    /// Implemented by sign-extending: shift the value up so its sign bit lands
    /// at bit 127, then arithmetic-shift back down. This is correct for every
    /// width in `1..=128` (including the awkward 127/128 cases where `2^width`
    /// is not representable in `i128`).
    pub fn signed(&self) -> i128 {
        let shift = 128 - self.width;
        ((self.value() << shift) as i128) >> shift
    }

    /// Whether every bit is zero.
    pub fn is_zero(&self) -> bool {
        self.words == [0, 0]
    }

    /// Wrapping addition at this width. Operands must share the width.
    ///
    /// # Panics
    /// Panics if the widths differ.
    pub fn wrapping_add(self, other: BitVector) -> BitVector {
        assert_eq!(self.width, other.width, "bit-vector width mismatch");
        BitVector::new(self.width, self.value().wrapping_add(other.value()))
    }

    /// Wrapping subtraction at this width.
    ///
    /// # Panics
    /// Panics if the widths differ.
    pub fn wrapping_sub(self, other: BitVector) -> BitVector {
        assert_eq!(self.width, other.width, "bit-vector width mismatch");
        BitVector::new(self.width, self.value().wrapping_sub(other.value()))
    }
}

impl fmt::Display for BitVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}u{}", self.value(), self.width)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduces_modulo_width() {
        assert_eq!(BitVector::new(8, 256).unsigned(), 0);
        assert_eq!(BitVector::new(8, 257).unsigned(), 1);
        assert_eq!(BitVector::new(8, 255).unsigned(), 255);
    }

    #[test]
    fn signed_interpretation() {
        assert_eq!(BitVector::new(8, 255).signed(), -1);
        assert_eq!(BitVector::new(8, 128).signed(), -128);
        assert_eq!(BitVector::new(8, 127).signed(), 127);
        assert_eq!(BitVector::new(8, 0).signed(), 0);
        assert_eq!(BitVector::new(32, u32::MAX as u128).signed(), -1);
        assert_eq!(BitVector::new(64, u64::MAX as u128).signed(), -1);
    }

    #[test]
    fn wrapping_arithmetic() {
        let a = BitVector::new(8, 200);
        let b = BitVector::new(8, 100);
        assert_eq!(a.wrapping_add(b).unsigned(), 44); // 300 mod 256
        assert_eq!(b.wrapping_sub(a).unsigned(), 156); // -100 mod 256
    }

    #[test]
    fn full_width_128_is_safe() {
        let m = BitVector::new(128, u128::MAX);
        assert_eq!(m.unsigned(), u128::MAX);
        assert_eq!(m.signed(), -1);
        assert!(!m.is_zero());
    }

    #[test]
    fn two_word_payload_roundtrips_exactly() {
        // The [lo, hi] split/reassemble is an exact identity across the full 128-bit
        // range and both word boundaries — the soundness invariant of the layout change.
        for v in [
            0u128,
            1,
            u64::MAX as u128,                    // all-low-word
            1u128 << 64,                          // only the high word
            (u64::MAX as u128) << 64,             // all-high-word
            u128::MAX,                            // both words full
            0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
        ] {
            assert_eq!(BitVector::new(128, v).unsigned(), v, "roundtrip {v:#x}");
        }
        // Reduction still applies per width, independent of the split.
        assert_eq!(BitVector::new(96, u128::MAX).unsigned(), (1u128 << 96) - 1);
        assert_eq!(BitVector::new(65, u128::MAX).unsigned(), (1u128 << 65) - 1);
    }

    #[test]
    #[should_panic]
    fn width_zero_panics() {
        let _ = BitVector::new(0, 0);
    }
}
