//! A fast, deterministic, non-cryptographic hasher for the analysis's hot maps.
//!
//! The standard-library `HashMap` defaults to SipHash via a *per-process randomly
//! seeded* `RandomState` — DoS-resistant but slow, and (were any result to depend on
//! iteration order) a source of run-to-run nondeterminism. The analysis interns
//! expressions, looks up SSA environments per instruction, and caches proofs in maps
//! keyed by small integers (`ExprId`/`RegId`/`usize`); SipHash dominates those hot
//! loops for no benefit, since the inputs are never adversarial and the code is already
//! iteration-order-independent (its verdicts are deterministic despite the random seed).
//!
//! [`FxHasher`] is the well-known "Firefox" hash (a rotate-xor-multiply mix, as used by
//! rustc's own `FxHashMap`): a handful of arithmetic ops per word, all safe code. Using
//! it changes no verdict — only speed — and makes runs deterministic as a bonus.
//!
//! Use the [`FxHashMap`] / [`FxHashSet`] aliases in place of the std types on hot paths.

use std::hash::{BuildHasherDefault, Hasher};

/// The odd multiplicative constant of the Fx mix (rustc's `fxhash` seed).
const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;
const ROTATE: u32 = 5;

/// A fast non-cryptographic hasher (rotate-xor-multiply). Deterministic and
/// seedless — identical inputs hash identically across runs.
#[derive(Default)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(ROTATE) ^ word).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, mut bytes: &[u8]) {
        while bytes.len() >= 8 {
            let mut b = [0u8; 8];
            b.copy_from_slice(&bytes[..8]);
            self.add(u64::from_le_bytes(b));
            bytes = &bytes[8..];
        }
        if bytes.len() >= 4 {
            let mut b = [0u8; 4];
            b.copy_from_slice(&bytes[..4]);
            self.add(u32::from_le_bytes(b) as u64);
            bytes = &bytes[4..];
        }
        for &byte in bytes {
            self.add(byte as u64);
        }
    }

    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }

    #[inline]
    fn finish(&self) -> u64 {
        // A final avalanche so low-entropy keys (small consecutive ids) spread across
        // the bucket space rather than clustering.
        const FINAL: u64 = 0x9E37_79B9_7F4A_7C15;
        self.hash.wrapping_mul(FINAL)
    }
}

/// A `BuildHasher` producing [`FxHasher`]s (seedless, so `Default`-constructible).
pub type FxBuildHasher = BuildHasherDefault<FxHasher>;

/// A `HashMap` using the fast [`FxHasher`]. Drop-in for `std::collections::HashMap`
/// on hot paths — construct with `FxHashMap::default()` (there is no `new`).
pub type FxHashMap<K, V> = std::collections::HashMap<K, V, FxBuildHasher>;

/// A `HashSet` using the fast [`FxHasher`]. Drop-in for `std::collections::HashSet`
/// on hot paths — construct with `FxHashSet::default()`.
pub type FxHashSet<T> = std::collections::HashSet<T, FxBuildHasher>;

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::BuildHasher;

    #[test]
    fn deterministic_and_distinct() {
        let bh = FxBuildHasher::default();
        // Determinism: the same key hashes identically (no random seed).
        assert_eq!(bh.hash_one(42u64), bh.hash_one(42u64));
        assert_eq!(bh.hash_one("abc"), bh.hash_one("abc"));
        // Distinctness on small consecutive ids (the common key shape): the final
        // avalanche keeps them from colliding into one bucket bit-pattern.
        let hs: std::collections::HashSet<u64> = (0u32..1000).map(|i| bh.hash_one(i)).collect();
        assert!(hs.len() > 990, "small ids spread across the hash space: {}", hs.len());
    }

    #[test]
    fn map_roundtrips() {
        let mut m: FxHashMap<u32, &str> = FxHashMap::default();
        m.insert(1, "a");
        m.insert(1 << 20, "b");
        assert_eq!(m.get(&1), Some(&"a"));
        assert_eq!(m.get(&(1 << 20)), Some(&"b"));
        assert_eq!(m.len(), 2);

        let mut s: FxHashSet<usize> = FxHashSet::default();
        assert!(s.insert(7));
        assert!(!s.insert(7));
    }
}
