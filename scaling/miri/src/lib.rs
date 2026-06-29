//! Soundness at scale — drive real scaling-corpus crates under Miri.
//!
//! The [scaling sweep](../../README.md) measured *coverage*: what fraction of
//! real crate functions CSolver can analyse (≈91% PASS). It did **not** check
//! those PASS verdicts against an independent oracle — the [differential
//! corpus](../../../differential) does that, but only on ~30 hand-written
//! functions. So the real-crate PASS verdicts were trusted, not tested. A subtle
//! lowering bug that models a memory construct *wrong* (rather than not at all)
//! would surface as a `PASS` with nothing to catch it — exactly how the
//! cleanup-block bug slipped in until a curated UB function happened to exercise
//! the same path.
//!
//! This harness closes that gap: it fuzzes each real crate's public API and runs
//! it under Miri (see `tests/fuzz.rs`). Miri executes the very functions CSolver
//! verified, on real inputs. **Any Miri `Undefined Behavior` in a `PASS`
//! function is a false `PASS`** — cross-reference the crate's verdicts from
//! `../run.sh`. Miri clean over a broad fuzz means the executed PASS functions
//! are validated on those paths: the coverage number becomes a *trustworthy* one.
//!
//! The unsafe-heavy data structures (`arrayvec`, `tinyvec`) are the most valuable
//! targets — their internal `unsafe` is what a lowering bug would mis-model, and
//! what a latent crate bug would trip. `adler2` exercises the index-into-field
//! lowering (its checksum updates a `[u32; 4]` struct field) added last.

/// SplitMix64 — a tiny, dependency-free, deterministic PRNG, identical to the one
/// the differential drivers use: pure arithmetic, so it runs under Miri with
/// isolation on and reproduces from its seed.
pub struct Fuzz(u64);

impl Fuzz {
    pub fn new(seed: u64) -> Self {
        Fuzz(seed)
    }

    pub fn bits(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `[0, n)` (`0` when `n == 0`).
    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.bits() % n as u64) as usize
        }
    }

    pub fn byte(&mut self) -> u8 {
        self.bits() as u8
    }

    pub fn u16(&mut self) -> u16 {
        self.bits() as u16
    }

    pub fn u32(&mut self) -> u32 {
        self.bits() as u32
    }

    pub fn u64(&mut self) -> u64 {
        self.bits()
    }
}

/// Fuzz iterations per driver; the harness lowers it for the slow Miri pass via
/// `FUZZ_CASES`.
pub fn cases() -> usize {
    std::env::var("FUZZ_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(200)
}
