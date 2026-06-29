//! Miri drivers: one `drive_<fn>` test per corpus function, run in isolation by
//! the harness (`cargo +nightly miri test -- --exact drive_<fn>`).
//!
//! Each driver **fuzzes** its target instead of hard-wiring one input: it draws
//! many inputs from a tiny deterministic PRNG (`Fuzz`, below) and calls the
//! function under `black_box` (so the access is not optimised away). Fuzzing —
//! rather than my hand-picking the trigger — is what makes Miri reach the UB
//! paths and breaks the circularity of me choosing both the bug *and* the input
//! that exposes it.
//!
//! Why a hand-rolled PRNG instead of `proptest`/`quickcheck`: the project builds
//! **offline** (no crates.io fetch), and a pure-arithmetic generator needs **no**
//! syscall, so it runs under Miri with isolation left on (no `getrandom`/time, no
//! `-Zmiri-disable-isolation`) and is fully reproducible from its fixed seed.
//!
//! The unsafe drivers draw inputs from a domain that reliably includes the
//! UB-triggering values (e.g. `i` ranging past `len`); the safe drivers draw
//! broadly so Miri stays clean across the whole range, not just one point.

use differential::*;
use std::hint::black_box;

/// SplitMix64 — a tiny, dependency-free, deterministic PRNG. Pure wrapping
/// arithmetic, so Miri executes it as ordinary code and every run reproduces.
struct Fuzz(u64);

impl Fuzz {
    fn new(seed: u64) -> Self {
        Fuzz(seed)
    }

    fn bits(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `[0, n)` (`0` when `n == 0`).
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.bits() % n as u64) as usize
        }
    }

    fn boolean(&mut self) -> bool {
        self.bits() & 1 == 1
    }

    fn int(&mut self) -> i32 {
        self.bits() as i32
    }

    /// A random `Vec<i32>` of length `< max_len`.
    fn vec(&mut self, max_len: usize) -> Vec<i32> {
        let len = self.below(max_len);
        (0..len).map(|_| self.int()).collect()
    }
}

/// Fuzz iterations per driver. The harness lowers this for the slow Miri pass via
/// `FUZZ_CASES`; a native `cargo test` uses the (still cheap) default. Reading an
/// env var needs no syscall under Miri, so isolation can stay on.
fn cases() -> usize {
    std::env::var("FUZZ_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(200)
}

// ===== safe drivers: Miri must stay clean across the whole fuzzed range =======

#[test]
fn drive_checked_get() {
    let mut f = Fuzz::new(0x5afe_0001);
    for _ in 0..cases() {
        let v = f.vec(12);
        let i = f.below(2 * v.len() + 8);
        black_box(checked_get(black_box(&v), black_box(i)));
    }
}

#[test]
fn drive_array_first() {
    let mut f = Fuzz::new(0x5afe_0002);
    for _ in 0..cases() {
        let a = [f.int(), f.int(), f.int(), f.int(), f.int(), f.int(), f.int(), f.int()];
        black_box(array_first(black_box(&a)));
    }
}

#[test]
fn drive_sum() {
    let mut f = Fuzz::new(0x5afe_0003);
    for _ in 0..cases() {
        let v = f.vec(16);
        black_box(sum(black_box(&v)));
    }
}

#[test]
fn drive_last() {
    let mut f = Fuzz::new(0x5afe_0004);
    for _ in 0..cases() {
        let v = f.vec(16);
        black_box(last(black_box(&v)));
    }
}

#[test]
fn drive_fill() {
    let mut f = Fuzz::new(0x5afe_0005);
    for _ in 0..cases() {
        let mut v = vec![0u8; f.below(16)];
        fill(black_box(&mut v), black_box(f.int() as u8));
        black_box(&v);
    }
}

#[test]
fn drive_two_slice() {
    let mut f = Fuzz::new(0x5afe_0006);
    for _ in 0..cases() {
        let a = f.vec(12);
        let b = f.vec(12);
        let i = f.below(2 * a.len().max(b.len()) + 8);
        black_box(two_slice(black_box(&a), black_box(&b), black_box(i)));
    }
}

#[test]
fn drive_clamp_get() {
    let mut f = Fuzz::new(0x5afe_0007);
    for _ in 0..cases() {
        let v = f.vec(12);
        let i = f.below(1000);
        black_box(clamp_get(black_box(&v), black_box(i)));
    }
}

#[test]
fn drive_guarded_pair() {
    let mut f = Fuzz::new(0x5afe_0008);
    for _ in 0..cases() {
        let v = f.vec(16);
        black_box(guarded_pair(black_box(&v)));
    }
}

#[test]
fn drive_nested_get() {
    let mut f = Fuzz::new(0x5afe_0009);
    for _ in 0..cases() {
        let rows = f.below(6);
        let m: Vec<[i32; 4]> = (0..rows)
            .map(|_| [f.int(), f.int(), f.int(), f.int()])
            .collect();
        let i = f.below(rows + 4);
        let j = f.below(8);
        black_box(nested_get(black_box(&m), black_box(i), black_box(j)));
    }
}

#[test]
fn drive_copy_within_guard() {
    let mut f = Fuzz::new(0x5afe_000a);
    for _ in 0..cases() {
        let mut dst = f.vec(12);
        let src = f.vec(12);
        copy_within_guard(black_box(&mut dst), black_box(&src));
        black_box(&dst);
    }
}

#[test]
fn drive_min_index_get() {
    let mut f = Fuzz::new(0x5afe_000b);
    for _ in 0..cases() {
        let v = f.vec(12);
        let i = f.below(1000);
        black_box(min_index_get(black_box(&v), black_box(i)));
    }
}

#[test]
fn drive_window_sum() {
    let mut f = Fuzz::new(0x5afe_000c);
    for _ in 0..cases() {
        let v = f.vec(16);
        black_box(window_sum(black_box(&v)));
    }
}

#[test]
fn drive_match_opt() {
    let mut f = Fuzz::new(0x5afe_0011);
    for _ in 0..cases() {
        let o = if f.boolean() { Some(f.int()) } else { None };
        black_box(match_opt(black_box(&o)));
    }
}

#[test]
fn drive_tagged_first() {
    let mut f = Fuzz::new(0x5afe_0012);
    for _ in 0..cases() {
        let t = if f.boolean() {
            Tagged::One(f.int())
        } else {
            Tagged::Two(f.int(), f.int())
        };
        black_box(tagged_first(black_box(&t)));
    }
}

#[test]
fn drive_read_field() {
    let mut f = Fuzz::new(0x5afe_000f);
    for _ in 0..cases() {
        let p = Pair { a: f.int(), b: f.int() };
        black_box(read_field(black_box(&p)));
    }
}

#[test]
fn drive_write_field() {
    let mut f = Fuzz::new(0x5afe_0010);
    for _ in 0..cases() {
        let mut p = Pair { a: f.int(), b: f.int() };
        write_field(black_box(&mut p), black_box(f.int()));
        black_box(&p);
    }
}

#[test]
fn drive_head_via_helper() {
    let mut f = Fuzz::new(0x5afe_000d);
    for _ in 0..cases() {
        let v = f.vec(16);
        black_box(head_via_helper(black_box(&v)));
    }
}

#[test]
fn drive_helper_bound() {
    let mut f = Fuzz::new(0x5afe_000e);
    for _ in 0..cases() {
        let v = f.vec(12);
        let i = f.below(2 * v.len() + 8);
        black_box(helper_bound(black_box(&v), black_box(i)));
    }
}

// ===== unsafe drivers: Miri must report UB on a fuzzed input ==================

#[test]
fn drive_unchecked_oob() {
    let mut f = Fuzz::new(0x0bad_0001);
    for _ in 0..cases() {
        let v = f.vec(12);
        let i = f.below(2 * v.len() + 8); // reliably samples i >= len
        black_box(unchecked_oob(black_box(&v), black_box(i)));
    }
}

#[test]
fn drive_past_end() {
    let mut f = Fuzz::new(0x0bad_0002);
    for _ in 0..cases() {
        let v = f.vec(12);
        black_box(past_end(black_box(&v))); // UB for any v
    }
}

#[test]
fn drive_unchecked_write() {
    let mut f = Fuzz::new(0x0bad_0003);
    for _ in 0..cases() {
        let mut v = f.vec(12);
        let i = f.below(2 * v.len() + 8);
        unchecked_write(black_box(&mut v), black_box(i));
        black_box(&v);
    }
}

#[test]
fn drive_raw_add() {
    let mut f = Fuzz::new(0x0bad_0004);
    for _ in 0..cases() {
        let v = f.vec(12);
        let i = f.below(2 * v.len() + 8);
        black_box(raw_add(black_box(&v), black_box(i)));
    }
}

#[test]
fn drive_off_by_one_loop() {
    let mut f = Fuzz::new(0x0bad_0005);
    for _ in 0..cases() {
        let v = f.vec(12);
        black_box(off_by_one_loop(black_box(&v))); // reads s[len] — UB
    }
}

#[test]
fn drive_raw_sub() {
    let mut f = Fuzz::new(0x0bad_0006);
    for _ in 0..cases() {
        let v = f.vec(12);
        black_box(raw_sub(black_box(&v))); // before the start — UB
    }
}

#[test]
fn drive_oob_via_helper() {
    let mut f = Fuzz::new(0x0bad_0007);
    for _ in 0..cases() {
        let v = f.vec(12);
        black_box(oob_via_helper(black_box(&v))); // helper index len+1 — UB
    }
}

#[test]
fn drive_cond_use_after_free() {
    let mut f = Fuzz::new(0x0bad_0008);
    for _ in 0..cases() {
        black_box(cond_use_after_free(black_box(f.boolean()))); // UB when true
    }
}

#[test]
fn drive_null_deref() {
    let mut f = Fuzz::new(0x0bad_0009);
    for _ in 0..cases() {
        black_box(null_deref(black_box(f.boolean()))); // UB when true
    }
}

#[test]
fn drive_slice_oob_from_raw() {
    let mut f = Fuzz::new(0x0bad_000a);
    for _ in 0..cases() {
        let v = f.vec(12);
        black_box(slice_oob_from_raw(black_box(&v))); // reads past the alloc — UB
    }
}

#[test]
fn drive_nested_oob() {
    let mut f = Fuzz::new(0x0bad_000b);
    for _ in 0..cases() {
        let rows = f.below(6);
        let m: Vec<[i32; 4]> = (0..rows)
            .map(|_| [f.int(), f.int(), f.int(), f.int()])
            .collect();
        let i = f.below(rows + 4);
        let j = f.below(8); // reliably samples i >= rows or j >= 4
        black_box(nested_oob(black_box(&m), black_box(i), black_box(j)));
    }
}
