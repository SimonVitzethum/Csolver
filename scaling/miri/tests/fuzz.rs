//! Fuzz drivers that run real scaling-corpus crates under Miri. Each draws inputs
//! from the deterministic PRNG and exercises the crate's public API broadly,
//! reaching the internal `unsafe` that CSolver verified. Run by `run.sh` under
//! `cargo +nightly miri test`; any Miri "Undefined Behavior" is a finding.
//!
//! The drivers prefer non-panicking operations (a panic is safe, just ends the
//! case early and exercises less), so guards keep indices/lengths in range.

use scaling_miri::{cases, Fuzz};
use std::hint::black_box;

/// `adler2`: the Adler-32 checksum. Exercises the index-into-struct-field lowering
/// (its state is a `[u32; 4]` field updated as `((*_1).0)[i]`) added last.
#[test]
fn fuzz_adler2() {
    let mut f = Fuzz::new(0x0ad1_e200);
    for _ in 0..cases() {
        let len = f.below(160);
        let data: Vec<u8> = (0..len).map(|_| f.byte()).collect();
        black_box(adler2::adler32_slice(&data));
        // The incremental API, fed in random-sized chunks.
        let mut a = adler2::Adler32::new();
        let mut i = 0;
        while i < data.len() {
            let end = (i + 1 + f.below(13)).min(data.len());
            a.write_slice(&data[i..end]);
            i = end;
        }
        black_box(a.checksum());
    }
}

/// `oorandom`: the PRNGs (arithmetic-heavy, few memory ops, but a clean baseline).
#[test]
fn fuzz_oorandom() {
    let mut f = Fuzz::new(0x0070_4a4d);
    for _ in 0..cases() {
        let mut r = oorandom::Rand32::new(f.u64());
        for _ in 0..16 {
            black_box(r.rand_u32());
        }
        let a = f.u32();
        let b = a.wrapping_add(1 + f.below(4096) as u32);
        black_box(r.rand_range(a..b));
        black_box(r.rand_float());
        let mut r64 = oorandom::Rand64::new(f.u64() as u128);
        for _ in 0..16 {
            black_box(r64.rand_u64());
        }
    }
}

/// `arrayvec`: a fixed-capacity vector — internal `unsafe` (raw writes, shifting
/// for insert/remove). The highest-value soundness target.
#[test]
fn fuzz_arrayvec() {
    let mut f = Fuzz::new(0x0a77_acec);
    for _ in 0..cases() {
        let mut v: arrayvec::ArrayVec<u8, 16> = arrayvec::ArrayVec::new();
        for _ in 0..60 {
            match f.below(8) {
                0 => {
                    let _ = v.try_push(f.byte());
                }
                1 => {
                    v.pop();
                }
                2 => {
                    if !v.is_empty() {
                        let i = f.below(v.len());
                        black_box(v.remove(i));
                    }
                }
                3 => {
                    if !v.is_full() {
                        let i = f.below(v.len() + 1);
                        v.insert(i, f.byte());
                    }
                }
                4 => {
                    let n = f.below(v.len() + 1);
                    v.truncate(n);
                }
                5 => {
                    if !v.is_empty() {
                        let i = f.below(v.len());
                        black_box(v.swap_remove(i));
                    }
                }
                6 => {
                    if !v.is_empty() {
                        let i = f.below(v.len());
                        black_box(v[i]);
                    }
                }
                _ => {
                    black_box(v.as_slice().len());
                }
            }
        }
    }
}

/// `tinyvec::ArrayVec`: the same shape, a different implementation.
#[test]
fn fuzz_tinyvec() {
    let mut f = Fuzz::new(0x7149_acec);
    for _ in 0..cases() {
        let mut v: tinyvec::ArrayVec<[u8; 16]> = tinyvec::ArrayVec::default();
        for _ in 0..60 {
            match f.below(7) {
                0 => {
                    let _ = v.try_push(f.byte());
                }
                1 => {
                    v.pop();
                }
                2 => {
                    if !v.is_empty() {
                        let i = f.below(v.len());
                        black_box(v.remove(i));
                    }
                }
                3 => {
                    if v.len() < 16 {
                        let i = f.below(v.len() + 1);
                        v.insert(i, f.byte());
                    }
                }
                4 => {
                    let n = f.below(v.len() + 1);
                    v.truncate(n);
                }
                5 => {
                    if !v.is_empty() {
                        let i = f.below(v.len());
                        black_box(v.swap_remove(i));
                    }
                }
                _ => {
                    if !v.is_empty() {
                        let i = f.below(v.len());
                        black_box(v[i]);
                    }
                }
            }
        }
    }
}

/// `itoa`: integer-to-string into a fixed buffer (raw byte writes internally).
/// A fresh buffer per call (`format` borrows the buffer for the returned `&str`).
#[test]
fn fuzz_itoa() {
    let mut f = Fuzz::new(0x1704_acec);
    for _ in 0..cases() {
        let mut b = itoa::Buffer::new();
        black_box(b.format(f.u64()).len());
        let mut b = itoa::Buffer::new();
        black_box(b.format(f.u32() as i32).len());
        let mut b = itoa::Buffer::new();
        black_box(b.format(f.u64() as i64).len());
        let mut b = itoa::Buffer::new();
        black_box(b.format(f.byte()).len());
    }
}
