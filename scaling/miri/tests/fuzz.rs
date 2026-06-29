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

/// `memchr`: SIMD byte search — fuzz needle(s) + haystack over its unsafe paths.
#[test]
fn fuzz_memchr() {
    let mut f = Fuzz::new(0x0e3c_4111);
    for _ in 0..cases() {
        let len = f.below(200);
        let hay: Vec<u8> = (0..len).map(|_| f.byte()).collect();
        let (a, b, c) = (f.byte(), f.byte(), f.byte());
        black_box(memchr::memchr(a, &hay));
        black_box(memchr::memrchr(a, &hay));
        black_box(memchr::memchr2(a, b, &hay));
        black_box(memchr::memchr3(a, b, c, &hay));
        let nlen = f.below(5);
        let needle: Vec<u8> = (0..nlen).map(|_| f.byte()).collect();
        black_box(memchr::memmem::find(&hay, &needle));
    }
}

/// `bytes`: ref-counted byte buffers — the `Vtable` of fn pointers the fn-pointer
/// type parse fix just enabled. Fuzz BytesMut/Bytes ops over its internal unsafe.
#[test]
fn fuzz_bytes() {
    use bytes::{Buf, BufMut, Bytes, BytesMut};
    let mut f = Fuzz::new(0xb17e_5111);
    for _ in 0..cases() {
        let mut b = BytesMut::new();
        for _ in 0..40 {
            match f.below(6) {
                0 => b.put_u8(f.byte()),
                1 => {
                    let n = f.below(8);
                    let s: Vec<u8> = (0..n).map(|_| f.byte()).collect();
                    b.put_slice(&s);
                }
                2 => {
                    let n = f.below(b.remaining() + 1);
                    b.advance(n);
                }
                3 => {
                    let n = f.below(b.len() + 1);
                    let _ = b.split_to(n);
                }
                4 => {
                    let n = f.below(b.len() + 1);
                    let _ = b.split_off(n);
                }
                _ => {
                    black_box(b.len());
                }
            }
        }
        let frozen: Bytes = b.freeze();
        if !frozen.is_empty() {
            let i = f.below(frozen.len());
            black_box(frozen.slice(i..));
        }
        black_box(Bytes::copy_from_slice(&[f.byte(), f.byte(), f.byte()]));
    }
}

/// A tiny dependency-free hasher (FNV-style) so `hashbrown::HashMap::with_hasher`
/// works without a default-hasher feature, and runs reproduce.
#[derive(Clone, Default)]
struct FxBuild;
impl std::hash::BuildHasher for FxBuild {
    type Hasher = Fx;
    fn build_hasher(&self) -> Fx {
        Fx(0xcbf2_9ce4_8422_2325)
    }
}
struct Fx(u64);
impl std::hash::Hasher for Fx {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0 ^ b as u64).wrapping_mul(0x0100_0000_01b3);
        }
    }
}

/// `hashbrown::HashMap` — complex unsafe generics over raw allocation, the densest
/// UB target. The driver fuzzes long **operation sequences**, not single calls: a
/// single insert on a fresh map never resizes, so the interesting paths (grow +
/// rehash, tombstones from removes, probe sequences, `entry`, `retain`, the table
/// scan) are only reached by driving a map through ~120 mixed ops until it resizes
/// several times.
#[test]
fn fuzz_hashbrown() {
    let mut f = Fuzz::new(0xba50_4111);
    for _ in 0..cases() {
        let mut m: hashbrown::HashMap<u16, u32, FxBuild> = hashbrown::HashMap::with_hasher(FxBuild);
        for _ in 0..120 {
            match f.below(8) {
                // Insert-heavy so the table grows and rehashes repeatedly.
                0 | 1 => {
                    m.insert(f.u16(), f.u32());
                }
                // Removes leave tombstones the probe sequence must skip.
                2 => {
                    let k = f.u16();
                    m.remove(&k);
                }
                3 => {
                    let k = f.u16();
                    black_box(m.get(&k));
                }
                4 => {
                    *m.entry(f.u16()).or_insert(0) += 1;
                }
                5 => m.retain(|k, _| (k & 3) != 0),
                6 => {
                    black_box(m.contains_key(&f.u16()));
                }
                _ => {
                    if f.below(30) == 0 {
                        m.clear();
                    }
                }
            }
        }
        // A full table scan over whatever survived (live slots + skipped tombstones).
        let mut s = 0u64;
        for (k, v) in &m {
            s = s.wrapping_add(*k as u64 ^ *v as u64);
        }
        black_box((m.len(), s));
    }
}

/// `nom` — parser combinators (the called-closure lowering this round enabled). Run
/// a small combinator chain over fuzzed bytes; nom slices with bounds checks, so a
/// clean run validates the new closure/generic lowering paths stay memory-safe.
#[test]
fn fuzz_nom() {
    use nom::branch::alt;
    use nom::bytes::complete::{tag, take_while};
    use nom::character::complete::{char, digit1};
    use nom::multi::separated_list0;
    use nom::sequence::separated_pair;
    use nom::IResult;
    type E<'a> = nom::error::Error<&'a [u8]>;
    let mut f = Fuzz::new(0x0_0e3c_acec);
    for _ in 0..cases() {
        let len = f.below(80);
        let data: Vec<u8> = (0..len).map(|_| f.byte()).collect();
        let _: IResult<&[u8], _, E> = separated_list0(char(','), digit1)(&data);
        let _: IResult<&[u8], _, E> = take_while(|c: u8| c.is_ascii_alphanumeric())(&data);
        let _: IResult<&[u8], _, E> = nom::number::complete::be_u32(&data);
        let _: IResult<&[u8], _, E> =
            alt((tag(b"GET".as_slice()), tag(b"PUT".as_slice())))(&data);
        let _: IResult<&[u8], _, E> = separated_pair(digit1, char(':'), digit1)(&data);
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
