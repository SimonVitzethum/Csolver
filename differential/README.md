# Differential validation: CSolver vs Miri

CSolver's whole claim is **soundness-first — never a false `PASS`**. This harness
*measures* that claim instead of asserting it, using [Miri](https://github.com/rust-lang/miri)
as an independent dynamic oracle for the same property bundle CSolver proves
(out-of-bounds, use-after-free, double-free, uninitialised reads, provenance).

## The asymmetry

CSolver is **static** (a verdict over *all* inputs); Miri is **dynamic** (it
observes UB only on the *executed* path). So the comparison is one-sided:

| Miri on the driven input | CSolver verdict | meaning |
|---|---|---|
| **UB** | `PASS` | **soundness violation** — a false `PASS`, the cardinal sin (must be zero) |
| **UB** | `UNKNOWN`/`FAIL` | sound — the danger was caught or honestly left unknown |
| clean | `PASS` | precise |
| clean | `UNKNOWN` | precision miss — sound, but a capability gap to close |

Only Miri's *Undefined Behavior* is the soundness oracle. A normal Rust **panic**
(e.g. a bounds-check abort) is *safe* behaviour — CSolver proves memory safety,
not panic-freedom — so the harness treats a panic as "no UB".

Because Miri is path-dependent, the drivers in `tests/drive.rs` must *reach* the
bug. Rather than hand-pick the triggering input (which would make me choose both
the bug *and* the input that exposes it — a blind spot that can hide a false
`PASS`), each driver **fuzzes**: it draws many inputs from a tiny deterministic
PRNG and runs the function under each. The unsafe drivers draw from a domain that
reliably includes the UB-triggering values (e.g. an index ranging past `len`); the
safe drivers draw broadly, so Miri must stay clean across the whole range, not
just at one point.

The PRNG (`Fuzz`, ~15 lines of SplitMix64 in `tests/drive.rs`) is hand-rolled
rather than `proptest`/`quickcheck` for two reasons: the project builds **offline**
(no crates.io fetch), and being pure arithmetic it needs **no** syscall, so it runs
under Miri with isolation left on (no `getrandom`/time, no
`-Zmiri-disable-isolation`) and reproduces exactly from its fixed per-driver seed.

## Running

```
./run.sh                 # default: FUZZ_CASES=32 inputs per driver
FUZZ_CASES=128 ./run.sh  # deeper sweep (slower)
```

It builds the `solver` CLI, emits the corpus MIR (`rustc --emit=mir`), runs
`solver verify`, then drives each function under `cargo +nightly miri test` and
prints a per-function table plus a summary. `FUZZ_CASES` bounds how many inputs
each driver draws under Miri (Miri is ~100× slower than native, so a full run is a
few minutes). It **exits non-zero iff a soundness violation is found**, so it
doubles as a regression guard for the trusted base as new front-end constructs are
added.

Prerequisites: a nightly toolchain with Miri
(`rustup component add --toolchain nightly miri`).

Latest run (24 functions, `FUZZ_CASES=32`): **0 soundness violations**, 10/10 UB
shapes caught (all `UNKNOWN`, never `PASS`), 11/14 safe functions precise, 3
precision misses (`nested_get`, `window_sum`, `head_via_helper`).

## Why it matters beyond soundness

The `UNKNOWN`-on-safe-code rows are a **data-driven priority list**: they show
which capability would unlock the most real code, rather than guessing. This
harness already paid for itself on its first run — it surfaced that *any* method
call (`s.is_empty()`, `s.len()`, any helper) was invalidating every borrowed
region's liveness, so every access *after* a call came back `UNKNOWN`. That is
catastrophic for real, call-heavy code; the fix (a borrowed `&T`/`&mut T` region
survives a call, since the callee cannot free a borrow) turned the whole safe
corpus `PASS`.

## Corpus

`src/lib.rs` holds the corpus — 24 functions organised by the realistic patterns
that dominate real Rust, so the precision-miss rows form an honest priority list:

- **safe** (CSolver should `PASS`, Miri clean): bounds-checked / constant indexing,
  index and fill loops, the `s[len-1]` idiom, a conjoined two-slice guard, a
  modulo- and a `min`-clamped index, an off-by-one-*safe* pair access, a nested
  `m[i][j]` behind a guard, a two-slice copy loop, a sliding-window iterator, and
  two **helper chains** (the safety precondition crosses a call — one returning
  `Option<&_>`, one returning the bound);
- **UB on a reachable input** (CSolver must not `PASS`, Miri finds it when fuzzed):
  `get_unchecked` out of bounds, one-past-end, an unchecked write, a raw-pointer
  `add` and a raw-pointer `sub` before the start, an off-by-one *loop* that reads
  `s[len]`, an out-of-range index computed by a **helper**, a **conditional free**
  then a dangling use, a **null** dereference, and a `from_raw_parts` slice
  fabricated longer than its allocation.

Private `fn` helpers (used by the helper-chain functions) are not corpus entries —
the harness keys off `pub fn` — but they still appear in the emitted MIR, so those
cases exercise CSolver's interprocedural reasoning end to end. Extend the corpus by
adding a `pub fn` and a matching `drive_<fn>` fuzz test.
