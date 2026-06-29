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
bug: each unsafe corpus function is driven with the input that triggers its UB,
and the safe ones are driven over edge cases (empty / full / one-past).

## Running

```
./run.sh
```

It builds the `solver` CLI, emits the corpus MIR (`rustc --emit=mir`), runs
`solver verify`, then drives each function under `cargo +nightly miri test` and
prints a per-function table plus a summary. It **exits non-zero iff a soundness
violation is found**, so it doubles as a regression guard for the trusted base as
new front-end constructs are added.

Prerequisites: a nightly toolchain with Miri
(`rustup component add --toolchain nightly miri`).

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

`src/lib.rs` holds the corpus — provably-safe functions (bounds-checked indexing,
loops, the `s[len-1]` idiom, a guarded two-slice) and functions that are UB on a
reachable input (`get_unchecked` out of bounds, one-past-end, an unchecked write,
a raw-pointer `add`+deref). Extend it by adding a `pub fn` and a matching
`drive_<fn>` test.
