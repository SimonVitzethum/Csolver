# C differential validation

The C counterpart to the Rust/Miri differential harness one directory up. It checks
CSolver's **static** verdicts against a **dynamic** soundness oracle over a corpus of
small C functions, so a false `PASS` (the cardinal sin) cannot hide.

## The oracle

For Rust the oracle is Miri. For C it is **AddressSanitizer + UndefinedBehaviorSanitizer**:

- ASan — spatial (heap/stack buffer overflow) and temporal (use-after-free, double-free).
- UBSan, **memory subset only** — out-of-bounds array indexing, misalignment, null deref,
  pointer-arithmetic overflow.

Arithmetic UB (signed overflow, shifts, divide-by-zero) is **excluded on purpose**: CSolver
proves *memory* safety, not overflow-freedom, so counting it would manufacture false
violations. `f_signed_ovf` is a control that exercises this — it is arithmetic UB, stays
CLEAN under the memory-scoped oracle, and CSolver PASSes it.

## Method

Each corpus function is **self-contained** (it owns its buffer — a fixed local array or a
constant-size `malloc`) and takes a fuzzable scalar, so CSolver reasons about it with no
caller, mirroring how the Rust corpus is self-contained via slice types. The driver fuzzes
that scalar across a range spanning the in-bounds/OOB boundary (a deterministic SplitMix64
PRNG), so a function that is UB on a reachable input actually reaches it.

The classification per function:

| oracle | CSolver | meaning |
|--------|---------|---------|
| UB     | PASS    | **soundness violation** — a false PASS (must be zero) |
| UB     | !PASS   | sound — caught as UNKNOWN/FAIL |
| clean  | PASS    | precise |
| clean  | !PASS   | precision miss (UNKNOWN on safe) — the priority list |

## Running

```sh
./run.sh                 # full sweep (FUZZ_CASES=256 by default)
FUZZ_CASES=4096 ./run.sh # deeper fuzz
./run.sh --selftest      # positive-control the violation detector itself
```

Exits non-zero iff any soundness violation is found. `--selftest` feeds the classifier a
synthetic `(PASS, UB)` row and asserts it is flagged, so a reported "0 violations" cannot be
a broken metric.

## Requirements

`clang` with ASan/UBSan. On hardened kernels ASan's shadow mapping collides with a PIE load
address; the build uses `-no-pie` to place the binary low and avoid it (the ELF_ET_DYN_BASE
issue) — it does not affect the verdicts.
