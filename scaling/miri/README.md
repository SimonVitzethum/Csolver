# Soundness at scale: real crates under Miri

The [scaling sweep](../README.md) measured **coverage** — ≈91% of real crate
functions verify `PASS`. It did not test those verdicts against an independent
oracle. The [differential corpus](../../differential) does, but only on ~30
hand-written functions, so the real-crate PASS verdicts were *trusted, not tested*.
A lowering bug that models a memory construct **wrong** (not merely not-at-all)
would surface as a `PASS` with nothing to catch it — which is exactly how the
cleanup-block bug slipped in until a curated UB function happened to hit the same
path. That was luck, not a system.

This harness closes the gap: it fuzzes each real crate's public API and runs it
under **Miri**, executing the very functions CSolver verified, on real inputs.

```
./run.sh                  # FUZZ_CASES=40 per driver under Miri
FUZZ_CASES=200 ./run.sh   # deeper
```

- **Miri `Undefined Behavior` in a crate whose functions CSolver verified `PASS`**
  is a candidate false `PASS` — cross-reference the Miri backtrace's function
  against that crate's per-function verdicts from `../run.sh`.
- **Miri clean** over a broad fuzz means the executed `PASS` functions are
  validated on those paths: the coverage number becomes a *trustworthy* one.

Only Miri's *Undefined Behavior* is the oracle — a Rust panic is safe behaviour.
Built offline from the cargo cache (a standalone crate with its own `[workspace]`,
like `../../differential`).

## Crates driven

The unsafe-heavy data structures are the most valuable targets — their internal
`unsafe` (raw writes, element shifting) is what a lowering bug would mis-model and
what a latent crate bug would trip:

- **`arrayvec`**, **`tinyvec`** — fixed-capacity vectors; fuzzed with random
  sequences of push/pop/insert/remove/swap_remove/truncate/index.
- **`adler2`** — Adler-32 checksum; exercises the index-into-struct-field lowering
  (its state is a `[u32; 4]` field updated as `((*_1).0)[i]`).
- **`oorandom`** — the PRNGs (arithmetic baseline).
- **`itoa`** — integer formatting into a fixed buffer (raw byte writes).

## Honest scope

This validates **executed paths**, not every `PASS` function: fuzzing reaches a
crate's public API and its transitive internals, but a `PASS` function not reachable
through the driven API (or needing a specific input) is not exercised. It is partial,
independent validation where there was none — and it extends directly: add a driver
for another crate, or raise `FUZZ_CASES`. The mapping is coarse (crate-level): a Miri
UB names its function in the backtrace, which is then checked against CSolver's
verdict for that function.

## Latest run

5 crates, `FUZZ_CASES=40`: **0 Miri UB** — every fuzzed real-crate API is clean, so
the executed PASS functions (adler2, oorandom, arrayvec, tinyvec, itoa) are validated
against the independent oracle.
