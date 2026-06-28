# What CSolver can and cannot prove

CSolver is a **sound** verifier: a `PASS` means *proven safe under the reported
assumptions*. This document is the honest map of where automation stops.

## The hard boundary

Full memory safety of an arbitrary program is **undecidable** (it encodes the
halting problem; Rice's theorem rules out any total decision procedure for a
non-trivial semantic property). So no tool — CSolver included — can return a
correct `PASS`/`FAIL` for *every* program. CSolver's design responds to this in
three ways:

1. **Soundness over completeness.** When unsure, CSolver says `UNKNOWN` (with
   residual obligations) or, if it finds a concrete violation, `FAIL` (with a
   counterexample). It never emits `PASS` without a proof.
2. **Explicit assumptions.** Every `PASS` is relative to a stated assumption set
   (FFI contracts, allocator behaviour, hardware memory model, decoded
   instruction semantics, parser correctness for binaries).
3. **Actionable residuals.** An `UNKNOWN` comes with the minimal extra
   assumption or annotation that would close the proof.

## Fully provable (target classes)

- **Constant / interval-decidable accesses.** Indices and sizes derived from
  constants and monotone updates whose ranges the interval (and later
  octagon/polyhedra) domains bound — e.g. fixed-size buffer indexing, many
  iterator and slice patterns. *Already today for constant indices.*
- **Bounded loops** whose trip count and induction variables yield a loop
  invariant via widening+narrowing (M1) or unrolling within a bound (M2).
- **Linear pointer arithmetic within one object**, including one-past-the-end,
  where provenance is tracked (the memory model + SMT array theory, M3).
- **Temporal safety with statically-matched alloc/free** (UAF/double-free) when
  the allocation lattice is precise enough (M3).

## Conditionally provable (needs an assumption/annotation)

- **FFI / external calls** — provable given a summarized contract (preconditions
  on pointers/lengths). Without it: `UNKNOWN` + a suggested contract.
- **`int → ptr` casts** — provenance is lost; provable given an assumption that
  re-establishes which object the integer addresses.
- **Inline assembly** — provable only for the fragment with a supplied semantics;
  otherwise an explicit assumption over its clobbers/effects.
- **Indirect calls/branches** — provable when the target set is recoverable
  (vtables, jump tables); otherwise a `ValidIndirectTarget` assumption.
- **Unbounded loops / recursion** — provable given a user-supplied loop invariant
  or ranking/bound annotation.

## Not automatically decidable

- Properties depending on **unbounded nondeterminism** the model cannot close
  (e.g. arbitrary attacker-controlled lengths with no relating constraint).
- **Concurrency / weak-memory** data-race-dependent safety (out of M0–M5 scope;
  would need a memory-model-aware extension).
- Anything equivalent to deciding termination of an arbitrary computation.

## How an `UNKNOWN` is reported

For each open obligation the report gives: the residual predicate, *why* it is
open (unbounded loop, opaque FFI, solver `unknown`, lost provenance, …), and a
**suggested minimal assumption** that would make it `PASS`. The goal is that a
human (or a future annotation pass) can close the remaining gap with the least
possible added trust.
