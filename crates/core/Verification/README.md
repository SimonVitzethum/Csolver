# Verification — csolver-core

## Design
`core` defines the vocabulary of a CSolver proof: [`SafetyProperty`],
`ProofObligation`, `ObligationResult` (`Proven`/`Refuted`/`Open`), `ProofTree`,
`CounterExample`, `Assumption`, `Verdict`, and the concrete `BitVector` value.
It has **no internal dependencies**, so these types are a stable shared
language and the soundness policy lives in exactly one place. The property
catalogue includes `WriteCapability` — a write/access must target a region whose
**provenance** grants the capability (the write-to-a-read-only-page class, driven
by external contract labels; see `csolver-contracts`) — plus `NoInfoLeak`
(no `copy_to_user` of uninitialized memory), `NoSizeOverflow` (an `n*sizeof(C)`
allocation size must not wrap), and `DataRace` (currently the AA self-deadlock
subclass). Integer-UB obligations: `NoDivByZero`, `NoShiftOverflow`, and
`NoArithOverflow` (`nsw`/`nuw` add/sub/mul — signed mul via a `sext` double-width
product). Temporal/CFI: `NoDanglingDeref` (a dangling-stack return, an
`llvm.lifetime.end` use-after-scope) and `ValidIndirectTarget` (a null indirect-call
target). `NoAliasingViolation` — the Rust borrow-stack class, currently a **write
through a shared `&T`** — is opt-in behind `--aliasing-model`. `NoSizeOverflow`,
`DataRace`, `DoubleFetch`, `TaintedSink`, `TypestateViolation`, `SecretDependent`,
and `SleepInAtomic` are **bug-finding-only** obligations (the verifier does not
enumerate them in sound `verify` mode). The enum is `#[non_exhaustive]`, so external
matches must carry a wildcard arm.

## Specification
- `Verdict::combine` is a commutative, associative monoid with identity `Pass`;
  `Fail` is absorbing over `{Pass}` and dominates `Unknown`; `Unknown`
  dominates `Pass`.
- `ObligationResult::verdict` maps `Proven→Pass`, `Refuted→Fail`, `Open→Unknown`.
- `BitVector::new(w, v)` stores `v mod 2^w`; `signed()` is the two's-complement
  interpretation for every `w ∈ 1..=128`.

## Assumptions
- Scalar values fit in ≤128 bits (true for all MIR/LLVM/x86-64/AArch64 scalars).
- Locations are advisory (used for reporting); soundness never depends on them.

## Limits
- `BitVector` is concrete only; symbolic values live in `solver`/`smt`.
- `Error` models *tool* failures, never verification outcomes (those are verdicts).

## Proofs (arguments)
- **Roll-up soundness.** `combine` never yields `Pass` unless *both* inputs are
  `Pass`; hence a module `Pass` requires every obligation `Pass`. Proven by the
  exhaustive case table in `verdict.rs::tests` (commutativity, associativity,
  identity, absorption).
- **Two's-complement correctness.** `signed()` uses left-shift to bit 127 then
  arithmetic right-shift; tested at the boundaries (`-1`, `MIN`, width 64/128).

## Test strategy
Unit tests for the verdict lattice laws, bit-vector modular/seigned semantics,
proof-tree leaf counting, and model lookup. Property tests over the lattice laws
are planned (M1).
