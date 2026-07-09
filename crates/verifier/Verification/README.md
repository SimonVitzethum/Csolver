# Verification — csolver-verifier

## Design
The orchestrator. For each function it runs the interval analysis, turns every
`SafetyCheck` into a `ProofObligation`, discharges it (interval first, SMT
later), and rolls up `Verdict`s into a `ModuleReport`. It threads module-wide
context to the symbolic executor: parameter/field contracts, globals, the
provenance lattice (`Module::prov_grants`, for `WriteCapability`), the
devirtualization table (`Module::global_fn_ptrs`), and the already-computed
interval analysis (so the executor reuses it instead of a second fixpoint).

`NoSizeOverflow` and `DataRace` are **bug-finding-only** obligations — skipped in
the implied-check enumeration unless `config.bug_finding`, so sound `verify`
PASS/FAIL is unchanged. `Config.time_budget` (`None` = unbounded) bounds the
executor's per-function wall-clock; `FunctionReport.truncated` /
`ModuleReport::any_truncated()` surface a budget hit so a scan can defer the unit.

## Specification
- `Trivalent::True → Proven(ProofTree)`, `False → Refuted(CounterExample)`,
  `Unknown → Open{residual, suggested}`.
- Function verdict = `combine` of its obligation verdicts; module verdict =
  `combine` of function verdicts.

## Assumptions
- The obligations the frontend emitted are the obligations that matter: a
  function with no `SafetyCheck`s is vacuously `PASS` **over the emitted checks**
  (so a frontend that under-emits checks weakens coverage, not soundness of the
  checks it did emit).
- The interval analysis is sound (see `csolver-absint/Verification`).

## Discharge pipeline (M1, increments 1–2)
Two obligation sources:
1. **Explicit `SafetyCheck`s** — intervals first (cheapest); an interval
   `Unknown` escalates to the symbolic scalar layer.
2. **Implied memory-op obligations** — enumerated from the IR via
   `Inst::implied_checks` (so a `Load`/`Store`/`PtrOffset`/`Dealloc` is never
   silently passed) and decided by the symbolic memory model. When symbolic did
   not run (loops/disabled/truncated) they are `Open`, not `Pass`.

A symbolic `Proven` yields a proof tree recording the assumptions it relied on
(`linear-no-overflow`, `alloc-succeeds`); `verify_module` collects the union of
all such assumptions across the module and lists them in the report.

## Limits
- Symbolic discharge is acyclic + scalar-relational only (loops, symbolic
  memory, summaries, recursion are later increments). Such cases stay `Unknown`.
- Counterexamples carry a summary but an empty concrete model until the SMT
  model-extraction layer lands.

## Proofs (arguments)
- **No false PASS.** A `Proven` is emitted only on `Trivalent::True`, which is
  sound by the absint discharge argument; `Unknown` never upgrades. The
  end-to-end tests assert that a symbolic index is `UNKNOWN`, not `PASS`.
- **Worst-case roll-up.** `combine` makes any `FAIL` dominate; the
  `module_verdict_is_the_worst_case` test pins this.

## Test strategy
Integration tests in `csolver-testsuite`: provably-safe ⇒ PASS, provably-buggy ⇒
FAIL+counterexample, symbolic ⇒ UNKNOWN+residual+suggestion, mixed module ⇒ FAIL.
