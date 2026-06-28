# Verification — csolver-smt

## Design
A uniform `SmtSolver` trait over BV/Array/UF, with pluggable backends and a
portable `NullSolver` fallback.

## Specification
- `NullSolver::check` always returns `SatResult::Unknown` — it decides nothing.

## Assumptions
- External backends (Z3/Bitwuzla/CVC5), when added, faithfully implement the
  SMT-LIB semantics of the declared theories.

## Limits
- M0 ships only the trait + `NullSolver`; real decision procedures are M2–M3.

## Proofs (arguments)
- **Sound default.** With `NullSolver`, every solver-dependent obligation
  becomes `UNKNOWN`, never a false `PASS`. This makes "no solver installed" a
  safe configuration.

## Test strategy
Unit test: declaring sorts/consts, push/assert/pop, and that `check` is
`Unknown`. Backend conformance suites (SMT-LIB benchmarks) planned with M2.
