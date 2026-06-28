# Verification — csolver-testsuite

## Design
End-to-end fixtures (MSIR modules modelling real, often `unsafe`, Rust patterns)
plus the integration tests that drive `ir → cfg → absint → verifier → report`.

## Specification
- `provably_safe` ⇒ PASS, `provably_buggy` ⇒ FAIL+counterexample,
  `needs_solver` ⇒ UNKNOWN+residual+suggestion, `mixed_module` ⇒ FAIL.

## Assumptions
- Until real frontends land, fixtures are hand-built MSIR; they are replaced by
  lowered Rust/`unsafe` programs as frontends mature.

## Limits
- Coverage is only as broad as the fixtures; it grows with each milestone.

## Proofs (arguments)
- These tests are the executable form of the soundness claims: in particular
  `symbolic_index_is_unknown_not_pass` guards against the single worst failure
  (a false `PASS`).

## Test strategy
`tests/end_to_end.rs` asserts verdicts, result shapes, and rendered output.
A growing corpus of real-program fixtures is the M1+ plan.
