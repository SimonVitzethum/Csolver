# Verification — csolver-solver

## Design
The shared value/constraint layer plus two decision procedures and a combined
prover:

- `expr`: a hash-consed symbolic expression IR (`Symbol`/`Const`/`Bin`/`Cmp`/
  `Ite`/connectives) with simplifying builders.
- `linear`: a sound, incomplete linear decision procedure (`prove_implies` via
  Fourier–Motzkin) over the integer model.
- `sat` + `bitblast` + `bitprecise`: a **pure-Rust bit-precise** decision
  procedure. `bitblast` lowers an `expr` graph to CNF (Tseitin gate circuits for
  the bit-vector ops), `sat` is a small DPLL solver, and
  `bitprecise::prove_implies` refutes `assumptions ∧ ¬goal` exactly.
  `bitprecise::find_counterexample` instead returns a **satisfying model** of
  `assumptions ∧ ¬goal` — a concrete witness mapping each named symbol to a
  value (read back from the SAT model via the bit-blaster's symbol table) — used
  by the symbolic engine to attach a counterexample to a `FAIL`.
- `prove_implies_method`: the combined prover the analyses call. It returns the
  `ProofMethod` (`BitPrecise` / `Linear`) that succeeded, so callers know which
  assumptions a `PASS` carries.
- the legacy `Term`/`Formula` constant-folding simplifier remains for now.

## Why pure-Rust SAT (no Z3)
A core project principle is *no C/C++ dependencies unless unavoidable*.
Bit-precise reasoning is **not** unavoidable in C++: bit-blasting to an internal
SAT solver achieves exact bit-vector semantics in pure Rust, builds in seconds
(no 4-minute C++ build), and is fully testable. An external solver (Z3/Bitwuzla)
could still be added later as an opt-in `SmtSolver` backend, but is not required
for bit-precise proofs.

## Specification
- `simplify_term`/`simplify` and the `expr` builders are **meaning-preserving**:
  the result is logically equivalent to the input (constant folding + identities
  + trivial-connective elimination), using wrapping bit-vector arithmetic at the
  operands' shared width.
- `bitblast` is an **equisatisfiable** encoding of fixed-width two's-complement
  (wrapping) bit-vector arithmetic — i.e. exactly Rust's value semantics. Each
  width-`w` value becomes `w` literals (LSB first); adders/subtractors are
  ripple-carry, comparisons use the subtraction borrow chain, multiplication is
  shift-add, shifts are constant-amount only. Gate builders fold the constant
  literal (so multiplying/masking by a constant collapses to shifts, keeping the
  CNF small).

## Soundness (arguments)
- **Simplification** is meaning-preserving: each rewrite is a tautology and
  hash-consing preserves identity.
- **`linear::prove_implies` is sound**: it returns `true` only when
  `assumptions ∧ ¬goal` is infeasible over the rationals. Rational-infeasible ⟹
  integer-infeasible ⟹ unsatisfiable ⟹ the implication holds. Non-linear terms
  become fresh opaque variables (precision loss only); overflow/size blow-up
  bail to "feasible" (= "not proved"), never to a false "proved". The integer
  model is sound under the caller-recorded `linear-no-overflow` assumption.
- **`sat` is sound for `Unsat`**: the only trusted result. A correct DPLL emits
  `Unsat` only after exhausting the assignment space; a decision-budget bail
  returns `Unknown` instead of guessing. So a budget bail loses precision, never
  soundness.
- **`bitprecise::prove_implies` is sound and assumption-free**: because
  bit-blasting is equisatisfiable and models wrapping exactly, an `Unsat` of the
  encoded `assumptions ∧ ¬goal` means there is genuinely no machine-value
  assignment satisfying the assumptions while falsifying the goal — so the
  implication holds for *all* values, with **no** `linear-no-overflow` side
  condition. Any other outcome (model found, budget exhausted, unblastable
  construct, CNF over the size cap) yields `false` = "not proved".
- **`prove_implies_method`** composes them soundly: linear first (fast), then a
  **tight-budget** bit-precise *refinement* (so a goal decidable exactly is
  reported `BitPrecise` and drops the overflow assumption), and a bit-precise
  *fallback* when linear fails (catching wrap/bitwise goals linear abstracts
  away). Every branch returns only a genuinely-proved verdict. The refinement
  budget is deliberately small because it runs on *every* linear success and is
  only a nicety: a *successful* bit-precise proof of a valid 64-bit bound — e.g.
  the unit-stride `i + 1 ≤ len` of a `&[u8]` access — makes the SAT solver grind
  out an `Unsat`, which a small budget cuts short, keeping such goals on the fast
  linear path (still sound, under the recorded assumption) rather than spending
  seconds upgrading them. (This was a real ~10× slowdown on unit-stride slice
  loops.)

## Limits
- The linear procedure does not linearize a `≠`/disjunctive *goal* (→ "not
  proved"). An *assumption* it cannot read (a `≠` guard, an opaque boolean) is
  **skipped**, not fatal: a smaller premise set only weakens the prover (it
  proves strictly fewer goals — never a false one), whereas bailing would defeat
  every later goal that depends on the *readable* premises (e.g. an `s[len - 1]`
  access proving from its `i <u len` bounds guard despite a sibling `len != 0`).
- Bit-blasting declines division/remainder, *symbolic* shift amounts, and widths
  above 64; the CNF size cap and SAT decision budget bound cost, so large or
  hard goals (e.g. two symbolic multiplicands) fall back to the linear method
  rather than dominating analysis time.
- `encode` (legacy `Formula` → `csolver-smt`) is still an `Unsupported` stub.

## Test strategy
Unit tests for hash-consing/sharing, folding, identities, comparison
folding/negation, connective normalization; the linear procedure
(implication/guard-bound/transitivity/soundness-non-proof); the SAT solver
(unit/empty-clause, pigeonhole and xor-chain UNSAT, model validity, budget
bail); the bit-precise procedure (guarded index with **no** overflow
assumption, wrap-around *not* proved, `x & 7 <= 7` proved where linear cannot,
unblastable fallback); and the combined `prove_implies_method`
(bit-precise-only mask, assumption-dropping guarded index, linear fallback for
non-wrapping scaling, unprovable → `None`). An end-to-end test
(`masked_index_is_proven_bit_precisely`) verifies a `buf[x & 7]` store as a
`PASS` that the linear procedure alone cannot reach.
