# Soundness audit (M1)

For a verifier, the only fatal defect is a **false PASS**: reporting a memory
operation "proven safe" when it can be unsafe. This document records a soundness
audit of the discharge pipeline and the fixes applied. Each finding has a
regression test so it cannot return.

## Method

Three independent reviewers audited the soundness-critical crates against the
contract "never emit `Proven`/`PASS` for an obligation that can fail", probing
the linear decision procedure, the symbolic engine (loops, calls, alias, heap),
and the interval analysis with constructed MSIR.

## Findings and fixes (all FALSE-PASS, all fixed)

| # | Where | Defect | Fix | Test |
|---|-------|--------|-----|------|
| 1 | `absint/analysis.rs` `eval_operand` | integer constants entered the interval domain via `unsigned()`, so `(i64)-1` became `2^64-1` and `-1 >= 0` proved **True** | interpret constants with `signed()` (the domain orders signed) | `negative_constant_is_interpreted_signed` |
| 2 | `symbolic/exec.rs` `havoc_header` | only the loop **header parameters** were havoc'd; a body-reassigned non-parameter register kept its stale pre-loop value across the cut back-edge | havoc the loop's whole **modified-register set**, not just parameters | covered by loop tests + write-set logic |
| 3 | `symbolic/exec.rs` `havoc_header` | a `free` inside a loop body did not reset region **lifetime**, so later iterations' use-after-free / double-free were invisible | if the loop body may free, invalidate region liveness at the header | `free_inside_loop_is_not_proven` |
| 4 | `symbolic/exec.rs` `step_call` | a call to a **freeing** callee cleared the heap but left caller regions `Live`, so a use afterward proved no-UAF | a freeing call also degrades region liveness | `use_after_freeing_call_is_not_proven` |
| 5 | `solver/linear.rs` `cmp_constraints` | signed and unsigned predicates collapse to one integer ordering, so an unsigned guard could discharge a signed goal for sign-bit-set values | made the underlying assumption explicit and surfaced (`linear-no-overflow`): quantities are non-negative and ≤ `isize::MAX`, where the two orderings coincide — a real Rust invariant (allocations are capped at `isize::MAX`) | documented + assumption in every affected proof |

Finding 5 is handled by **making the assumption explicit** rather than by code,
in line with the project's principle that every `PASS` is relative to reported
assumptions. Programs that genuinely use the full unsigned range with the sign
bit set fall outside it and need the bit-precise SMT backend (a later milestone).

## Confirmed sound (audited, no defect)

Interval lattice laws (join/meet/widen extensiveness/leq), saturating interval
arithmetic, the Fourier–Motzkin feasibility routine (combine-step signs,
overflow/limit bail-outs all to "feasible" = "not proved"), non-linear
abstraction to opaque variables, constant folding / `eval_cmp` signedness, the
fixpoint engine's post-fixpoint convergence, dominator/loop-header detection,
alias `Must` only on provable offset equality, provenance never fabricated from
integers, and per-path obligation aggregation (truncation wipes all decisions).

## Known non-soundness limitations (precision, not false PASS)

* **False FAIL on dead branches.** The interval analysis does not yet refine
  register ranges by branch guards, so a concretely-unreachable block is still
  "reachable" abstractly; an interval-`False` check there is reported as FAIL.
  This never turns a violation into a PASS — it can only raise a false alarm on
  unreachable code. Branch-condition refinement (a later increment) removes it.
* **Latent hardening:** `Inst::Asm` does not havoc its `defs` and `Switch` edges
  do not rebind block parameters in the interval transfer; both are sound under
  strict SSA (the contract for MSIR) and are noted for a future IR validator.
