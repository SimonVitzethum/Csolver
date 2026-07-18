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

## Resolved precision defects (false FAIL, now fixed)

A false FAIL is not a soundness bug, but it erodes trust and buries real findings.
These were found while triaging a QEMU `--bugs` scan and fixed with a regression test.

| # | Where | Defect | Fix | Test |
|---|-------|--------|-----|------|
| P1 | `symbolic/exec/step.rs` shift check | the `NoShiftOverflow` obligation compared the shift **amount** against the width at which the *amount* was evaluated, not the width of the value being shifted. A `zext i32 (…) to i64` is a value-preserving no-op in the executor (still width 32), so `lshr i64 x, zext(i32 k)` was checked as `k < 32` and any `k ∈ [32, 64)` was falsely flagged as UB | evaluate the amount at the **result** type's width (`zext` it up first), then bound it by that width — a `lshr i64` amount is in range iff `< 64` | `shift_overflow_uses_the_shifted_value_width_not_the_amount_width` |

Corpus effect: `−20` spurious shift/div findings on the QEMU sample (`FAIL 480 → 468`),
no `PASS` lost, both differential oracles still `SOUND`.

| # | Where | Defect | Fix | Test |
|---|-------|--------|-----|------|
| P2 | `symbolic/exec/step.rs` Bin UB checks | an integer operation **wider than the bit-precise domain** (`MAX_WIDTH` = 128 — kernel crypto / SIMD `i256`/`i512`) made the scalar UB checks build a width-derived bound constant, and `BitVector::new` panicked (`"bit-vector width out of range"`). In a parallel scan the worker panic propagated through the scope join and **crashed the whole run** before the coverage report | skip the overflow / div-by-zero / shift obligations when `type_width(ty) > MAX_WIDTH`; the op is undecidable bit-precisely anyway, so it stays UNKNOWN. Sound (nothing proven ⇒ no false PASS) | `wide_integer_arithmetic_does_not_panic` |

A panic is treated as a bug to fix, never a file to silently drop: P2 turned a scan-killing crash into a graceful per-obligation UNKNOWN on exotic widths.

## Known non-soundness limitations (precision, not false PASS)

* **False FAIL on dead branches.** The interval analysis does not yet refine
  register ranges by branch guards, so a concretely-unreachable block is still
  "reachable" abstractly; an interval-`False` check there is reported as FAIL.
  This never turns a violation into a PASS — it can only raise a false alarm on
  unreachable code. Branch-condition refinement (a later increment) removes it.
* **Latent hardening:** `Inst::Asm` does not havoc its `defs` and `Switch` edges
  do not rebind block parameters in the interval transfer; both are sound under
  strict SSA (the contract for MSIR) and are noted for a future IR validator.
