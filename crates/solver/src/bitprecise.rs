//! A bit-precise decision procedure: prove `assumptions ⟹ goal` exactly, with
//! no arithmetic-overflow assumption, by bit-blasting `assumptions ∧ ¬goal` to
//! CNF ([`crate::bitblast`]) and refuting it with the internal SAT solver
//! ([`crate::sat`]).
//!
//! ## Soundness
//!
//! Bit-blasting is an equisatisfiable encoding of fixed-width two's-complement
//! (wrapping) bit-vector arithmetic — exactly Rust's value semantics. So if the
//! SAT solver reports the encoded `assumptions ∧ ¬goal` **unsatisfiable**, there
//! is genuinely no bit-vector assignment that satisfies the assumptions yet
//! falsifies the goal: the implication holds for every machine value, with
//! **no** `linear-no-overflow` side condition. Any other outcome — a model
//! found, the budget exhausted, or an unblastable construct — yields `false`
//! ("not proved"), which the caller treats as `UNKNOWN`, never as a refutation.
//! Thus the procedure can only ever lose precision, never soundness.

use crate::bitblast::Blaster;
use crate::expr::{ExprCtx, ExprId};
use crate::sat::{SatResult, Solver, DEFAULT_BUDGET};
use csolver_core::{Assignment, BitVector, Model};

/// Upper bound on the bit-blasted CNF size. Past this we decline (return "not
/// proved") rather than hand the SAT solver a formula large enough to dominate
/// the analysis time — the linear procedure is the right tool for those goals.
const MAX_CLAUSES: usize = 60_000;

/// Try to prove `assumptions ⟹ goal` bit-precisely. Returns `true` only when
/// the implication is established for all machine values (see soundness note).
pub fn prove_implies(ctx: &ExprCtx, assumptions: &[ExprId], goal: ExprId) -> bool {
    prove_implies_budget(ctx, assumptions, goal, DEFAULT_BUDGET)
}

/// As [`prove_implies`], with an explicit SAT decision budget.
pub fn prove_implies_budget(
    ctx: &ExprCtx,
    assumptions: &[ExprId],
    goal: ExprId,
    budget: u64,
) -> bool {
    let mut blaster = Blaster::new(ctx);

    // Assert each assumption.
    for &a in assumptions {
        match blaster.encode_bool(a) {
            Some(lit) => blaster.cnf.clauses.push(vec![lit]),
            None => return false, // unblastable assumption ⇒ cannot refute soundly
        }
    }
    // Assert the negation of the goal.
    match blaster.encode_bool(goal) {
        Some(lit) => blaster.cnf.clauses.push(vec![lit.negated()]),
        None => return false,
    }

    let cnf = blaster.cnf;
    if cnf.clauses.len() > MAX_CLAUSES {
        return false; // too large to refute affordably; fall back soundly
    }
    let mut solver = Solver::new(cnf.num_vars, cnf.clauses);
    matches!(solver.solve(budget), SatResult::Unsat)
}

/// Find a concrete model witnessing `assumptions ∧ ¬goal` — i.e. inputs that
/// satisfy the assumptions yet **violate** the goal. Returns the named symbol
/// values, or `None` if no such model exists, the query is unblastable, or the
/// CNF/budget limits are hit.
///
/// The model is a genuine bit-vector assignment, so a caller that has already
/// established (bit-precisely, on an exact path) that the goal is *always*
/// violated can present this as a sound counterexample.
pub fn find_counterexample(
    ctx: &ExprCtx,
    assumptions: &[ExprId],
    goal: ExprId,
) -> Option<Model> {
    let mut blaster = Blaster::new(ctx);
    for &a in assumptions {
        let lit = blaster.encode_bool(a)?;
        blaster.cnf.clauses.push(vec![lit]);
    }
    let g = blaster.encode_bool(goal)?;
    blaster.cnf.clauses.push(vec![g.negated()]);

    if blaster.cnf.clauses.len() > MAX_CLAUSES {
        return None;
    }
    // Capture the symbol → literal map before the CNF is consumed.
    let syms: Vec<(String, u32, Vec<crate::sat::Lit>)> = blaster.symbols().to_vec();
    let cnf = blaster.cnf;
    let mut solver = Solver::new(cnf.num_vars, cnf.clauses);
    let SatResult::Sat(model) = solver.solve(DEFAULT_BUDGET) else {
        return None;
    };

    let mut assignments = Vec::new();
    for (name, width, bits) in syms {
        let mut value: u128 = 0;
        for (i, lit) in bits.iter().enumerate() {
            // A symbol's bits are fresh positive literals; read the model bit.
            let bit = model.get(lit.var as usize).copied().unwrap_or(false) != lit.neg;
            if bit {
                value |= 1u128 << i;
            }
        }
        assignments.push(Assignment {
            name,
            value: BitVector::new(width, value),
        });
    }
    Some(Model { assignments })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{BvOp, CmpOp};

    #[test]
    fn proves_reflexive_implication() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 32);
        let len = c.symbol("len", 32);
        let lt = c.cmp(CmpOp::Ult, i, len);
        assert!(prove_implies(&c, &[lt], lt));
    }

    #[test]
    fn proves_guarded_index_without_overflow_assumption() {
        // {0 <=u i, i <u len} ⟹ i <u len  — purely bit-precise.
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 32);
        let len = c.symbol("len", 32);
        let zero = c.int(32, 0);
        let nonneg = c.cmp(CmpOp::Ule, zero, i);
        let guard = c.cmp(CmpOp::Ult, i, len);
        let goal = c.cmp(CmpOp::Ult, i, len);
        assert!(prove_implies(&c, &[nonneg, guard], goal));
    }

    #[test]
    fn refutes_unsound_bound() {
        // i <u len does NOT imply i <u len-1 (wrapping-aware).
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 8);
        let len = c.symbol("len", 8);
        let guard = c.cmp(CmpOp::Ult, i, len);
        let one = c.int(8, 1);
        let lenm1 = c.bin(BvOp::Sub, len, one);
        let goal = c.cmp(CmpOp::Ult, i, lenm1);
        assert!(!prove_implies(&c, &[guard], goal));
    }

    #[test]
    fn catches_wraparound_the_linear_model_misses() {
        // Over u8: x <=u 200 does NOT imply x + 100 >=u x, because the addition
        // wraps. A bit-precise solver must NOT prove the monotonicity claim.
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 8);
        let twohundred = c.int(8, 200);
        let bound = c.cmp(CmpOp::Ule, x, twohundred);
        let hundred = c.int(8, 100);
        let xp = c.bin(BvOp::Add, x, hundred);
        let goal = c.cmp(CmpOp::Uge, xp, x); // false when x+100 wraps past 255
        assert!(!prove_implies(&c, &[bound], goal));
    }

    #[test]
    fn proves_nonwrapping_addition_is_monotonic() {
        // Over u8: x <=u 100 ⟹ x + 100 >=u x (no wrap possible: x+100 <= 200).
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 8);
        let hundred = c.int(8, 100);
        let bound = c.cmp(CmpOp::Ule, x, hundred);
        let xp = c.bin(BvOp::Add, x, hundred);
        let goal = c.cmp(CmpOp::Uge, xp, x);
        assert!(prove_implies(&c, &[bound], goal));
    }

    #[test]
    fn proves_bitwise_and_upper_bound() {
        // x & 7 <=u 7 always — a fact the *linear* procedure cannot see (it
        // abstracts `&` as opaque), but bit-blasting decides exactly.
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 32);
        let seven = c.int(32, 7);
        let masked = c.bin(BvOp::And, x, seven);
        let goal = c.cmp(CmpOp::Ule, masked, seven);
        assert!(prove_implies(&c, &[], goal));
    }

    #[test]
    fn signed_max_is_a_tautology() {
        // Every i8 value is <=s 127 (the signed maximum) — validates the signed
        // comparator at the sign boundary.
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 8);
        let max = c.int(8, 127);
        let goal = c.cmp(CmpOp::Sle, x, max);
        assert!(prove_implies(&c, &[], goal));
    }

    #[test]
    fn signed_compare_respects_the_sign_bit() {
        // x <=s -1 ⟹ x <s 0 (a negative value is below zero)...
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 8);
        let neg1 = c.int(8, 0xff); // -1 as i8
        let zero = c.int(8, 0);
        let neg = c.cmp(CmpOp::Sle, x, neg1);
        let below_zero = c.cmp(CmpOp::Slt, x, zero);
        assert!(prove_implies(&c, &[neg], below_zero));
        // ...but a negative value is NOT signed-greater than 100.
        let hundred = c.int(8, 100);
        let above = c.cmp(CmpOp::Sgt, x, hundred);
        assert!(!prove_implies(&c, &[neg], above));
    }

    #[test]
    fn does_not_prove_false_goal() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 16);
        let eight = c.int(16, 8);
        let goal = c.cmp(CmpOp::Ult, i, eight);
        assert!(!prove_implies(&c, &[], goal));
    }

    #[test]
    fn counterexample_witnesses_a_violation() {
        // `x | 8` is always >= 8, so the goal `x|8 <u 8` is never satisfiable:
        // the negation is bit-precisely provable, and a concrete witness exists.
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 8);
        let eight = c.int(8, 8);
        let masked = c.bin(BvOp::Or, x, eight);
        let goal = c.cmp(CmpOp::Ult, masked, eight);
        let not_goal = c.not(goal);
        assert!(prove_implies(&c, &[], not_goal), "goal is always violated");
        let model = find_counterexample(&c, &[], goal).expect("a witness exists");
        // The witness assigns the input symbol a concrete value.
        assert!(model.get("x").is_some(), "the witness assigns x: {model:?}");
    }

    #[test]
    fn no_counterexample_for_a_tautology() {
        // `x | 8 >=u 8` always holds, so there is no violating model.
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 8);
        let eight = c.int(8, 8);
        let masked = c.bin(BvOp::Or, x, eight);
        let goal = c.cmp(CmpOp::Uge, masked, eight);
        assert!(find_counterexample(&c, &[], goal).is_none());
    }

    #[test]
    fn wrapping_extent_needs_a_no_overflow_guard() {
        // Demonstrates the in-bounds false-PASS hole the symbolic executor's
        // no-overflow conjunct closes. Pin offset to 2^63 - 4 (signed-positive),
        // access size 8, region size 16 — a blatant OOB.
        let w = 64;
        let mut c = ExprCtx::new();
        let off = c.symbol("off", w);
        let pin = c.int(w, (1u128 << 63) - 4);
        let assume = c.cmp(CmpOp::Eq, off, pin);
        let eight = c.int(w, 8);
        let end = c.bin(BvOp::Add, off, eight); // wraps to a negative value
        let size = c.int(w, 16);
        // The naive upper bound `offset + 8 <=s 16` is *vacuously* provable because
        // the wrapped `end` is negative — exactly the false PASS.
        let upper = c.cmp(CmpOp::Sle, end, size);
        assert!(
            prove_implies(&c, &[assume], upper),
            "wrapping makes the naive upper bound vacuously true (the hole)",
        );
        // The no-overflow guard `offset <=s offset+8` is NOT provable here, so the
        // strengthened conjunction correctly declines to prove in-bounds.
        let no_overflow = c.cmp(CmpOp::Sle, off, end);
        assert!(
            !prove_implies(&c, &[assume], no_overflow),
            "the no-overflow guard rejects the wrapped extent",
        );
    }

    #[test]
    fn unblastable_goal_is_not_proved() {
        // Division is not bit-blasted ⇒ sound fallback (false), never a crash.
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 32);
        let y = c.symbol("y", 32);
        let q = c.bin(BvOp::UDiv, x, y);
        let goal = c.cmp(CmpOp::Ule, q, x);
        assert!(!prove_implies(&c, &[], goal));
    }
}
