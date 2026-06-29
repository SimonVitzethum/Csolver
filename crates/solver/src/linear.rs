//! A sound, incomplete decision procedure for the linear-arithmetic fragment.
//!
//! Given assumptions and a goal (boolean [`ExprId`]s), [`prove_implies`] tries
//! to show `assumptions ⟹ goal` by proving `assumptions ∧ ¬goal`
//! *unsatisfiable*. It linearizes the relevant comparisons into integer
//! inequalities and runs Fourier–Motzkin elimination.
//!
//! ## Soundness
//!
//! We only ever return `true` (proved) when the linear system is **infeasible
//! over the rationals**. Rational-infeasible implies integer-infeasible, which
//! implies the original formula is unsatisfiable — so a `true` result is sound.
//! Non-linear sub-terms (multiplication of two unknowns, division, bitwise ops,
//! shifts) are abstracted as fresh opaque variables, which only loses
//! precision.
//!
//! ### The integer model and its assumption
//!
//! Bit-vector values are interpreted over the mathematical integers, and the
//! two signedness variants of each predicate (`Ult`/`Slt`, …) are mapped to the
//! same integer ordering. This is sound **only under the assumption that every
//! quantity reasoned about is non-negative and fits in the signed range**
//! (i.e. `0 ≤ v ≤ isize::MAX`), because then a value's signed and unsigned
//! interpretations coincide and no addition/subtraction wraps. That assumption
//! is a genuine invariant for memory-safety quantities in valid Rust — the
//! allocator caps any single allocation at `isize::MAX` bytes (`Layout`), so
//! offsets, sizes and in-bounds indices are all within `[0, isize::MAX]`.
//! Callers attach the `linear-no-overflow` assumption to proofs that rely on
//! this (see `csolver-verifier`), keeping every such `PASS` explicitly relative
//! to it. A program that genuinely uses the full unsigned range with the sign
//! bit set falls outside the assumption and must be modelled bit-precisely
//! (the external SMT backends, a later milestone).

use crate::expr::{BvOp, CmpOp, ExprCtx, ExprId, Node};
use std::collections::BTreeMap;

/// Upper bound on the constraint set size before Fourier–Motzkin bails out
/// (returning "feasible", i.e. "cannot prove") to stay affordable and sound.
const CONSTRAINT_LIMIT: usize = 4096;

/// A linear form `Σ coeff_i · atom_i + constant`.
#[derive(Clone, Debug, Default)]
struct Linear {
    coeffs: BTreeMap<ExprId, i128>,
    constant: i128,
}

impl Linear {
    fn constant(c: i128) -> Linear {
        Linear {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    fn atom(e: ExprId) -> Linear {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(e, 1);
        Linear {
            coeffs,
            constant: 0,
        }
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn coeff_of(&self, v: ExprId) -> i128 {
        self.coeffs.get(&v).copied().unwrap_or(0)
    }

    fn normalized(mut self) -> Linear {
        self.coeffs.retain(|_, c| *c != 0);
        self
    }

    fn add(&self, o: &Linear) -> Option<Linear> {
        let mut out = self.clone();
        out.constant = out.constant.checked_add(o.constant)?;
        for (&k, &c) in &o.coeffs {
            let e = out.coeffs.entry(k).or_insert(0);
            *e = e.checked_add(c)?;
        }
        Some(out.normalized())
    }

    fn scale(&self, k: i128) -> Option<Linear> {
        let mut out = Linear::constant(self.constant.checked_mul(k)?);
        for (&atom, &c) in &self.coeffs {
            out.coeffs.insert(atom, c.checked_mul(k)?);
        }
        Some(out.normalized())
    }

    fn sub(&self, o: &Linear) -> Option<Linear> {
        let neg = o.scale(-1)?;
        self.add(&neg)
    }

    fn add_const(&self, k: i128) -> Option<Linear> {
        let mut out = self.clone();
        out.constant = out.constant.checked_add(k)?;
        Some(out)
    }
}

/// Interpret a constant as a mathematical integer (unsigned when it fits).
fn const_to_int(bv: csolver_core::BitVector) -> i128 {
    let u = bv.unsigned();
    if u <= i128::MAX as u128 {
        u as i128
    } else {
        bv.signed()
    }
}

/// Linearize an integer-valued expression, or `None` on overflow.
///
/// Non-linear shapes degrade to a fresh opaque variable (the node itself),
/// which is always sound (it just forgets the term's structure).
fn linearize(ctx: &ExprCtx, e: ExprId) -> Option<Linear> {
    match ctx.node(e) {
        Node::Const(bv) => Some(Linear::constant(const_to_int(*bv))),
        Node::Bin { op, a, b } => {
            let la = linearize(ctx, *a)?;
            let lb = linearize(ctx, *b)?;
            match op {
                BvOp::Add => la.add(&lb),
                BvOp::Sub => la.sub(&lb),
                BvOp::Mul => {
                    if la.is_constant() {
                        lb.scale(la.constant)
                    } else if lb.is_constant() {
                        la.scale(lb.constant)
                    } else {
                        Some(Linear::atom(e))
                    }
                }
                _ => Some(Linear::atom(e)),
            }
        }
        // Symbols and every non-arithmetic node become opaque variables.
        _ => Some(Linear::atom(e)),
    }
}

/// Build the `≤ 0` constraints equivalent to `e == truth`, or `None` if `e`
/// cannot be expressed as a conjunction of linear inequalities.
fn constraints_of(ctx: &ExprCtx, e: ExprId, truth: bool) -> Option<Vec<Linear>> {
    match ctx.node(e) {
        Node::Bool(b) => {
            if *b == truth {
                Some(Vec::new())
            } else {
                // An unsatisfiable literal: `1 ≤ 0`.
                Some(vec![Linear::constant(1)])
            }
        }
        Node::Not(x) => constraints_of(ctx, *x, !truth),
        Node::And(xs) => {
            if truth {
                let mut out = Vec::new();
                for &x in xs {
                    out.extend(constraints_of(ctx, x, true)?);
                }
                Some(out)
            } else {
                // ¬(a ∧ b) is a disjunction — not a conjunction of inequalities.
                None
            }
        }
        Node::Or(xs) => {
            if !truth {
                let mut out = Vec::new();
                for &x in xs {
                    out.extend(constraints_of(ctx, x, false)?);
                }
                Some(out)
            } else {
                None
            }
        }
        Node::Cmp { op, a, b } => {
            let la = linearize(ctx, *a)?;
            let lb = linearize(ctx, *b)?;
            let eff = if truth { *op } else { op.negate() };
            cmp_constraints(eff, &la, &lb)
        }
        _ => None,
    }
}

/// The `≤ 0` constraints for `la (op) lb` (signedness collapsed; see soundness
/// note — the integer relation is what we reason about).
fn cmp_constraints(op: CmpOp, la: &Linear, lb: &Linear) -> Option<Vec<Linear>> {
    let mut res = match op {
        // a < b  ⇔  a - b + 1 ≤ 0   (integers)
        CmpOp::Ult | CmpOp::Slt => vec![la.sub(lb)?.add_const(1)?],
        // a ≤ b  ⇔  a - b ≤ 0
        CmpOp::Ule | CmpOp::Sle => vec![la.sub(lb)?],
        // a > b  ⇔  b - a + 1 ≤ 0
        CmpOp::Ugt | CmpOp::Sgt => vec![lb.sub(la)?.add_const(1)?],
        // a ≥ b  ⇔  b - a ≤ 0
        CmpOp::Uge | CmpOp::Sge => vec![lb.sub(la)?],
        // a = b  ⇔  a - b ≤ 0 ∧ b - a ≤ 0
        CmpOp::Eq => vec![la.sub(lb)?, lb.sub(la)?],
        // a ≠ b is a disjunction.
        CmpOp::Ne => return None,
    };
    // For an *unsigned* predicate both operands are non-negative (their unsigned
    // value). Adding `0 ≤ a` and `0 ≤ b` is sound under the `linear-no-overflow`
    // assumption (quantities are in `[0, isize::MAX]`) and supplies the lower
    // bound that `usize` indexing needs — e.g. `i <u len` then yields `i ≥ 0`.
    if matches!(op, CmpOp::Ult | CmpOp::Ule | CmpOp::Ugt | CmpOp::Uge) {
        res.push(la.scale(-1)?); // -a ≤ 0
        res.push(lb.scale(-1)?); // -b ≤ 0
    }
    Some(res)
}

/// Decide whether a set of `≤ 0` constraints is infeasible over the rationals.
/// Returns `true` if **feasible** (or if we had to bail), `false` if proven
/// infeasible.
fn feasible(mut constraints: Vec<Linear>) -> bool {
    loop {
        // Any pure-constant constraint with positive constant is a direct
        // contradiction.
        for c in &constraints {
            if c.is_constant() && c.constant > 0 {
                return false;
            }
        }
        // Pick a variable to eliminate.
        let Some(v) = constraints
            .iter()
            .flat_map(|c| c.coeffs.keys().copied())
            .next()
        else {
            // No variables left and no contradiction found: feasible.
            return true;
        };

        let mut pos = Vec::new();
        let mut neg = Vec::new();
        let mut next = Vec::new();
        for c in constraints {
            let cv = c.coeff_of(v);
            if cv > 0 {
                pos.push(c);
            } else if cv < 0 {
                neg.push(c);
            } else {
                next.push(c);
            }
        }

        for p in &pos {
            for n in &neg {
                let a = p.coeff_of(v); // > 0
                let b = -n.coeff_of(v); // > 0
                let (Some(bp), Some(an)) = (p.scale(b), n.scale(a)) else {
                    return true; // overflow: bail, soundly "feasible"
                };
                let Some(mut combined) = bp.add(&an) else {
                    return true;
                };
                combined.coeffs.remove(&v);
                let combined = combined.normalized();
                if combined.is_constant() && combined.constant > 0 {
                    return false;
                }
                next.push(combined);
                if next.len() > CONSTRAINT_LIMIT {
                    return true; // too large: bail
                }
            }
        }
        constraints = next;
    }
}

/// Try to prove `assumptions ⟹ goal`. Returns `true` only when the proof
/// succeeds (sound); `false` means "not proved" (the caller treats it as
/// `UNKNOWN`, never as a refutation).
pub fn prove_implies(ctx: &ExprCtx, assumptions: &[ExprId], goal: ExprId) -> bool {
    let mut constraints = Vec::new();
    for &a in assumptions {
        // An assumption the linear fragment cannot read (a `≠` guard, an opaque
        // boolean from an unmodelled check, …) is **skipped**, not fatal: dropping
        // a premise only weakens the prover (a smaller constraint set is *more*
        // feasible, so it proves *fewer* goals — never a false proof), while
        // bailing entirely would defeat every later goal. This lets, e.g., a
        // `s[len - 1]` access prove from its `i <u len` bounds guard even though
        // the sibling `len != 0` guard is a disequality the fragment cannot use.
        if let Some(cs) = constraints_of(ctx, a, true) {
            constraints.extend(cs);
        }
    }
    match constraints_of(ctx, goal, false) {
        Some(cs) => constraints.extend(cs),
        None => return false,
    }
    !feasible(constraints)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proves_direct_implication() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let len = c.symbol("len", 64);
        let lt = c.cmp(CmpOp::Ult, i, len);
        // (i < len) ⟹ (i < len)
        assert!(prove_implies(&c, &[lt], lt));
    }

    #[test]
    fn proves_idx_lt_len_from_guard() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let len = c.symbol("len", 64);
        let guard = c.cmp(CmpOp::Ult, i, len);
        let zero = c.int(64, 0);
        let nonneg = c.cmp(CmpOp::Uge, i, zero);
        let check = c.cmp(CmpOp::Ult, i, len);
        // {0 ≤ i, i < len} ⟹ i < len
        assert!(prove_implies(&c, &[nonneg, guard], check));
    }

    #[test]
    fn proves_transitive_bound() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let len = c.symbol("len", 64);
        let guard = c.cmp(CmpOp::Ult, i, len);
        // i < len  ⟹  i < len + 1
        let one = c.int(64, 1);
        let lenp1 = c.bin(BvOp::Add, len, one);
        let goal = c.cmp(CmpOp::Ult, i, lenp1);
        assert!(prove_implies(&c, &[guard], goal));
    }

    #[test]
    fn does_not_prove_unsound_bound() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let len = c.symbol("len", 64);
        let guard = c.cmp(CmpOp::Ult, i, len);
        // i < len does NOT imply i < len - 1
        let one = c.int(64, 1);
        let lenm1 = c.bin(BvOp::Sub, len, one);
        let goal = c.cmp(CmpOp::Ult, i, lenm1);
        assert!(!prove_implies(&c, &[guard], goal));
    }

    #[test]
    fn trivial_constant_goal_is_proved() {
        let mut c = ExprCtx::new();
        let three = c.int(64, 3);
        let eight = c.int(64, 8);
        let goal = c.cmp(CmpOp::Ult, three, eight); // folds to true
        assert!(prove_implies(&c, &[], goal));
    }

    #[test]
    fn unprovable_without_assumptions() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let eight = c.int(64, 8);
        let goal = c.cmp(CmpOp::Ult, i, eight);
        // Nothing constrains i, so i < 8 cannot be proved.
        assert!(!prove_implies(&c, &[], goal));
    }

    #[test]
    fn skips_unparseable_assumption_instead_of_bailing() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let len = c.symbol("len", 64);
        let zero = c.int(64, 0);
        // A `≠` guard the fragment cannot read, alongside a usable `<` guard.
        let ne = c.cmp(CmpOp::Ne, len, zero);
        let guard = c.cmp(CmpOp::Ult, i, len);
        let goal = c.cmp(CmpOp::Ult, i, len);
        // The `≠` assumption is skipped, not fatal: the goal still proves from
        // the usable guard (exactly what an `s[len - 1]` access needs, whose
        // sibling `len != 0` guard the fragment cannot use).
        assert!(prove_implies(&c, &[ne, guard], goal));
        // The skip stays sound — an unsupported assumption cannot make an unsound
        // goal provable.
        let one = c.int(64, 1);
        let lenm1 = c.bin(BvOp::Sub, len, one);
        let unsound = c.cmp(CmpOp::Ult, i, lenm1); // i < len-1 (not implied)
        assert!(!prove_implies(&c, &[ne, guard], unsound));
    }
}
