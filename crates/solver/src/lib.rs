//! # csolver-solver — constraint IR, simplification, and the decision engine
//!
//! A small bit-vector constraint language ([`Term`] / [`Formula`]) plus the
//! **self-contained** decision engine: a constant-folding simplifier, the CDCL SAT
//! core ([`sat`]) with a bit-blaster ([`bitblast`], all arithmetic incl. div/rem and
//! symbolic shifts), the bit-precise front door ([`bitprecise`]), and a linear
//! fallback ([`linear`]). Every proof obligation is decided here in pure Rust — there
//! is no external SMT backend (a deliberate zero-dependency choice).

pub mod bitblast;
pub mod bitprecise;
pub mod expr;
pub mod linear;
pub mod sat;

pub use expr::{BvOp, CmpOp, ExprCtx, ExprId, Node};
pub use linear::prove_implies;

/// How an implication was discharged — which determines the assumptions a
/// resulting `PASS` carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofMethod {
    /// Decided exactly, at the bit level ([`bitprecise`]). Carries **no**
    /// arithmetic-overflow assumption: the implication holds for all machine
    /// values.
    BitPrecise,
    /// Decided in the linear-integer fragment ([`linear`]). Sound only under the
    /// `linear-no-overflow` assumption (quantities in `[0, isize::MAX]`); the
    /// caller must record that assumption.
    Linear,
}

/// SAT decision budget for the *refinement* attempt (after the linear procedure
/// already succeeded, to see whether the assumption can be dropped). Deliberately
/// **small**, because it runs on every linear success: the refinement is only a
/// nicety (it drops the already-recorded `linear-no-overflow` assumption when
/// cheap), and a *successful* bit-precise proof of a 64-bit bound (e.g. the
/// unit-stride `i + 1 ≤ len` of a `&[u8]` access, which is genuinely valid and so
/// makes the SAT solver grind out an `Unsat`) can be expensive. A tight budget
/// keeps such goals on the fast linear path (still sound, under the assumption)
/// instead of spending seconds upgrading them; the *fallback* below stays
/// generous for goals linear cannot prove at all.
///
/// SOUNDNESS NOTE — this constant is a **precision/performance dial, never a
/// correctness one**, so it may be tuned freely without re-auditing soundness.
/// A smaller budget only makes the refinement give up sooner, leaving the goal on
/// the linear path *with* its recorded `linear-no-overflow` assumption — a weaker,
/// still-sound result (a more honest verdict, never a false `PASS`). A larger
/// budget only drops that assumption on more goals (more precise, slower). It was
/// cut 40_000 → 3_000 to fix a 250× slowdown on unit-stride `&[u8]` loops; do not
/// raise it back without measuring that case (see `docs/PROVABILITY.md`).
const REFINE_BUDGET: u64 = 3_000;

/// SAT decision budget for the *fallback* attempt (when the linear procedure
/// failed and bit-precise reasoning is the only hope). More generous, but still
/// bounded.
const FALLBACK_BUDGET: u64 = 200_000;

/// Try to prove `assumptions ⟹ goal`, returning which [`ProofMethod`] succeeded
/// (or `None`, treated by the caller as `UNKNOWN`).
///
/// The strategy keeps the common path fast while still minimizing assumptions:
///
/// 1. **Linear first** — cheap, and it discharges the bulk of memory-safety
///    goals (soundly, under `linear-no-overflow`).
/// 2. If linear succeeds, a tight-budget **bit-precise refinement** retries the
///    same goal exactly. If that also succeeds, the goal needed no overflow
///    assumption, so it is reported as [`ProofMethod::BitPrecise`]; otherwise it
///    stays [`ProofMethod::Linear`]. (A goal that genuinely relies on
///    non-wrapping arithmetic — e.g. `i * stride` not overflowing — naturally
///    fails the bit-precise retry and keeps the assumption, which is correct.)
/// 3. If linear fails, a **bit-precise fallback** can still prove goals the
///    linear fragment cannot model (exact wrap-around, bitwise masks).
///
/// Both bit-precise attempts are bounded by a SAT decision budget *and* a CNF
/// size cap, so this never blows up the analysis time.
pub fn prove_implies_method(
    ctx: &ExprCtx,
    assumptions: &[ExprId],
    goal: ExprId,
) -> Option<ProofMethod> {
    if linear::prove_implies(ctx, assumptions, goal) {
        if bitprecise::prove_implies_budget(ctx, assumptions, goal, REFINE_BUDGET) {
            return Some(ProofMethod::BitPrecise);
        }
        return Some(ProofMethod::Linear);
    }
    if bitprecise::prove_implies_budget(ctx, assumptions, goal, FALLBACK_BUDGET) {
        return Some(ProofMethod::BitPrecise);
    }
    None
}

use csolver_core::BitVector;

/// A bit-vector term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// A constant.
    Const(BitVector),
    /// A symbolic variable of the given width.
    Var {
        /// Variable name.
        name: String,
        /// Bit width.
        width: u32,
    },
    /// Wrapping addition.
    Add(Box<Term>, Box<Term>),
    /// Wrapping subtraction.
    Sub(Box<Term>, Box<Term>),
    /// Wrapping multiplication.
    Mul(Box<Term>, Box<Term>),
}

impl Term {
    /// The bit width of this term.
    pub fn width(&self) -> u32 {
        match self {
            Term::Const(bv) => bv.width(),
            Term::Var { width, .. } => *width,
            Term::Add(a, _) | Term::Sub(a, _) | Term::Mul(a, _) => a.width(),
        }
    }

    /// The constant value, if this term is a literal.
    pub fn as_const(&self) -> Option<BitVector> {
        match self {
            Term::Const(bv) => Some(*bv),
            _ => None,
        }
    }
}

/// A boolean constraint over [`Term`]s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    /// A boolean literal.
    Bool(bool),
    /// Unsigned less-than.
    Ult(Term, Term),
    /// Unsigned less-or-equal.
    Ule(Term, Term),
    /// Equality.
    Eq(Term, Term),
    /// Conjunction.
    And(Vec<Formula>),
    /// Disjunction.
    Or(Vec<Formula>),
    /// Negation.
    Not(Box<Formula>),
}

/// Constant-fold a term: collapse operations over literals to a literal.
pub fn simplify_term(t: &Term) -> Term {
    match t {
        Term::Const(_) | Term::Var { .. } => t.clone(),
        Term::Add(a, b) => fold(a, b, |x, y| x.wrapping_add(y), Term::Add),
        Term::Sub(a, b) => fold(a, b, |x, y| x.wrapping_sub(y), Term::Sub),
        Term::Mul(a, b) => fold(
            a,
            b,
            |x, y| BitVector::new(x.width(), x.unsigned().wrapping_mul(y.unsigned())),
            Term::Mul,
        ),
    }
}

fn fold(
    a: &Term,
    b: &Term,
    op: impl Fn(BitVector, BitVector) -> BitVector,
    rebuild: impl Fn(Box<Term>, Box<Term>) -> Term,
) -> Term {
    let a = simplify_term(a);
    let b = simplify_term(b);
    match (a.as_const(), b.as_const()) {
        (Some(x), Some(y)) if x.width() == y.width() => Term::Const(op(x, y)),
        _ => rebuild(Box::new(a), Box::new(b)),
    }
}

/// Simplify a formula: fold constant comparisons and flatten trivial
/// connectives. The result is logically equivalent to the input.
pub fn simplify(f: &Formula) -> Formula {
    match f {
        Formula::Bool(_) => f.clone(),
        Formula::Ult(a, b) => cmp(a, b, |x, y| x.unsigned() < y.unsigned(), Formula::Ult),
        Formula::Ule(a, b) => cmp(a, b, |x, y| x.unsigned() <= y.unsigned(), Formula::Ule),
        Formula::Eq(a, b) => cmp(a, b, |x, y| x == y, Formula::Eq),
        Formula::And(cs) => {
            let mut out = Vec::new();
            for c in cs {
                match simplify(c) {
                    Formula::Bool(true) => {}
                    Formula::Bool(false) => return Formula::Bool(false),
                    other => out.push(other),
                }
            }
            match out.len() {
                0 => Formula::Bool(true),
                1 => out.swap_remove(0),
                _ => Formula::And(out),
            }
        }
        Formula::Or(cs) => {
            let mut out = Vec::new();
            for c in cs {
                match simplify(c) {
                    Formula::Bool(false) => {}
                    Formula::Bool(true) => return Formula::Bool(true),
                    other => out.push(other),
                }
            }
            match out.len() {
                0 => Formula::Bool(false),
                1 => out.swap_remove(0),
                _ => Formula::Or(out),
            }
        }
        Formula::Not(c) => match simplify(c) {
            Formula::Bool(b) => Formula::Bool(!b),
            other => Formula::Not(Box::new(other)),
        },
    }
}

fn cmp(
    a: &Term,
    b: &Term,
    rel: impl Fn(BitVector, BitVector) -> bool,
    rebuild: impl Fn(Term, Term) -> Formula,
) -> Formula {
    let a = simplify_term(a);
    let b = simplify_term(b);
    match (a.as_const(), b.as_const()) {
        (Some(x), Some(y)) if x.width() == y.width() => Formula::Bool(rel(x, y)),
        _ => rebuild(a, b),
    }
}

#[cfg(test)]
mod method_tests {
    use super::*;
    use expr::{BvOp, CmpOp};

    #[test]
    fn bitwise_mask_is_proved_only_bit_precisely() {
        // `x & 7 <=u 7` holds for all x, but the linear procedure abstracts `&`
        // as opaque and cannot prove it; the bit-precise backend decides it.
        let mut c = ExprCtx::new();
        let x = c.symbol("x", 32);
        let seven = c.int(32, 7);
        let masked = c.bin(BvOp::And, x, seven);
        let goal = c.cmp(CmpOp::Ule, masked, seven);

        assert!(!linear::prove_implies(&c, &[], goal), "linear cannot bound `&`");
        assert!(bitprecise::prove_implies(&c, &[], goal), "bit-precise can");
        assert_eq!(prove_implies_method(&c, &[], goal), Some(ProofMethod::BitPrecise));
    }

    #[test]
    fn guarded_index_is_bit_precise_so_drops_the_assumption() {
        // {0 <=u i, i <u len} ⟹ i <u len — decided exactly, so reported as
        // BitPrecise (no `linear-no-overflow` needed).
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let len = c.symbol("len", 64);
        let zero = c.int(64, 0);
        let nonneg = c.cmp(CmpOp::Ule, zero, i);
        let guard = c.cmp(CmpOp::Ult, i, len);
        let goal = c.cmp(CmpOp::Ult, i, len);
        assert_eq!(
            prove_implies_method(&c, &[nonneg, guard], goal),
            Some(ProofMethod::BitPrecise)
        );
    }

    #[test]
    fn non_wrapping_scaling_falls_back_to_linear() {
        // From `0 <=s i` alone, `0 <=s i*4` needs the no-overflow assumption
        // (i*4 wraps for large i), so bit-precise correctly fails and the proof
        // falls back to the linear method.
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let zero = c.int(64, 0);
        let four = c.int(64, 4);
        let nonneg = c.cmp(CmpOp::Sle, zero, i);
        let scaled = c.bin(BvOp::Mul, i, four);
        let goal = c.cmp(CmpOp::Sle, zero, scaled);
        assert_eq!(
            prove_implies_method(&c, &[nonneg], goal),
            Some(ProofMethod::Linear)
        );
    }

    #[test]
    fn unprovable_goal_is_none() {
        let mut c = ExprCtx::new();
        let i = c.symbol("i", 64);
        let eight = c.int(64, 8);
        let goal = c.cmp(CmpOp::Ult, i, eight);
        assert_eq!(prove_implies_method(&c, &[], goal), None);
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used)]
    use super::*;

    fn c(v: u128) -> Term {
        Term::Const(BitVector::new(64, v))
    }

    #[test]
    fn folds_constant_arithmetic() {
        // (2 + 3) * 4 = 20
        let t = Term::Mul(
            Box::new(Term::Add(Box::new(c(2)), Box::new(c(3)))),
            Box::new(c(4)),
        );
        assert_eq!(simplify_term(&t), c(20));
    }

    #[test]
    fn keeps_symbolic_terms() {
        let t = Term::Add(
            Box::new(Term::Var {
                name: "x".into(),
                width: 64,
            }),
            Box::new(c(1)),
        );
        // Cannot fold; stays symbolic.
        assert!(matches!(simplify_term(&t), Term::Add(_, _)));
    }

    #[test]
    fn folds_constant_comparison() {
        assert_eq!(simplify(&Formula::Ult(c(3), c(4))), Formula::Bool(true));
        assert_eq!(simplify(&Formula::Ult(c(4), c(4))), Formula::Bool(false));
        assert_eq!(simplify(&Formula::Eq(c(7), c(7))), Formula::Bool(true));
    }

    #[test]
    fn flattens_connectives() {
        let f = Formula::And(vec![
            Formula::Bool(true),
            Formula::Ult(c(1), c(2)), // true
            Formula::Ule(
                Term::Var {
                    name: "y".into(),
                    width: 64,
                },
                c(9),
            ),
        ]);
        // The two true conjuncts drop out, leaving the single symbolic one.
        assert!(matches!(simplify(&f), Formula::Ule(_, _)));

        let contradiction = Formula::And(vec![Formula::Bool(false), Formula::Eq(c(1), c(2))]);
        assert_eq!(simplify(&contradiction), Formula::Bool(false));
    }
}
