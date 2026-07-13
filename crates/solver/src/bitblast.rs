//! Bit-blasting: lower a hash-consed [`ExprCtx`] expression to CNF over the
//! [`crate::sat`] solver, exactly preserving fixed-width (wrapping) bit-vector
//! semantics.
//!
//! Every bit-vector value of width `w` becomes `w` SAT literals (LSB first); the
//! operations are built from textbook gate-level circuits (ripple-carry
//! adder/subtractor, shift-add multiplier, borrow-chain comparators) wired up
//! with Tseitin clauses. Because the encoding is equisatisfiable and the
//! circuits implement modular two's-complement arithmetic — exactly Rust's
//! wrapping bit-vector semantics — a bit-precise `Unsat` is faithful to the real
//! program semantics, with **no** linear/no-overflow assumption.
//!
//! ## What is and isn't blasted
//!
//! Supported: constants, symbols, `Add`/`Sub`/`Mul`, bitwise `And`/`Or`/`Xor`,
//! constant-amount `Shl`/`LShr`/`AShr`, all comparisons, `Not`/`And`/`Or`/`Ite`.
//! Anything else — division/remainder, a *symbolic* shift amount, or a width
//! above [`MAX_WIDTH`] — makes [`Blaster::encode_bool`] return `None`, so the
//! caller soundly falls back (it never mis-encodes into a wrong answer).

use crate::expr::{BvOp, CmpOp, ExprCtx, ExprId, Node};
use crate::sat::Lit;
use csolver_core::FxHashMap;

/// The widest bit-vector we bit-blast. Memory-safety quantities are `i1`..`i64`;
/// capping keeps every query bounded.
pub const MAX_WIDTH: u32 = 64;

/// A CNF under construction, with Tseitin gate helpers.
#[derive(Default)]
pub struct Cnf {
    /// Number of SAT variables allocated.
    pub num_vars: usize,
    /// The accumulated clauses.
    pub clauses: Vec<Vec<Lit>>,
    /// A cached literal constrained to be always true.
    true_lit: Option<Lit>,
}

impl Cnf {
    /// A fresh SAT variable, returned as its positive literal.
    fn new_var(&mut self) -> Lit {
        let v = self.num_vars as u32;
        self.num_vars += 1;
        Lit::pos(v)
    }

    /// Add a clause.
    fn add_clause(&mut self, clause: Vec<Lit>) {
        self.clauses.push(clause);
    }

    /// A literal that is always true (and its negation, always false).
    fn lit_true(&mut self) -> Lit {
        if let Some(l) = self.true_lit {
            return l;
        }
        let l = self.new_var();
        self.add_clause(vec![l]);
        self.true_lit = Some(l);
        l
    }

    fn lit_false(&mut self) -> Lit {
        self.lit_true().negated()
    }

    /// Whether `l` is the cached always-true constant.
    fn is_true(&self, l: Lit) -> bool {
        self.true_lit == Some(l)
    }

    /// Whether `l` is the cached always-false constant.
    fn is_false(&self, l: Lit) -> bool {
        self.true_lit == Some(l.negated())
    }

    /// `o ↔ a ∧ b`, folding the constant cases (so e.g. multiplying by a
    /// constant collapses to shifts instead of emitting a full multiplier).
    fn and2(&mut self, a: Lit, b: Lit) -> Lit {
        if self.is_false(a) || self.is_false(b) {
            return self.lit_false();
        }
        if self.is_true(a) {
            return b;
        }
        if self.is_true(b) {
            return a;
        }
        if a == b {
            return a;
        }
        if a == b.negated() {
            return self.lit_false();
        }
        let o = self.new_var();
        self.add_clause(vec![a.negated(), b.negated(), o]);
        self.add_clause(vec![a, o.negated()]);
        self.add_clause(vec![b, o.negated()]);
        o
    }

    /// `o ↔ a ∨ b`, folding the constant cases.
    fn or2(&mut self, a: Lit, b: Lit) -> Lit {
        if self.is_true(a) || self.is_true(b) {
            return self.lit_true();
        }
        if self.is_false(a) {
            return b;
        }
        if self.is_false(b) {
            return a;
        }
        if a == b {
            return a;
        }
        if a == b.negated() {
            return self.lit_true();
        }
        let o = self.new_var();
        self.add_clause(vec![a, b, o.negated()]);
        self.add_clause(vec![a.negated(), o]);
        self.add_clause(vec![b.negated(), o]);
        o
    }

    /// `o ↔ a ⊕ b`, folding the constant cases.
    fn xor2(&mut self, a: Lit, b: Lit) -> Lit {
        if self.is_false(a) {
            return b;
        }
        if self.is_false(b) {
            return a;
        }
        if self.is_true(a) {
            return b.negated();
        }
        if self.is_true(b) {
            return a.negated();
        }
        if a == b {
            return self.lit_false();
        }
        if a == b.negated() {
            return self.lit_true();
        }
        let o = self.new_var();
        self.add_clause(vec![a.negated(), b.negated(), o.negated()]);
        self.add_clause(vec![a, b, o.negated()]);
        self.add_clause(vec![a, b.negated(), o]);
        self.add_clause(vec![a.negated(), b, o]);
        o
    }

    /// `o ↔ (s ? a : b)`, folding a constant selector or equal arms.
    fn mux(&mut self, s: Lit, a: Lit, b: Lit) -> Lit {
        if self.is_true(s) {
            return a;
        }
        if self.is_false(s) {
            return b;
        }
        if a == b {
            return a;
        }
        let t = self.and2(s, a);
        let e = self.and2(s.negated(), b);
        self.or2(t, e)
    }

    /// `o ↔ (a = b)`.
    fn iff(&mut self, a: Lit, b: Lit) -> Lit {
        self.xor2(a, b).negated()
    }

    /// Conjunction of many literals.
    fn big_and(&mut self, lits: &[Lit]) -> Lit {
        match lits.split_first() {
            None => self.lit_true(),
            Some((&first, rest)) => rest.iter().fold(first, |acc, &l| self.and2(acc, l)),
        }
    }

    /// Disjunction of many literals.
    fn big_or(&mut self, lits: &[Lit]) -> Lit {
        match lits.split_first() {
            None => self.lit_false(),
            Some((&first, rest)) => rest.iter().fold(first, |acc, &l| self.or2(acc, l)),
        }
    }

    // --- bit-vector circuits (operands are LSB-first literal vectors) --------

    /// One full adder: returns `(sum, carry_out)`.
    fn full_adder(&mut self, a: Lit, b: Lit, cin: Lit) -> (Lit, Lit) {
        let axb = self.xor2(a, b);
        let sum = self.xor2(axb, cin);
        let ab = self.and2(a, b);
        let cx = self.and2(cin, axb);
        let cout = self.or2(ab, cx);
        (sum, cout)
    }

    /// Ripple-carry add of two equal-width vectors with an incoming carry.
    /// Returns `(sum bits, carry_out)`; the sum is truncated to the width.
    fn adder(&mut self, a: &[Lit], b: &[Lit], cin: Lit) -> (Vec<Lit>, Lit) {
        debug_assert_eq!(a.len(), b.len());
        let mut carry = cin;
        let mut out = Vec::with_capacity(a.len());
        for i in 0..a.len() {
            let (s, c) = self.full_adder(a[i], b[i], carry);
            out.push(s);
            carry = c;
        }
        (out, carry)
    }

    /// `a + b` (wrapping).
    fn add(&mut self, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
        let cin = self.lit_false();
        self.adder(a, b, cin).0
    }

    /// `a - b` (wrapping), via `a + ¬b + 1`. Returns `(diff, carry_out)`, where
    /// `carry_out == 1` iff `a >=u b` (no borrow).
    fn sub_with_borrow(&mut self, a: &[Lit], b: &[Lit]) -> (Vec<Lit>, Lit) {
        let nb: Vec<Lit> = b.iter().map(|l| l.negated()).collect();
        let cin = self.lit_true();
        self.adder(a, &nb, cin)
    }

    fn sub(&mut self, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
        self.sub_with_borrow(a, b).0
    }

    /// Shift-add multiplier (`a * b`, wrapping to the operand width).
    fn mul(&mut self, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
        let w = a.len();
        let zero = self.lit_false();
        let mut acc = vec![zero; w];
        for (j, &bj) in b.iter().enumerate() {
            // Partial product: (a << j) masked by b[j].
            let mut pp = vec![zero; w];
            for i in j..w {
                pp[i] = self.and2(a[i - j], bj);
            }
            acc = self.add(&acc, &pp);
        }
        acc
    }

    /// `a & b`, `a | b`, `a ^ b` bitwise.
    fn bitwise(&mut self, op: BvOp, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
        a.iter()
            .zip(b.iter())
            .map(|(&x, &y)| match op {
                BvOp::And => self.and2(x, y),
                BvOp::Or => self.or2(x, y),
                BvOp::Xor => self.xor2(x, y),
                _ => unreachable!("bitwise called with non-bitwise op"),
            })
            .collect()
    }

    /// `a == b` over equal-width vectors.
    fn eq(&mut self, a: &[Lit], b: &[Lit]) -> Lit {
        let bits: Vec<Lit> = a
            .iter()
            .zip(b.iter())
            .map(|(&x, &y)| self.iff(x, y))
            .collect();
        self.big_and(&bits)
    }

    /// Unsigned `a < b` — false iff the subtraction `a - b` produces no borrow.
    fn ult(&mut self, a: &[Lit], b: &[Lit]) -> Lit {
        let (_, carry) = self.sub_with_borrow(a, b);
        carry.negated()
    }

    /// Signed `a < b`.
    fn slt(&mut self, a: &[Lit], b: &[Lit]) -> Lit {
        let w = a.len();
        let sa = a[w - 1];
        let sb = b[w - 1];
        let diff_sign = self.xor2(sa, sb);
        let unsigned_lt = self.ult(a, b);
        // signs differ ⇒ the negative one (sign bit 1) is smaller ⇒ result = sa.
        self.mux(diff_sign, sa, unsigned_lt)
    }

    /// A comparison predicate as a single literal.
    fn compare(&mut self, op: CmpOp, a: &[Lit], b: &[Lit]) -> Lit {
        match op {
            CmpOp::Eq => self.eq(a, b),
            CmpOp::Ne => self.eq(a, b).negated(),
            CmpOp::Ult => self.ult(a, b),
            CmpOp::Ule => self.ult(b, a).negated(), // a<=b  ⇔ ¬(b<a)
            CmpOp::Ugt => self.ult(b, a),
            CmpOp::Uge => self.ult(a, b).negated(),
            CmpOp::Slt => self.slt(a, b),
            CmpOp::Sle => self.slt(b, a).negated(),
            CmpOp::Sgt => self.slt(b, a),
            CmpOp::Sge => self.slt(a, b).negated(),
        }
    }
}

#[path = "blaster.rs"]
mod blaster;
pub use blaster::Blaster;

#[cfg(test)]
#[path = "bitblast_tests.rs"]
mod tests;
