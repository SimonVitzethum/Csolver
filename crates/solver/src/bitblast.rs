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
//! Supported: constants, symbols, `Add`/`Sub`/`Mul`, `UDiv`/`SDiv`/`URem`/`SRem`
//! (restoring long division, SMT-LIB-total on a zero divisor), bitwise `And`/`Or`/`Xor`,
//! `Shl`/`LShr`/`AShr` with a **constant or symbolic** amount (a barrel shifter for the
//! latter), all comparisons, `Not`/`And`/`Or`/`Ite`. Only a width above [`MAX_WIDTH`]
//! makes [`Blaster::encode_bool`] return `None`, so the caller soundly falls back (it
//! never mis-encodes into a wrong answer).

use crate::expr::{BvOp, CmpOp, ExprCtx, ExprId, Node};
use crate::sat::Lit;
use csolver_core::FxHashMap;

/// The widest bit-vector we bit-blast. Covers `i1`..`i128` — the full concrete domain
/// ([`csolver_core::BitVector`] holds up to 128 bits, and the frontends clamp there), so
/// a `mul`/`udiv`/shift on an `i128`/`u128` is decided bit-precisely instead of falling back
/// to the linear abstraction. The cap keeps every query bounded (a 128-bit multiplier/divider
/// is ~4× the 64-bit gate count — still small); a wider width degrades soundly to linear.
pub const MAX_WIDTH: u32 = 128;

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

    /// Two's-complement negation `-a` = `¬a + 1`.
    fn negate(&mut self, a: &[Lit]) -> Vec<Lit> {
        let na: Vec<Lit> = a.iter().map(|l| l.negated()).collect();
        let zeros = vec![self.lit_false(); a.len()];
        let cin = self.lit_true();
        self.adder(&na, &zeros, cin).0
    }

    /// The magnitude `|a|` and sign bit of a two's-complement value: `(sign ? -a : a, sign)`.
    /// Note `|INT_MIN|` is `INT_MIN` as an unsigned pattern (`2^(w-1)`) — the same wraparound
    /// SMT-LIB `bvsdiv`/`bvsrem` use, so the `INT_MIN / -1` edge case comes out consistently.
    fn abs_sign(&mut self, a: &[Lit]) -> (Vec<Lit>, Lit) {
        let w = a.len();
        let sign = a[w - 1];
        let nega = self.negate(a);
        let mag = (0..w).map(|i| self.mux(sign, nega[i], a[i])).collect();
        (mag, sign)
    }

    /// **Unsigned** division, restoring long division: returns `(quotient, remainder)`, both
    /// width `w` (LSB-first). The partial remainder is kept in `w+1` bits (headroom for the
    /// shift-in before the trial subtraction); its top bit is provably 0 after each step (the
    /// reduced remainder is `< divisor ≤ 2^w-1`), so the low `w` bits carry it forward. The
    /// **divide-by-zero** valuation is SMT-LIB-total: `bvudiv a 0 = ~0` (every trial subtracts
    /// 0 → all quotient bits set) and `bvurem a 0 = a` (nothing is ever reduced → the shifted-in
    /// dividend remains) — so no term is left under-constrained even without a guard, and the
    /// IR's `NoDivByZero` obligation independently flags the UB.
    fn udivrem(&mut self, a: &[Lit], b: &[Lit]) -> (Vec<Lit>, Vec<Lit>) {
        let w = a.len();
        let zero = self.lit_false();
        let mut rem = vec![zero; w]; // partial remainder, always < b (fits w bits)
        let mut quot = vec![zero; w];
        let mut bext = b.to_vec(); // divisor zero-extended to w+1 bits
        bext.push(zero);
        for i in (0..w).rev() {
            // shifted = (rem << 1) | a[i]  — w+1 bits, LSB = the next dividend bit.
            let mut shifted = Vec::with_capacity(w + 1);
            shifted.push(a[i]);
            shifted.extend_from_slice(&rem);
            // carry == 1  ⇔  shifted ≥u bext  ⇔  subtract and set this quotient bit.
            let (diff, carry) = self.sub_with_borrow(&shifted, &bext);
            quot[i] = carry;
            let newrem: Vec<Lit> = (0..=w).map(|k| self.mux(carry, diff[k], shifted[k])).collect();
            rem = newrem[..w].to_vec(); // newrem[w] is provably 0
        }
        (quot, rem)
    }

    /// **Signed** division/remainder (LLVM/SMT rounding toward zero): divide the magnitudes,
    /// then fix signs — quotient sign is `sign_a ⊕ sign_b`, remainder sign follows the
    /// **dividend** (`a = (a/b)*b + (a%b)`).
    fn sdivrem(&mut self, a: &[Lit], b: &[Lit]) -> (Vec<Lit>, Vec<Lit>) {
        let w = a.len();
        let (ma, sa) = self.abs_sign(a);
        let (mb, sb) = self.abs_sign(b);
        let (uq, ur) = self.udivrem(&ma, &mb);
        let qsign = self.xor2(sa, sb);
        let neg_uq = self.negate(&uq);
        let quot = (0..w).map(|i| self.mux(qsign, neg_uq[i], uq[i])).collect();
        let neg_ur = self.negate(&ur);
        let rem = (0..w).map(|i| self.mux(sa, neg_ur[i], ur[i])).collect();
        (quot, rem)
    }

    /// A **symbolic-amount** shift (barrel shifter). `log2(w)` stages each conditionally shift
    /// by `2^k` when amount bit `b[k]` is set; bits shifted in are 0 (`Shl`/`LShr`) or the sign
    /// (`AShr`). An amount `≥ w` yields all-zero / all-sign — since every practical width is a
    /// power of two, `2^stages == w`, so the low `stages` bits address exactly `0..w-1` and the
    /// out-of-range case is precisely "some higher amount bit is set" (`b[stages..]`); a shift of
    /// *exactly* `w` also falls out of the barrel as all-fill, so both routes agree.
    fn shift_var(&mut self, op: BvOp, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
        let w = a.len();
        let zero = self.lit_false();
        let sign = a[w - 1];
        let fill = if matches!(op, BvOp::AShr) { sign } else { zero };
        let stages = if w <= 1 { 0 } else { (w - 1).ilog2() as usize + 1 };
        let mut x = a.to_vec();
        for (k, &ctrl) in b.iter().take(stages).enumerate() {
            let amt = 1usize << k;
            let shifted: Vec<Lit> = match op {
                BvOp::Shl => (0..w).map(|i| if i >= amt { x[i - amt] } else { zero }).collect(),
                BvOp::LShr | BvOp::AShr => {
                    (0..w).map(|i| if i + amt < w { x[i + amt] } else { fill }).collect()
                }
                _ => unreachable!("shift_var called with non-shift op"),
            };
            x = (0..w).map(|i| self.mux(ctrl, shifted[i], x[i])).collect();
        }
        // Amount ≥ w (any bit above the barrel range) forces the all-fill result.
        let oob = self.big_or(&b[stages.min(w)..]);
        (0..w).map(|i| self.mux(oob, fill, x[i])).collect()
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
