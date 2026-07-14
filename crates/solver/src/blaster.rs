use super::*;

/// Lowers expressions of one [`ExprCtx`] into a shared [`Cnf`], memoizing by
/// [`ExprId`] so structural sharing in the expression graph carries over to the
/// circuit.
pub struct Blaster<'c> {
    ctx: &'c ExprCtx,
    /// The CNF being built.
    pub cnf: Cnf,
    memo: FxHashMap<ExprId, Vec<Lit>>,
    /// Each named symbol encountered, with its width and bit literals (LSB
    /// first) — so a SAT model can be read back into concrete symbol values.
    syms: Vec<(String, u32, Vec<Lit>)>,
}

impl<'c> Blaster<'c> {
    /// A blaster over the given expression context.
    pub fn new(ctx: &'c ExprCtx) -> Blaster<'c> {
        Blaster {
            ctx,
            cnf: Cnf::default(),
            memo: FxHashMap::default(),
            syms: Vec::new(),
        }
    }

    /// The symbols encoded so far: `(name, width, bit literals)`.
    pub fn symbols(&self) -> &[(String, u32, Vec<Lit>)] {
        &self.syms
    }

    /// The literals (LSB first) of a constant of the given width.
    fn const_bits(&mut self, value: u128, width: u32) -> Vec<Lit> {
        (0..width)
            .map(|i| {
                if (value >> i) & 1 == 1 {
                    self.cnf.lit_true()
                } else {
                    self.cnf.lit_false()
                }
            })
            .collect()
    }

    /// Encode a bit-vector (or boolean, as a 1-bit vector) expression to its
    /// literals, or `None` if it uses an unsupported construct/width.
    pub fn encode(&mut self, id: ExprId) -> Option<Vec<Lit>> {
        if let Some(bits) = self.memo.get(&id) {
            return Some(bits.clone());
        }
        let width = self.ctx.width(id);
        if width == 0 || width > MAX_WIDTH {
            return None;
        }
        // Clone the node so the immutable borrow of `ctx` ends before we mutate
        // `self.cnf`.
        let node = self.ctx.node(id).clone();
        let bits = match node {
            Node::Const(bv) => self.const_bits(bv.unsigned(), width),
            Node::Sym { name, .. } => {
                let bits: Vec<Lit> = (0..width).map(|_| self.cnf.new_var()).collect();
                self.syms.push((name, width, bits.clone()));
                bits
            }
            Node::Bool(b) => {
                let l = if b {
                    self.cnf.lit_true()
                } else {
                    self.cnf.lit_false()
                };
                vec![l]
            }
            Node::Bin { op, a, b } => {
                let av = self.encode(a)?;
                let bv = self.encode(b)?;
                if av.len() != bv.len() {
                    return None;
                }
                self.encode_bin(op, &av, &bv, b)?
            }
            Node::Cmp { op, a, b } => {
                let av = self.encode(a)?;
                let bv = self.encode(b)?;
                if av.len() != bv.len() {
                    return None;
                }
                vec![self.cnf.compare(op, &av, &bv)]
            }
            Node::Not(x) => {
                let xv = self.encode(x)?;
                if xv.len() != 1 {
                    return None;
                }
                vec![xv[0].negated()]
            }
            Node::And(xs) => {
                let mut lits = Vec::with_capacity(xs.len());
                for x in xs {
                    let xv = self.encode(x)?;
                    if xv.len() != 1 {
                        return None;
                    }
                    lits.push(xv[0]);
                }
                vec![self.cnf.big_and(&lits)]
            }
            Node::Or(xs) => {
                let mut lits = Vec::with_capacity(xs.len());
                for x in xs {
                    let xv = self.encode(x)?;
                    if xv.len() != 1 {
                        return None;
                    }
                    lits.push(xv[0]);
                }
                vec![self.cnf.big_or(&lits)]
            }
            Node::Ite { c, t, e } => {
                let cv = self.encode(c)?;
                if cv.len() != 1 {
                    return None;
                }
                let tv = self.encode(t)?;
                let ev = self.encode(e)?;
                if tv.len() != ev.len() {
                    return None;
                }
                tv.iter()
                    .zip(ev.iter())
                    .map(|(&t, &e)| self.cnf.mux(cv[0], t, e))
                    .collect()
            }
            Node::Zext(val) => {
                // Low bits are the operand's; high bits are zero (unsigned widen).
                let mut bits = self.encode(val)?;
                while (bits.len() as u32) < width {
                    bits.push(self.cnf.lit_false());
                }
                bits
            }
            Node::Sext(val) => {
                // Low bits are the operand's; high bits replicate its top (sign) bit.
                let bits = self.encode(val)?;
                let sign = *bits.last()?;
                let mut out = bits;
                while (out.len() as u32) < width {
                    out.push(sign);
                }
                out
            }
        };
        self.memo.insert(id, bits.clone());
        Some(bits)
    }

    /// Encode a binary op given the already-encoded operands. `b_id` is the
    /// right operand's expression id (needed to read a constant shift amount).
    fn encode_bin(
        &mut self,
        op: BvOp,
        a: &[Lit],
        b: &[Lit],
        b_id: ExprId,
    ) -> Option<Vec<Lit>> {
        let w = a.len();
        let bits = match op {
            BvOp::Add => self.cnf.add(a, b),
            BvOp::Sub => self.cnf.sub(a, b),
            BvOp::Mul => self.cnf.mul(a, b),
            BvOp::And | BvOp::Or | BvOp::Xor => self.cnf.bitwise(op, a, b),
            BvOp::Shl | BvOp::LShr | BvOp::AShr => {
                // A constant amount collapses to wiring (cheapest); a symbolic amount uses the
                // barrel shifter. Both are exact and width-clamped.
                match self.ctx.as_const(b_id) {
                    Some(k) => self.shift_const(op, a, k.unsigned(), w),
                    None => self.cnf.shift_var(op, a, b),
                }
            }
            BvOp::UDiv => self.cnf.udivrem(a, b).0,
            BvOp::URem => self.cnf.udivrem(a, b).1,
            BvOp::SDiv => self.cnf.sdivrem(a, b).0,
            BvOp::SRem => self.cnf.sdivrem(a, b).1,
        };
        Some(bits)
    }

    /// A shift by a constant amount.
    fn shift_const(&mut self, op: BvOp, a: &[Lit], k: u128, w: usize) -> Vec<Lit> {
        let zero = self.cnf.lit_false();
        // Clamp to the width first: any shift `≥ w` yields all-zero (Shl/LShr) or
        // all-sign (AShr), so `w` is a faithful stand-in — and it keeps `i + k`
        // from overflowing `usize` for a near-`u64::MAX` constant amount at w=64.
        let k = k.min(w as u128) as usize;
        match op {
            BvOp::Shl => (0..w)
                .map(|i| if i >= k { a[i - k] } else { zero })
                .collect(),
            BvOp::LShr => (0..w)
                .map(|i| if i + k < w { a[i + k] } else { zero })
                .collect(),
            BvOp::AShr => {
                let sign = a[w - 1];
                (0..w)
                    .map(|i| if i + k < w { a[i + k] } else { sign })
                    .collect()
            }
            _ => unreachable!("shift_const called with non-shift op"),
        }
    }

    /// Encode a boolean expression to a single literal, or `None` if it (or a
    /// sub-term) is outside the blastable fragment.
    pub fn encode_bool(&mut self, id: ExprId) -> Option<Lit> {
        let bits = self.encode(id)?;
        if bits.len() == 1 {
            Some(bits[0])
        } else {
            None
        }
    }
}
