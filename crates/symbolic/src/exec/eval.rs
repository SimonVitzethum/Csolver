use super::*;

impl Explorer<'_> {
    pub(crate) fn eval_value(&mut self, op: &Operand, state: &PathState) -> SymValue {
        match op {
            Operand::Reg(r) => match state.env.get(r) {
                // A pointer into a region that a control-flow merge dropped keeps its old
                // region id, which now points past the end of this path's `regions`.
                // `merge_core` rewrites such pointers held in the environment, but one can
                // still reach a register via the heap/store list, a block argument, or a
                // summary return. Sanitize it to Unknown provenance on read, so every
                // downstream region access (bounds, liveness, dealloc, provenance) sees a
                // valid id or an opaque pointer — never an out-of-range index. Sound: an
                // unknown-provenance pointer is only ever treated conservatively.
                Some(SymValue::Ptr(p))
                    if matches!(p.prov, Prov::Region(rid) if rid >= state.regions.len()) =>
                {
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Unknown(POrigin::RegionDrop, None),
                        offset: p.offset,
                        align: p.align,
                        borrow: p.borrow,
                    })
                }
                Some(v) => v.clone(),
                None => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            },
            Operand::Const(Const::Int(bv)) => SymValue::Scalar(self.ctx.constant(*bv)),
            Operand::Const(Const::Null) => SymValue::Ptr(SymPointer {
                prov: Prov::Null,
                offset: self.ctx.int(PTR_WIDTH, 0),
                align: 1,
                borrow: None,
            }),
            Operand::Const(Const::Undef) => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            Operand::Const(Const::Symbol(name)) => match self.global_rids.get(name) {
                Some(&(rid, align)) => SymValue::Ptr(SymPointer {
                    prov: Prov::Region(rid),
                    offset: self.ctx.int(PTR_WIDTH, 0),
                    align,
                    borrow: None,
                }),
                // Not a known global (e.g. a function address): an opaque scalar.
                None => SymValue::Scalar(self.ctx.symbol(format!("@{name}"), PTR_WIDTH)),
            },
            Operand::Const(Const::SymbolOffset(name, off)) => {
                match self.global_rids.get(name) {
                    Some(&(rid, align)) => {
                        let offset = if *off >= 0 {
                            self.ctx.int(PTR_WIDTH, *off as u128)
                        } else {
                            let zero = self.ctx.int(PTR_WIDTH, 0);
                            let mag = self.ctx.int(PTR_WIDTH, (-*off) as u128);
                            self.ctx.bin(BvOp::Sub, zero, mag)
                        };
                        // The interior pointer's alignment is what offset+align
                        // imply, conservatively 1 unless the offset preserves it.
                        let a = if *off >= 0 && (*off as u64).is_multiple_of(align) {
                            align
                        } else {
                            1
                        };
                        SymValue::Ptr(SymPointer { prov: Prov::Region(rid), offset, align: a, borrow: None })
                    }
                    None => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
                }
            }
        }
    }

    pub(crate) fn eval_scalar(&mut self, op: &Operand, state: &PathState) -> ExprId {
        let v = self.eval_value(op, state);
        self.scalarize(v)
    }

    /// A symbolic value as a scalar expression: a null-provenance pointer is `0`; an
    /// **opaque pointer with a provenance id** gets a *stable* address symbol keyed by that
    /// id (not a fresh one), so its numeric address has a consistent identity across uses.
    /// This is what lets a `p != null` branch guard carry over to a later dereference: the
    /// guard and the deref scalarise the same opaque pointer to the *same* symbol, so the
    /// path condition `ptr#id != 0` proves `NoNullDeref` (see `check_access`). An idless
    /// opaque pointer stays a fresh unknown. Sound and strictly more precise: a stable symbol
    /// only adds equalities the guard genuinely established; `ptr#…` is not an `arg…` genuine
    /// input, so it never makes an over-approximated goal refutable.
    pub(crate) fn scalarize(&mut self, v: SymValue) -> ExprId {
        match v {
            SymValue::Scalar(e) => e,
            SymValue::Ptr(p) => match p.prov {
                Prov::Null => self.ctx.int(PTR_WIDTH, 0),
                Prov::Unknown(_, Some(id)) => self.ctx.symbol(format!("ptr#{id}"), PTR_WIDTH),
                _ => self.fresh_scalar(PTR_WIDTH),
            },
        }
    }

    /// Evaluate a comparison, treating two **same-allocation** pointer operands
    /// as a comparison of their offsets — so `iter != end` within one allocation
    /// becomes the offset relation the pointer-walk bounds reasoning needs.
    /// Pointers of differing or opaque provenance fall back to fresh scalars
    /// (sound: the result is simply unconstrained).
    pub(crate) fn eval_ptr_aware_cmp(
        &mut self,
        op: CmpOp,
        lhs: &Operand,
        rhs: &Operand,
        state: &PathState,
    ) -> ExprId {
        let lv = self.eval_value(lhs, state);
        let rv = self.eval_value(rhs, state);
        if let (SymValue::Ptr(pa), SymValue::Ptr(pb)) = (&lv, &rv) {
            if let (Prov::Region(ra), Prov::Region(rb)) = (&pa.prov, &pb.prov) {
                if ra == rb {
                    return self.ctx.cmp(map_cmpop(op), pa.offset, pb.offset);
                }
            }
        }
        let a = self.scalarize(lv);
        let b = self.scalarize(rv);
        self.ctx.cmp(map_cmpop(op), a, b)
    }

    pub(crate) fn eval_pointer(&mut self, op: &Operand, state: &PathState) -> SymPointer {
        match self.eval_value(op, state) {
            SymValue::Ptr(p) => p,
            SymValue::Scalar(_) => {
                let cause = match op {
                    Operand::Reg(r) => {
                        self.scalar_ptr_cause.get(r).copied().unwrap_or(ScalarPtrCause::Other)
                    }
                    _ => ScalarPtrCause::Other,
                };
                SymPointer {
                    prov: Prov::Unknown(POrigin::ScalarAsPtr(cause), None),
                    offset: self.ctx.int(PTR_WIDTH, 0),
                    align: 1,
                    borrow: None,
                }
            }
        }
    }

    /// Build the "does not overflow" goal for an `nsw`/`nuw`-flagged `add`/`sub`/`mul`
    /// on operands `a`, `b`. Returns `None` when the case is not modelled (signed
    /// multiply — no sign-extend primitive — so it is soundly left unchecked). When
    /// both flags are set the goal is the conjunction of the signed and unsigned
    /// conditions.
    pub(crate) fn arith_no_overflow(
        &mut self,
        op: BinOp,
        a: ExprId,
        b: ExprId,
        flags: WrapFlags,
    ) -> Option<ExprId> {
        let w = self.ctx.width(a);
        let zero = self.ctx.int(w, 0);
        let mut goals: Vec<ExprId> = Vec::new();
        // The multiplication no-overflow goal builds a **double-width** (`2w`) product. For a
        // `w = 128` (`i128`/`u128`) operation — which passes the caller's `op_wide` gate, since
        // 128 ≤ `MAX_WIDTH` — `2w = 256` exceeds the bit-precise domain and constructing the
        // `sext`/`zext` to 256 bits would panic (`BitVector::new`). Skip only the mul goal in
        // that case (add/sub need no doubling): the operation stays UNKNOWN rather than crashing
        // the scan. Sound — a skipped goal is never a false PASS. Reached via wide-integer code
        // (crypto `u128` multiply) that whole-program reachability surfaces.
        let can_double = w * 2 <= csolver_solver::bitblast::MAX_WIDTH;
        if flags.nsw {
            // Signed: overflow iff the operand signs and the result sign disagree in
            // the characteristic way. sign(x) := x <s 0.
            let sa = self.ctx.cmp(SCmp::Slt, a, zero);
            let sb = self.ctx.cmp(SCmp::Slt, b, zero);
            match op {
                BinOp::Add => {
                    let s = self.ctx.bin(BvOp::Add, a, b);
                    let ss = self.ctx.cmp(SCmp::Slt, s, zero);
                    // overflow = (sa == sb) && (ss != sa)
                    let same = self.ctx.cmp(SCmp::Eq, sa, sb);
                    let s_eq_a = self.ctx.cmp(SCmp::Eq, ss, sa);
                    let diff = self.ctx.not(s_eq_a);
                    let ovf = self.ctx.and(vec![same, diff]);
                    goals.push(self.ctx.not(ovf));
                }
                BinOp::Sub => {
                    let s = self.ctx.bin(BvOp::Sub, a, b);
                    let ss = self.ctx.cmp(SCmp::Slt, s, zero);
                    // overflow = (sa != sb) && (ss != sa)
                    let same_ab = self.ctx.cmp(SCmp::Eq, sa, sb);
                    let diff_ab = self.ctx.not(same_ab);
                    let s_eq_a = self.ctx.cmp(SCmp::Eq, ss, sa);
                    let diff_s = self.ctx.not(s_eq_a);
                    let ovf = self.ctx.and(vec![diff_ab, diff_s]);
                    goals.push(self.ctx.not(ovf));
                }
                BinOp::Mul if can_double => {
                    // no overflow = sext(a*b, 2w) == sext(a,2w) * sext(b,2w): the w-bit
                    // signed product, sign-extended, equals the exact double-width product.
                    let pw = self.ctx.bin(BvOp::Mul, a, b);
                    let pw2 = self.ctx.sext(pw, w * 2);
                    let sa2 = self.ctx.sext(a, w * 2);
                    let sb2 = self.ctx.sext(b, w * 2);
                    let full = self.ctx.bin(BvOp::Mul, sa2, sb2);
                    goals.push(self.ctx.cmp(SCmp::Eq, pw2, full));
                }
                _ => {}
            }
        }
        if flags.nuw {
            match op {
                BinOp::Add => {
                    // no overflow = (a + b) >=u a
                    let s = self.ctx.bin(BvOp::Add, a, b);
                    goals.push(self.ctx.cmp(SCmp::Uge, s, a));
                }
                BinOp::Sub => {
                    // no borrow = a >=u b
                    goals.push(self.ctx.cmp(SCmp::Uge, a, b));
                }
                BinOp::Mul if can_double => {
                    // no overflow = zext(a*b, 2w) == zext(a,2w) * zext(b,2w)
                    let pw = self.ctx.bin(BvOp::Mul, a, b);
                    let pw2 = self.ctx.zext(pw, w * 2);
                    let za = self.ctx.zext(a, w * 2);
                    let zb = self.ctx.zext(b, w * 2);
                    let full = self.ctx.bin(BvOp::Mul, za, zb);
                    goals.push(self.ctx.cmp(SCmp::Eq, pw2, full));
                }
                _ => {}
            }
        }
        match goals.len() {
            0 => None,
            1 => Some(goals[0]),
            _ => Some(self.ctx.and(goals)),
        }
    }

    pub(crate) fn eval_rvalue(&mut self, rv: &RValue, state: &PathState) -> SymValue {
        match rv {
            RValue::Use(op) => self.eval_value(op, state),
            RValue::Bin { op, lhs, rhs, .. } => {
                let a = self.eval_scalar(lhs, state);
                let b = self.eval_scalar(rhs, state);
                SymValue::Scalar(self.ctx.bin(map_binop(*op), a, b))
            }
            RValue::Cmp { op, lhs, rhs } => {
                SymValue::Scalar(self.eval_ptr_aware_cmp(*op, lhs, rhs, state))
            }
            RValue::Cast { op, operand, .. } => match op {
                CastOp::Bitcast => self.eval_value(operand, state),
                CastOp::IntToPtr => SymValue::Ptr(SymPointer {
                    prov: Prov::Unknown(POrigin::IntToPtr, None),
                    offset: self.ctx.int(PTR_WIDTH, 0),
                    align: 1,
                    borrow: None,
                }),
                CastOp::ZExt | CastOp::SExt => match self.eval_value(operand, state) {
                    SymValue::Scalar(e) => SymValue::Scalar(e),
                    SymValue::Ptr(_) => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
                },
                CastOp::Trunc | CastOp::PtrToInt => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            },
            RValue::Select { cond, then_val, else_val } => {
                let d = self.eval_scalar(cond, state);
                let a = self.eval_value(then_val, state);
                let b = self.eval_value(else_val, state);
                let ty = Type::ptr(Type::Unit); // a hint; `select` builds Prov::Select for ptrs, ite for scalars
                self.select(d, a, b, &ty)
            }
        }
    }

    pub(crate) fn eval_condition(&mut self, cond: &Condition, state: &PathState) -> ExprId {
        match cond {
            Condition::True => self.ctx.boolean(true),
            Condition::Cmp { op, lhs, rhs } => self.eval_ptr_aware_cmp(*op, lhs, rhs, state),
            Condition::And(cs) => {
                let parts = cs.iter().map(|c| self.eval_condition(c, state)).collect();
                self.ctx.and(parts)
            }
            Condition::Or(cs) => {
                let parts = cs.iter().map(|c| self.eval_condition(c, state)).collect();
                self.ctx.or(parts)
            }
            Condition::Not(c) => {
                let inner = self.eval_condition(c, state);
                self.ctx.not(inner)
            }
        }
    }
}
