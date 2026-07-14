use super::*;

impl Explorer<'_> {
    pub(crate) fn install_sentinel_scan_bound(&mut self, header: BlockId, state: &mut PathState) {
        let Some(body) = self.loop_bodies.get(&header).cloned() else { return };
        let body_set: HashSet<BlockId> = body.iter().copied().collect();
        let Some(hdr) = self.f.block(header) else { return };

        // Definition of every register (for the increment / gep / cmp checks).
        let mut def: HashMap<RegId, &Inst> = HashMap::new();
        for b in &self.f.blocks {
            for inst in &b.insts {
                if let Some(d) = inst.defined_reg() {
                    def.insert(d, inst);
                }
            }
        }

        // 1. A counting induction `n`: a header parameter whose value is 0 on the
        //    entry edge and `n + 1` on the back-edge (unit stride, so it visits
        //    every element and cannot step over the sentinel).
        let preds: Vec<BlockId> = self
            .analysis
            .cfg()
            .predecessors(self.analysis.cfg().index_of(header).unwrap_or(usize::MAX))
            .iter()
            .map(|&p| self.analysis.cfg().block_id(p))
            .collect();
        for (pos, &(n, _)) in hdr.params.iter().enumerate() {
            let mut zero_entry = false;
            let mut unit_backedge = false;
            for &pred in &preds {
                let Some(args) = edge_args(self.f, pred, header) else { continue };
                let Some(arg) = args.get(pos) else { continue };
                if self.is_back_edge(pred, header) {
                    // back-edge arg must be `n + 1`.
                    if let Operand::Reg(m) = arg {
                        if let Some(Inst::Assign { value: RValue::Bin { op: BinOp::Add, lhs, rhs, .. }, .. }) =
                            def.get(&resolve_copy(*m, &def))
                        {
                            let one = |o: &Operand| matches!(o, Operand::Const(Const::Int(bv)) if bv.unsigned() == 1);
                            // The increment operand may be a copy of `n`.
                            let is_n = |o: &Operand| matches!(o, Operand::Reg(r) if resolve_copy(*r, &def) == n);
                            unit_backedge = (is_n(lhs) && one(rhs)) || (is_n(rhs) && one(lhs));
                        }
                    }
                } else if matches!(arg, Operand::Const(Const::Int(bv)) if bv.unsigned() == 0) {
                    zero_entry = true;
                }
            }
            if !(zero_entry && unit_backedge) {
                continue;
            }

            // 2. In the body, a load `v = base[n]` of an `E`-byte element, where
            //    `base` evaluates to a sentinel-terminated region of element `E`.
            for &bid in &body {
                let Some(blk) = self.f.block(bid) else { continue };
                for inst in &blk.insts {
                    let Inst::Load { dst: v, ty, ptr: Operand::Reg(q), .. } = inst else { continue };
                    let Some(Inst::PtrOffset { base: Operand::Reg(b), index: Operand::Reg(idx), elem, .. }) =
                        def.get(q)
                    else {
                        continue;
                    };
                    // mem2reg leaves the base/index as copies of the parameter and
                    // the induction (`%b = base`, `%i = n`); follow those chains,
                    // and at -O0 the index is a `sext`/`zext` of the counter.
                    if resolve_index(*idx, &def) != n {
                        continue;
                    }
                    let base_reg = resolve_copy(*b, &def);
                    let Some(e) = elem.size_bytes(&LAYOUT) else { continue };
                    if ty.size_bytes(&LAYOUT) != Some(e) {
                        continue;
                    }
                    // The base must be a live sentinel region of matching element.
                    let Some(SymValue::Ptr(bp)) = state.env.get(&base_reg) else { continue };
                    let Prov::Region(rid) = bp.prov else { continue };
                    let Some(region) = state.regions.get(rid) else { continue };
                    if region.sentinel != Some(e) {
                        continue;
                    }
                    // 3. The loaded value must gate the loop exit: a `v == 0` /
                    //    `v != 0` comparison feeding a branch that leaves the loop.
                    if !self.loaded_value_gates_exit(*v, &body_set, &def) {
                        continue;
                    }
                    // All side-conditions hold. The induction value `n` is what the
                    // access offset uses — directly at -O1, and at -O0 through a
                    // `sext`/`zext` the executor models as a width-preserving no-op
                    // on the same expression (so `base[sext(n)]` reuses `n`'s value).
                    // Install `0 <= n` and `(n + 1)·E ≤ size`, so the access
                    // `base[n]` (offset `n·E`, span `E`) is in bounds.
                    let size = region.size;
                    let Some(&SymValue::Scalar(n_e)) = state.env.get(&n) else { continue };
                    if self.ctx.width(n_e) != PTR_WIDTH {
                        continue;
                    }
                    let zero = self.ctx.int(PTR_WIDTH, 0);
                    let nonneg = self.ctx.cmp(SCmp::Sle, zero, n_e);
                    let one = self.ctx.int(PTR_WIDTH, 1);
                    let np1 = self.ctx.bin(BvOp::Add, n_e, one);
                    let e_e = self.ctx.int(PTR_WIDTH, e as u128);
                    let bytes = self.ctx.bin(BvOp::Mul, np1, e_e);
                    let fact = self.ctx.cmp(SCmp::Sle, bytes, size);
                    state.facts.push(nonneg);
                    state.facts.push(fact);
                    return;
                }
            }
        }
    }

    /// Whether `v` (a loaded value) feeds a comparison to zero that governs a
    /// branch leaving the loop body — the sentinel test of a scan.
    pub(crate) fn loaded_value_gates_exit(
        &self,
        v: RegId,
        body: &HashSet<BlockId>,
        def: &HashMap<RegId, &Inst>,
    ) -> bool {
        // Registers equal to `v`'s zero-test: `icmp eq/ne v, 0`.
        let mut tests: HashSet<RegId> = HashSet::new();
        for (d, inst) in def {
            if let Inst::Assign { value: RValue::Cmp { op: CmpOp::Eq | CmpOp::Ne, lhs, rhs }, .. } = inst {
                let is_v = |o: &Operand| matches!(o, Operand::Reg(r) if *r == v);
                let is_zero = |o: &Operand| matches!(o, Operand::Const(Const::Int(bv)) if bv.unsigned() == 0);
                if (is_v(lhs) && is_zero(rhs)) || (is_v(rhs) && is_zero(lhs)) {
                    tests.insert(*d);
                }
            }
        }
        if tests.is_empty() {
            return false;
        }
        // A `CondBr` on such a test with a target outside the loop = the exit.
        for &bid in body {
            let Some(blk) = self.f.block(bid) else { continue };
            if let Terminator::CondBr { cond: Operand::Reg(c), then_blk, else_blk, .. } = &blk.term {
                if tests.contains(c) && (!body.contains(then_blk) || !body.contains(else_blk)) {
                    return true;
                }
            }
        }
        false
    }

    /// Install the sound offset bound for a pointer equality-exit induction. The
    /// generic havoc made `iter` opaque; here — only after **proving** the
    /// side-conditions — we restore its region provenance with a fresh offset `o`
    /// constrained by `b0 ≤ o`, the congruence `o ≡ b0 (mod stride)`, and an upper
    /// bound that depends on the loop form:
    ///   - **header-test** (`bottom_test == false`): `o ≤ end_off`. The load is
    ///     guarded, so with the guard `iter != end` (`o != end_off`) the
    ///     congruence gives `o ≤ end_off − stride`, hence `o + stride ≤ end_off`.
    ///   - **bottom-test / rotated** (`bottom_test == true`): `o + stride ≤
    ///     end_off`. The load is unconditional, so this stronger invariant is
    ///     needed directly; its base case (`b0 + stride ≤ end_off`) is provable
    ///     only when the loop is entered non-empty — i.e. from the preheader
    ///     guard `base != end`, which sits in this header's path condition.
    ///
    /// The common side-conditions: `0 ≤ b0`, `end_off ≤ size ≤ isize::MAX`, and
    /// `stride | (end_off − b0)` (so `end` lies on the walk's grid — otherwise the
    /// pointer steps over `end`, never satisfies the `== end` exit, and the bound
    /// would be unsound). Only power-of-two strides (the element sizes that arise)
    /// get the exact bit-precise divisibility; others are skipped.
    pub(crate) fn assert_ptr_walk_bound(&mut self, state: &mut PathState, cap: PtrIndCapture) {
        let stride = cap.stride_bytes;
        if stride == 0 || !(stride as u128).is_power_of_two() {
            return;
        }
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let isize_max = self.ctx.int(PTR_WIDTH, i64::MAX as u128);
        let mask = self.ctx.int(PTR_WIDTH, (stride as u128) - 1);
        // `lo + d` is the largest accessed offset's lower witness: for the rotated
        // form the load happens at the unincremented pointer, so the invariant is
        // shifted by one stride (`d = stride`); the header-test form has `d = 0`.
        let plus_d = |s: &mut Self, e: ExprId| -> ExprId {
            if cap.bottom_test {
                let d = s.ctx.int(PTR_WIDTH, stride as u128);
                s.ctx.bin(BvOp::Add, e, d)
            } else {
                e
            }
        };
        // (end_off − b0) & mask == 0: end is on the walk's grid.
        let ediff = self.ctx.bin(BvOp::Sub, cap.end_off, cap.b0);
        let emask = self.ctx.bin(BvOp::And, ediff, mask);
        let end_on_grid = self.ctx.cmp(SCmp::Eq, emask, zero);
        let b0_upper = plus_d(self, cap.b0);
        let gate = [
            self.ctx.cmp(SCmp::Sle, zero, cap.b0),           // 0 ≤ b0
            self.ctx.cmp(SCmp::Sle, b0_upper, cap.end_off),  // b0 (+ stride) ≤ end_off
            self.ctx.cmp(SCmp::Sle, cap.end_off, cap.size),  // end_off ≤ size
            self.ctx.cmp(SCmp::Sle, cap.size, isize_max),    // size ≤ isize::MAX
            end_on_grid,
        ];
        // The region's no-wrap premise (`size = count·stride ≤ isize::MAX`) lets
        // `size ≤ isize::MAX` be proved for a *symbolic* slice length, and the
        // preheader guard (already in `pathcond`) is what makes the rotated form's
        // `b0 + stride ≤ end_off` provable. Both are read from the current state.
        let nowrap = state.regions.get(cap.region).and_then(|r| r.size_nowrap);
        let restore = state.facts.len();
        if let Some(nw) = nowrap {
            state.facts.push(nw);
        }
        let proved = gate.into_iter().all(|g| self.prove(g, state));
        state.facts.truncate(restore);
        if !proved {
            return;
        }
        // Sound: a region pointer at a fresh, grid-aligned, in-range offset.
        let o = self.fresh_scalar(PTR_WIDTH);
        state.env.insert(
            cap.reg,
            SymValue::Ptr(SymPointer {
                prov: Prov::Region(cap.region),
                offset: o,
                align: gcd(cap.align, stride),
                borrow: None,
            }),
        );
        let o_upper = plus_d(self, o);
        let odiff = self.ctx.bin(BvOp::Sub, o, cap.b0);
        let omask = self.ctx.bin(BvOp::And, odiff, mask);
        let ediff2 = self.ctx.bin(BvOp::Sub, cap.end_off, cap.b0);
        let emask2 = self.ctx.bin(BvOp::And, ediff2, mask);
        let facts = [
            self.ctx.cmp(SCmp::Sle, zero, cap.b0),          // 0 ≤ b0
            self.ctx.cmp(SCmp::Sle, cap.b0, o),             // b0 ≤ o
            self.ctx.cmp(SCmp::Sle, zero, o_upper),         // 0 ≤ o (+ stride) (no wrap)
            self.ctx.cmp(SCmp::Sle, o_upper, cap.end_off),  // o (+ stride) ≤ end_off
            self.ctx.cmp(SCmp::Sle, o_upper, cap.size),     // o (+ stride) ≤ size
            self.ctx.cmp(SCmp::Sle, cap.end_off, cap.size), // end_off ≤ size
            self.ctx.cmp(SCmp::Sle, cap.size, isize_max),   // size ≤ isize::MAX (no wrap)
            self.ctx.cmp(SCmp::Eq, omask, zero),            // o ≡ b0 (mod stride)
            self.ctx.cmp(SCmp::Eq, emask2, zero),           // end_off ≡ b0 (mod stride)
        ];
        state.facts.extend(facts);
    }

    /// Assert the sound bound `start ≤ v ≤ bound` for an equality-exit induction
    /// variable, but only after **proving** the side-conditions that make it a
    /// true loop invariant: `0 ≤ start ≤ bound ≤ isize::MAX` (the counter starts
    /// in range and the bound does not wrap), and `stride | (bound − start)` so
    /// `bound` lies on the grid `{start + k·stride}` — otherwise `v` steps *over*
    /// `bound`, never satisfies the `v == bound` exit, and could exceed `bound`
    /// (making the bound unsound). If any condition is not proved, nothing is
    /// asserted (sound fallback). The divisibility check is exact only for
    /// power-of-two strides (the element sizes that arise); other strides are
    /// skipped.
    pub(crate) fn assert_eq_exit_bound(
        &mut self,
        state: &mut PathState,
        v: ExprId,
        start: ExprId,
        bound: ExprId,
        stride: i128,
    ) {
        if stride <= 0 {
            return;
        }
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let isize_max = self.ctx.int(PTR_WIDTH, i64::MAX as u128);
        let mut gate = vec![
            self.ctx.cmp(SCmp::Sle, zero, start),     // 0 ≤ start
            self.ctx.cmp(SCmp::Sle, start, bound),    // start ≤ bound
            self.ctx.cmp(SCmp::Sle, bound, isize_max), // bound ≤ isize::MAX
        ];
        if stride > 1 {
            if !(stride as u128).is_power_of_two() {
                return; // non-power-of-two stride: divisibility not encodable exactly
            }
            // (bound − start) & (stride − 1) == 0  ⟺  stride | (bound − start).
            let mask = self.ctx.int(PTR_WIDTH, (stride as u128) - 1);
            let diff = self.ctx.bin(BvOp::Sub, bound, start);
            let masked = self.ctx.bin(BvOp::And, diff, mask);
            gate.push(self.ctx.cmp(SCmp::Eq, masked, zero));
        }
        if !gate.into_iter().all(|g| self.prove(g, state)) {
            return;
        }
        let f_lo = self.ctx.cmp(SCmp::Sle, start, v);
        let f_hi = self.ctx.cmp(SCmp::Sle, v, bound);
        state.facts.push(f_lo);
        state.facts.push(f_hi);
    }
}
