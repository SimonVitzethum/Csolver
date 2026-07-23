use super::*;

impl Explorer<'_> {
    /// Replace a loop header's parameters with fresh symbols constrained by the
    /// interval invariant that holds at the header on every iteration.
    pub(crate) fn havoc_header(&mut self, header: BlockId, state: &mut PathState) {
        // Havocking introduces over-approximation, so this path is no longer
        // exact: it may stand for unreachable states, so we must not refute on it.
        state.exact = false;
        // The loop may have written arbitrary memory across iterations, so the
        // stored-value knowledge is no longer reliable: forget it (sound
        // over-approximation; loads then return fresh unknowns).
        state.heap.clear();
        state.unwritten_reads.clear();
        state.ref_regions.clear();

        // Equality-exit induction variables (`while i != n { … i += c }`): capture
        // each one's start (its pre-havoc value) and bound now, before the havoc
        // below replaces it with a fresh symbol. The sound bound is asserted after
        // the havoc (see `assert_eq_exit_bound`).
        let inductions: Vec<(EqExitIndVar, ExprId, ExprId)> = self
            .inductions
            .eq_exit_indvars(header)
            .to_vec()
            .into_iter()
            .filter_map(|iv| {
                let start = match state.env.get(&iv.reg) {
                    Some(SymValue::Scalar(e)) => *e,
                    _ => return None,
                };
                let bound = self.eval_scalar(&iv.bound, state);
                Some((iv, start, bound))
            })
            .collect();

        // Pointer equality-exit induction (`iter != end`): capture each one's
        // base region/offset/alignment, the end pointer's offset in that same
        // region, and the region byte size — all before the havoc clobbers
        // `iter`. The bounded offset is installed after the havoc (see
        // `assert_ptr_walk_bound`).
        let ptr_inductions: Vec<PtrIndCapture> = self
            .inductions
            .eq_exit_ptr_indvars(header)
            .to_vec()
            .into_iter()
            .filter_map(|iv: PtrIndVar| {
                let SymValue::Ptr(base) = state.env.get(&iv.reg)?.clone() else { return None };
                let Prov::Region(region) = base.prov else { return None };
                let size = state.regions.get(region)?.size;
                let SymValue::Ptr(end) = self.eval_value(&iv.end, state) else { return None };
                let Prov::Region(end_region) = end.prov else { return None };
                if end_region != region {
                    return None; // end is in a different allocation: cannot relate
                }
                let elem_stride = iv.elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let stride_bytes = u64::try_from(iv.stride_elems).ok()?.checked_mul(elem_stride)?;
                Some(PtrIndCapture {
                    reg: iv.reg,
                    region,
                    b0: base.offset,
                    align: base.align,
                    end_off: end.offset,
                    size,
                    stride_bytes,
                    bottom_test: iv.bottom_test,
                })
            })
            .collect();

        // If the loop body may free memory, then on any iteration after the
        // first a region could already be freed — so no region's liveness can
        // be proved inside (or after) the loop. Invalidate liveness
        // conservatively. (Loops that never free are unaffected.) Only *owned
        // heap* regions can be legitimately freed: a free of a borrowed or
        // stack/global region is flagged by `check_dealloc` (or the callee's own
        // verification), leaving the function non-PASS on that path anyway.
        if self.loop_frees.get(&header).copied().unwrap_or(false) {
            for r in &mut state.regions {
                if r.state == LifetimeState::Live
                    && r.contract.is_none()
                    && matches!(r.kind, RegionKind::Heap)
                {
                    r.state = LifetimeState::Freed;
                }
            }
        }

        // Havoc *every* register the loop body may redefine — not just the
        // header's own parameters. In strict SSA the loop-carried values are
        // header parameters and the rest are recomputed before use, so this is
        // usually redundant; but it makes the analysis robust to non-SSA input
        // (a register reassigned in the body keeps no stale pre-loop value).
        let modified = self
            .loop_modified
            .get(&header)
            .cloned()
            .unwrap_or_default();
        let modified_set: HashSet<RegId> = modified.iter().copied().collect();
        for reg in modified {
            match state.env.get(&reg).cloned() {
                Some(SymValue::Ptr(pre)) => {
                    // A loop-modified pointer loses its *region/bounds* provenance
                    // (conservative — it becomes opaque). But it **keeps its provenance
                    // labels**: an iterator walking a `foreign` container (a `list_for_each`
                    // over a foreign scatterlist) stays foreign. Sound — labels only feed the
                    // gated capability sink, never a memory-safety check — and it is what lets
                    // the taint reach the sink through the real worker's list traversal.
                    let labels = match pre.prov {
                        Prov::Region(rid) => {
                            state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default()
                        }
                        Prov::Unknown(_, Some(id)) => {
                            state.opaque_labels.get(&id).cloned().unwrap_or_default()
                        }
                        _ => FxHashSet::default(),
                    };
                    let offset = self.ctx.int(PTR_WIDTH, 0);
                    // **Opt-in** (`--assume-valid-loop-ptrs`): assume a loop-carried pointer
                    // still designates a valid, live object on every iteration — the kernel's
                    // intrusive-container / iterator discipline (`list_for_each_entry` walks
                    // live nodes; a moving cursor stays inside its buffer). Materialise a valid
                    // live region of *unknown* size instead of an opaque pointer: liveness
                    // (`no_use_after_free`) and non-null are then provable through the iterator,
                    // while **bounds stay UNKNOWN** (no size is known, so nothing is refuted
                    // against a guessed one — no false FAIL). Unsound in general: a moving
                    // pointer can walk off its object, and a list node can already be freed.
                    // Surfaced as the `valid-loop-ptrs` assumption.
                    if self.limits.assume_valid_loop_ptrs {
                        self.assumptions.insert("valid-loop-ptrs");
                        // **Bounds for the iterator.** The type of the `gep` that indexes this
                        // register says what it points at (`gep %struct.node, ptr %it, …` ⇒ a
                        // `struct node`), so the region gets `sizeof(struct node)` instead of an
                        // unsized (always-UNKNOWN) size — an access within the node then *proves*
                        // in bounds. The region stays `assumed`, so a constant offset past the
                        // recovered size is not refuted (no false FAIL if the node is embedded in
                        // a larger object); only a genuine input-driven overrun is. `None` when
                        // the frontend carries no type for it — the sound, unsized default.
                        let hint = self.reg_ptr_hints.get(&reg).copied();
                        // A `container_of`/`list_for_each_entry` cursor points at `member_offset`
                        // inside its *whole node* (size `container_size`): materialise the node and
                        // place the cursor at that offset, so the backward `container_of`
                        // subtraction (`cursor - member_offset`) lands at the node base (offset 0,
                        // in-object) instead of underflowing a member-sized region. An ordinary
                        // iterator keeps the pointee-typed size at offset 0.
                        let (region_size, ptr_offset) = match hint.and_then(|h| h.container()) {
                            Some((csize, coff)) => {
                                (Some(csize), self.ctx.int(PTR_WIDTH, coff as u128))
                            }
                            // No container: the type-derived pointee size, else the observed access
                            // extent (an untyped hand-rolled list cursor carries no `struct T` gep,
                            // so `size == 0` — size it to the bytes the code actually dereferences).
                            None => {
                                let sz = hint.and_then(|h| match (h.size, h.access_extent) {
                                    (s, _) if s > 0 => Some(s),
                                    (_, e) if e > 0 => Some(e),
                                    _ => None,
                                });
                                (sz, offset)
                            }
                        };
                        let rid = self.materialize_ref_region(region_size, true, true, state);
                        state.regions[rid].prov_labels.extend(labels);
                        // A valid object is aligned to its type's alignment, so give the region
                        // that alignment — the same rule the DWARF field/param recoveries use.
                        // Without it every access through the iterator would stay UNKNOWN on
                        // `alignment` alone. (For a container, the member type's alignment is a
                        // sound lower bound on the node's — a struct is at least as aligned as any
                        // member — so it never over-claims.)
                        if let Some(h) = hint.filter(|h| h.size > 0 || h.container_size > 0) {
                            state.regions[rid].base_align = h.region_align();
                        }
                        state.env.insert(
                            reg,
                            SymValue::Ptr(SymPointer {
                                prov: Prov::Region(rid),
                                offset: ptr_offset,
                                align: 1,
                                borrow: None,
                            }),
                        );
                    } else {
                        let id = self.prov_ids;
                        self.prov_ids += 1;
                        if !labels.is_empty() {
                            state.opaque_labels.insert(id, labels);
                        }
                        state.env.insert(
                            reg,
                            SymValue::Ptr(SymPointer {
                                prov: Prov::Unknown(POrigin::Loop, Some(id)),
                                offset,
                                align: 1,
                                borrow: None,
                            }),
                        );
                    }
                }
                Some(SymValue::Scalar(_)) => {
                    // A unit-stride, single-exit counting induction reaches every value
                    // its body guard admits, so model it as a GENUINE symbol (`ind…`):
                    // the body path condition's guard on it is then an exact reachable
                    // range, and an access it indexes can be refuted (an OOB there is a
                    // real bug). Otherwise a plain over-approximated `?` symbol.
                    let s = if self.sound_counting_induction(header, reg) {
                        self.fresh_induction_scalar(PTR_WIDTH)
                    } else {
                        self.fresh_scalar(PTR_WIDTH)
                    };
                    // Constrain by the sound interval invariant at the header
                    // (only faithfully-encodable, non-negative bounds).
                    let iv = self.analysis.entry_interval(header, reg);
                    if let Some(Bound::Fin(lo)) = iv.lower() {
                        if lo >= 0 {
                            let k = self.ctx.int(PTR_WIDTH, lo as u128);
                            let fact = self.ctx.cmp(SCmp::Sge, s, k);
                            state.facts.push(fact);
                        }
                    }
                    if let Some(Bound::Fin(hi)) = iv.upper() {
                        if hi >= 0 {
                            let k = self.ctx.int(PTR_WIDTH, hi as u128);
                            let fact = self.ctx.cmp(SCmp::Sle, s, k);
                            state.facts.push(fact);
                        }
                    }
                    state.env.insert(reg, SymValue::Scalar(s));
                }
                None => {} // not live at the header; defined fresh in the body
            }
        }

        // A register live at the header but *not* modified by the loop (a bound
        // computed before it — e.g. a clamped length `n = min(n, cap)`) keeps its
        // symbolic value, so it is not havoc'd above; but its sound interval bound
        // at the header still holds every iteration. Assert it, so a body access
        // guarded by it (`i < n`, with `n <= cap` known only to the interval
        // domain after guard refinement) can be proved. Deterministic order.
        let live_scalars: Vec<RegId> = {
            let mut v: Vec<RegId> = state
                .env
                .iter()
                .filter(|(r, val)| !modified_set.contains(r) && matches!(val, SymValue::Scalar(_)))
                .map(|(r, _)| *r)
                .collect();
            v.sort_unstable_by_key(|r| r.0);
            v
        };
        for reg in live_scalars {
            let Some(&SymValue::Scalar(s)) = state.env.get(&reg) else { continue };
            // Constrain at the *value's own width* — an `i1` (a boolean like
            // `buf == end`) carries no useful numeric bound and comparing it to a
            // 64-bit constant is ill-typed, so skip narrow values.
            let w = self.ctx.width(s);
            if w <= 1 {
                continue;
            }
            let iv = self.analysis.entry_interval(header, reg);
            if let Some(Bound::Fin(lo)) = iv.lower() {
                if lo >= 0 {
                    let k = self.ctx.int(w, lo as u128);
                    let fact = self.ctx.cmp(SCmp::Sge, s, k);
                    state.facts.push(fact);
                }
            }
            if let Some(Bound::Fin(hi)) = iv.upper() {
                if hi >= 0 {
                    let k = self.ctx.int(w, hi as u128);
                    let fact = self.ctx.cmp(SCmp::Sle, s, k);
                    state.facts.push(fact);
                }
            }
        }

        // Relational (zone) invariants: difference constraints `a - b <= c`
        // between the freshly-havoc'd register values that hold on every header
        // visit (e.g. `j <= i`). These are exactly what the per-register interval
        // bounds above cannot express, so they let a loop whose safety is a
        // *relation* between variables (a second induction variable, `buf[j]`
        // with `j <= i < n`) be proved. Sound under the same `linear-no-overflow`
        // assumption as the interval facts.
        let diffs: Vec<(ExprId, ExprId, i128)> = self
            .zones
            .entry_diffs(header)
            .into_iter()
            .filter_map(|(a, b, c)| match (state.env.get(&a), state.env.get(&b)) {
                (Some(SymValue::Scalar(ea)), Some(SymValue::Scalar(eb))) => Some((*ea, *eb, c)),
                _ => None,
            })
            .collect();
        for (ea, eb, c) in diffs {
            // The zone invariant `a - b <= c`, encoded as `a <=s b + c`. A *wrapping*
            // `b + c` makes the naive fact unsound: if the add signed-overflows, the
            // wrapped sum is wrong and the fact can read FALSE on a state where the
            // invariant genuinely holds — excluding a reachable state, which could
            // license a false PASS. Guard it to be vacuously true exactly when the
            // add overflows: then the fact is sound *bit-precisely* (no
            // linear-no-overflow tax on its consumers), and on the common no-overflow
            // path it collapses to the same strong `a <=s b + c` as before.
            //
            // `c` is a compile-time constant, so (a) skip bounds that do not fit the
            // blastable signed width — `const_expr` would misrepresent them — and
            // (b) its sign picks the overflow direction.
            if i64::try_from(c).is_err() {
                continue;
            }
            let cexpr = self.const_expr(c);
            let sum = self.ctx.bin(BvOp::Add, eb, cexpr);
            let le = self.ctx.cmp(SCmp::Sle, ea, sum); // a <=s b + c
            let fact = if c == 0 {
                le // b + 0 = b: never overflows
            } else if c > 0 {
                // adding c > 0 overflowed iff the sum dropped below b
                let overflow = self.ctx.cmp(SCmp::Slt, sum, eb);
                self.ctx.or(vec![overflow, le])
            } else {
                // adding c < 0 underflowed iff the sum rose above b
                let underflow = self.ctx.cmp(SCmp::Sgt, sum, eb);
                self.ctx.or(vec![underflow, le])
            };
            state.facts.push(fact);
        }

        // Equality-exit induction bounds: for each `while v != bound { … v += c }`
        // recognized at this header, assert `start ≤ v ≤ bound` on the now-havoc'd
        // `v` — after solver-checking the soundness side-conditions.
        for (iv, start_e, bound_e) in inductions {
            if let Some(SymValue::Scalar(v)) = state.env.get(&iv.reg).cloned() {
                self.assert_eq_exit_bound(state, v, start_e, bound_e, iv.stride);
            }
        }

        // Pointer-walk (`iter != end`) bounds: install the region-bounded offset
        // for each recognized pointer induction, replacing the conservative
        // opaque pointer the generic havoc produced.
        for cap in ptr_inductions {
            self.assert_ptr_walk_bound(state, cap);
        }

        // Sentinel-scan (`while (p[n] != 0) n++`) bound: if this loop sequentially
        // scans a sentinel-terminated region for its zero terminator, its index
        // cannot pass that terminator, which lies before the end.
        self.install_sentinel_scan_bound(header, state);
    }

    /// If `header`'s loop is a **sentinel scan** over a sentinel-terminated region
    /// — an index `n` starting at 0 and stepping by one element, a load of
    /// `base[n]`, and a loop exit taken exactly when that load is zero — bound the
    /// index by the region so every `base[n]` access is in bounds. Sound because a
    /// zero element is guaranteed before the end and the unit stride visits every
    /// element, so the scan stops at or before it: `n < element_count`, hence
    /// `(n+1)·E ≤ size`. Every side-condition below is checked; if any fails,
    /// nothing is installed.
    /// Is `reg` a **unit-stride, single-exit counting induction** at `header`? Such a
    /// loop reaches *every* value its governing guard admits, so the guard that the
    /// loop body's path condition already carries (entering the body requires it) is
    /// the induction's *exact* reachable range — not an over-approximation. Then a
    /// memory access indexed by the induction may be refuted: a witness value the
    /// guard admits is genuinely reached, so an out-of-bounds there is a real bug
    /// (e.g. an inclusive `for (i = 0; i <= N; i++) a[i]` writing `a[N]`).
    ///
    /// Requires, structurally: `reg` is a header parameter; its entry value is a
    /// constant and its back-edge value is `reg + 1` (unit stride up); the header's
    /// own branch is the loop's **only** exit and is governed by an upper-bound
    /// comparison on `reg` (`reg < B` / `reg <= B`, signed or unsigned) that gates
    /// entry to the body — so the body path condition bounds `reg` to the reached set.
    pub(crate) fn sound_counting_induction(&self, header: BlockId, reg: RegId) -> bool {
        let Some(hdr) = self.f.block(header) else { return false };
        let Some(pos) = hdr.params.iter().position(|(r, _)| *r == reg) else { return false };
        let mut def: HashMap<RegId, &Inst> = HashMap::new();
        for b in &self.f.blocks {
            for inst in &b.insts {
                if let Some(d) = inst.defined_reg() {
                    def.insert(d, inst);
                }
            }
        }
        // Unit-stride up: const entry, `reg + 1` back-edge.
        let preds: Vec<BlockId> = self
            .analysis
            .cfg()
            .predecessors(self.analysis.cfg().index_of(header).unwrap_or(usize::MAX))
            .iter()
            .map(|&p| self.analysis.cfg().block_id(p))
            .collect();
        let (mut const_entry, mut unit_backedge) = (false, false);
        for &pred in &preds {
            let Some(args) = edge_args(self.f, pred, header) else { continue };
            let Some(arg) = args.get(pos) else { continue };
            if self.is_back_edge(pred, header) {
                if let Operand::Reg(m) = arg {
                    if let Some(Inst::Assign { value: RValue::Bin { op: BinOp::Add, lhs, rhs, .. }, .. }) =
                        def.get(&resolve_copy(*m, &def))
                    {
                        let one = |o: &Operand| matches!(o, Operand::Const(Const::Int(bv)) if bv.unsigned() == 1);
                        let is_r = |o: &Operand| matches!(o, Operand::Reg(r) if resolve_copy(*r, &def) == reg);
                        unit_backedge = (is_r(lhs) && one(rhs)) || (is_r(rhs) && one(lhs));
                    }
                }
            } else if matches!(arg, Operand::Const(Const::Int(_))) {
                const_entry = true;
            }
        }
        if !(const_entry && unit_backedge) {
            return false;
        }
        // The header's branch is an upper-bound guard on `reg` gating body entry.
        let Terminator::CondBr { cond: Operand::Reg(c), then_blk, else_blk, .. } = &hdr.term else {
            return false;
        };
        let body = self.loop_bodies.get(&header).map(|b| b.as_slice()).unwrap_or(&[]);
        let in_body = |b: &BlockId| body.contains(b);
        let upper_on_reg = matches!(
            def.get(&resolve_copy(*c, &def)),
            Some(Inst::Assign { value: RValue::Cmp { op: CmpOp::Slt | CmpOp::Sle | CmpOp::Ult | CmpOp::Ule, lhs, rhs }, .. })
                if matches!(lhs, Operand::Reg(r) if resolve_copy(*r, &def) == reg)
                    && !matches!(rhs, Operand::Reg(r) if resolve_copy(*r, &def) == reg)
        );
        // The true edge must enter the loop (else the guard is inverted and the body
        // pathcond would carry its negation — not a clean upper bound).
        if !(upper_on_reg && in_body(then_blk) && !in_body(else_blk)) {
            return false;
        }
        // Single exit: the header's guard is the loop's only way out. Any other
        // body→outside edge (a `break`) means an iteration can be skipped, so a
        // guard-admitted index is no longer guaranteed reached.
        let body_set: HashSet<BlockId> = body.iter().copied().collect();
        for &bid in body {
            if bid == header {
                continue;
            }
            let Some(b) = self.f.block(bid) else { continue };
            let exits = match &b.term {
                Terminator::Br { target, .. } => !body_set.contains(target),
                Terminator::CondBr { then_blk, else_blk, .. } => {
                    !body_set.contains(then_blk) || !body_set.contains(else_blk)
                }
                _ => true, // a return/unreachable inside the body is another exit
            };
            if exits {
                return false;
            }
        }
        true
    }

    /// A fresh **genuine induction** symbol (named `ind…`, accepted by
    /// [`Explorer::goal_is_genuine`]): a unit-stride counter that reaches every value
    /// its body guard admits, so an access it indexes is refutable within that range.
    pub(crate) fn fresh_induction_scalar(&mut self, width: u32) -> ExprId {
        let name = format!("ind{}", self.fresh);
        self.fresh += 1;
        self.ctx.symbol(name, width)
    }
}
