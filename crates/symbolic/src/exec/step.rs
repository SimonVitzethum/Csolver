use super::*;

impl Explorer<'_> {
    pub(crate) fn step(&mut self, block: BlockId, idx: usize, inst: &Inst, state: &mut PathState) {
        match inst {
            Inst::Assign { dst, ty, value } => {
                // A generically-bound **pointer** call result (`Assign(dst, Undef)` for a
                // modelled call with no return summary — e.g. `fopen`'s handle) must get a
                // *stable opaque pointer identity*, not a scalar `undef`: otherwise the same
                // SSA value is a scalar here and an opaque pointer once used as one, so a
                // `ret`-typestate/taint target and a later use disagree on the resource key.
                let v = match value {
                    RValue::Use(Operand::Const(Const::Undef)) if ty.is_ptr() => {
                        self.fresh_value(ty, POrigin::Call)
                    }
                    _ => self.eval_rvalue(value, state),
                };
                state.env.insert(*dst, v);
                // Division / modulo by zero: the divisor of a `/` or `%` must be provably non-zero
                // (a zero divisor is UB / a hardware trap). Refuted with a witness when the divisor
                // can be zero on the path (the `decide` gate keeps it sound: a genuine-input divisor
                // in bug-finding mode, or a definite zero on an exact path in strict mode).
                if let RValue::Bin { op, lhs, rhs, flags } = value {
                    // `nsw`/`nuw`-flagged add/sub/mul must not wrap (UB in C / poison in
                    // LLVM). Only the flagged form carries an obligation — plain wrapping
                    // arithmetic raises nothing. The no-overflow goal is built with
                    // same-width sign predicates (signed add/sub) and a double-width
                    // product for BOTH mul forms — signed via `sext`, unsigned via `zext`
                    // (see `arith_no_overflow`), so signed *and* unsigned mul are checked.
                    if (flags.nsw || flags.nuw)
                        && matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul)
                    {
                        let a = self.eval_scalar(lhs, state);
                        let b = self.eval_scalar(rhs, state);
                        if let Some(goal) = self.arith_no_overflow(*op, a, b, *flags) {
                            let decision =
                                self.decide(&[goal], state, RefuteMode::Possible, &[]);
                            self.record_mem(
                                block,
                                idx,
                                SafetyProperty::NoArithOverflow,
                                decision,
                                "the arithmetic does not overflow",
                                "the operation may overflow (signed/unsigned wrap is undefined behaviour)",
                            );
                        }
                    }
                    if matches!(op, BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem) {
                        let d = self.eval_scalar(rhs, state);
                        let zero = self.ctx.int(self.ctx.width(d), 0);
                        let nonzero = self.ctx.cmp(SCmp::Ne, d, zero);
                        let decision = self.decide(&[nonzero], state, RefuteMode::Possible, &[]);
                        self.record_mem(
                            block,
                            idx,
                            SafetyProperty::NoDivByZero,
                            decision,
                            "divisor is non-zero",
                            "the divisor may be zero (division by zero)",
                        );
                    }
                    // Shift past the bit width is UB (a poison value): the shift amount must be
                    // strictly less than the operand width. Refuted when it can reach the width.
                    if matches!(op, BinOp::Shl | BinOp::LShr | BinOp::AShr) {
                        let amt = self.eval_scalar(rhs, state);
                        let w = self.ctx.width(amt);
                        let width_c = self.ctx.int(w, w as u128);
                        let in_range = self.ctx.cmp(SCmp::Ult, amt, width_c);
                        let decision = self.decide(&[in_range], state, RefuteMode::Possible, &[]);
                        self.record_mem(
                            block,
                            idx,
                            SafetyProperty::NoShiftOverflow,
                            decision,
                            "shift amount is less than the bit width",
                            "the shift amount may reach or exceed the bit width (undefined behaviour)",
                        );
                    }
                }
                // Taint propagation: the result carries the union of its operands' taint.
                let t = self.rvalue_taint(value, state);
                if t.is_empty() {
                    state.tainted.remove(dst);
                } else {
                    state.tainted.insert(*dst, t);
                }
            }
            Inst::Alloc { dst, region, elem, count, align } => {
                let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let count_e = self.eval_scalar(count, state);
                let stride_e = self.ctx.int(PTR_WIDTH, stride as u128);
                let size = self.ctx.bin(BvOp::Mul, count_e, stride_e);
                let perms = if *region == RegionKind::Global {
                    Permissions::READ_ONLY
                } else {
                    Permissions::READ_WRITE
                };
                // A successful allocation has size <= isize::MAX, so the element
                // count times the stride does not wrap (`alloc-succeeds`). Kept
                // off `facts` (it would slow every proof) and used only to make a
                // memory-OOB counterexample faithful.
                let nowrap = self.size_no_wrap_fact(count_e, stride);
                // A stack allocation whose byte count is **not a compile-time constant**
                // is a *guessed*-size region: a machine-code frame model (`rsp`/`rbp` with
                // an open-above size) or a variable-length array. Mark it `assumed` so a
                // constant in-bounds obligation past the guessed size is left UNKNOWN rather
                // than refuted (no false FAIL on a stack-passed argument at `[rbp + 16]`, or
                // a fixed index into a VLA); a genuinely adversarial (input-driven) offset is
                // still refuted (see `check_access`). A constant-count `alloca`/`sub rsp, N`
                // stays precise (refutable) as before.
                let assumed = *region == RegionKind::Stack && !matches!(count, Operand::Const(_));
                let rid = state.regions.len();
                state.regions.push(SymRegion {
                    kind: *region,
                    size,
                    base_align: (*align as u64).max(1),
                    state: LifetimeState::Live,
                    perms,
                    contract: None,
                    size_nowrap: Some(nowrap),
                    sentinel: None,
                    user_controlled: false,
                    assumed,
                    prov_labels: FxHashSet::default(),
                });
                // Bug-finding: an attacker-controlled `count * sizeof(T)` size that can
                // wrap the pointer width under-allocates — a heap overflow at the root.
                // When the size is a variable factor times a constant element size `c`,
                // overflow is exactly `var > (UINT_MAX / c)` — a constant-bound check the
                // solver discharges cheaply (no wide multiply). A feasible genuine
                // overflow is refuted with a witness; a bounded (guarded) count proves.
                // Only run in bug-finding mode; sound `verify` does not enumerate this
                // obligation, so allocation sizes stay non-wrapping under `alloc-succeeds`.
                if self.bug_finding {
                    match self.size_overflow_goal(size) {
                        Some(goal) => {
                            let decision = self.decide(&[goal], state, RefuteMode::Possible, &[]);
                            self.record_mem(block, idx, SafetyProperty::NoSizeOverflow, decision, "allocation size does not overflow", "the size product may overflow and under-allocate");
                        }
                        None => self.record(block, idx, SafetyProperty::NoSizeOverflow, true, "allocation size does not overflow", ""),
                    }
                } else {
                    self.record(block, idx, SafetyProperty::NoSizeOverflow, true, "allocation size does not overflow", "");
                }
                // The byte size is non-negative by construction.
                let zero = self.ctx.int(PTR_WIDTH, 0);
                let nonneg = self.ctx.cmp(SCmp::Sle, zero, size);
                state.facts.push(nonneg);
                state.env.insert(
                    *dst,
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: zero,
                        align: *align as u64,
                    }),
                );
            }
            Inst::PtrOffset { dst, base, index, elem } => {
                let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let base_ptr = self.eval_pointer(base, state);
                // Widen a narrower index to pointer width — a `zext i32 %i to i64`
                // the executor kept at its source width (the common `arr[unsigned]`
                // form), else the offset arithmetic mixes widths and no bound holds.
                let index_e = self.eval_scalar(index, state);
                let index_e = self.widen_to_ptr(index_e);
                let stride_e = self.ctx.int(PTR_WIDTH, stride as u128);
                let delta = self.ctx.bin(BvOp::Mul, index_e, stride_e);
                let new_off = self.ctx.bin(BvOp::Add, base_ptr.offset, delta);
                // Alignment after the offset: for a *constant* index use the
                // concrete byte delta (so `buf(16-aligned) + 16` stays
                // 16-aligned); for a symbolic index fall back to the stride.
                let new_align = match self.ctx.as_const(index_e) {
                    Some(c) => {
                        let d = c.signed().wrapping_mul(stride as i128).unsigned_abs() as u64;
                        gcd(base_ptr.align, d)
                    }
                    None => gcd(base_ptr.align, stride),
                };
                let result = SymPointer {
                    prov: base_ptr.prov.clone(),
                    offset: new_off,
                    align: new_align,
                };
                self.check_ptr_arith(block, idx, &result, state);
                state.env.insert(*dst, SymValue::Ptr(result));
            }
            Inst::FieldPtr { dst, base, field, size, align } => {
                let base_ptr = self.eval_pointer(base, state);
                let result = match &base_ptr.prov {
                    // Guard against a stale (dropped-region) id — fall through to the
                    // unknown-provenance arm below rather than indexing out of bounds.
                    Prov::Region(r) if state.regions.get(*r).is_some() => {
                        // A typed field of a valid aggregate lies within it. Place
                        // it at its synthetic offset (concrete, so distinct fields
                        // are disjoint and the same field round-trips), assert
                        // `offset + size <= region size` (the field fits), and
                        // inherit the field's alignment (a field is aligned within
                        // its struct). The following Load/Store is then in bounds
                        // and aligned by construction — no real layout is needed.
                        let rid = *r;
                        let region_size = state.regions[rid].size;
                        let off = self.field_offset(rid, *field, *size);
                        let off_e = self.ctx.int(PTR_WIDTH, off as u128);
                        let end = self.ctx.int(PTR_WIDTH, (off + *size) as u128);
                        let hi = self.ctx.cmp(SCmp::Sle, end, region_size);
                        state.facts.push(hi);
                        SymPointer { prov: Prov::Region(rid), offset: off_e, align: (*align).max(1) }
                    }
                    // Not a known region (null/unknown provenance): the field
                    // pointer inherits it, so a later access is soundly unproven.
                    _ => SymPointer {
                        prov: base_ptr.prov.clone(),
                        offset: base_ptr.offset,
                        align: (*align).max(1),
                    },
                };
                state.env.insert(*dst, SymValue::Ptr(result));
            }
            Inst::Load { dst, ty, ptr, align, volatile } => {
                let p = self.eval_pointer(ptr, state);
                let asize = ty.size_bytes(&LAYOUT).unwrap_or(1);
                self.check_access((block, idx), &p, asize, *align as u64, SafetyProperty::ValidRead, state);
                if self.limits.aliasing_model {
                    self.check_borrow_access((block, idx), ptr, false, &p, state);
                }
                // An atomic/volatile read (`READ_ONCE`/`atomic_read`) is race-free by
                // construction — excluded from the data-race pass.
                if !*volatile {
                    self.record_shared_access(ptr, false, &p, state);
                }
                let exact_before = state.exact;
                let (value, origin) = self.load_value(&p, asize, ty, state);
                match origin {
                    LoadOrigin::Stored => {}
                    LoadOrigin::Uncertain => state.exact = false,
                    LoadOrigin::Unwritten => {
                        // No store reaches this location. For a freshly-allocated
                        // region that is a read of uninitialized memory (UB). On
                        // an exact path it is a definite violation, refutable with
                        // a faithful witness. (Compute the witness before dropping
                        // `exact` for the unknown value below.)
                        if exact_before && self.is_fresh_alloc(&p, state) {
                            if let Some(model) = self.feasibility_witness(state) {
                                self.record_uninit_read(block, idx, model);
                            }
                        }
                        state.exact = false;
                    }
                }
                // Taint-on-read: a pointer loaded from a labelled object inherits its
                // provenance — a pointer stored in a `foreign` scatterlist/socket is itself
                // foreign. Only ADDS labels, and a label causes a FAIL only through a (gated)
                // capability requirement (`require-if-alias` never fires off the safe
                // out-of-place path), so this can introduce neither a false PASS nor a false
                // FAIL. Flows provenance through the plain pointer-field loads the real crypto
                // worker uses (`sk → ctx → tsgl_src`), complementing the RefWitness path.
                if ty.is_ptr() {
                    let src_labels = match p.prov {
                        Prov::Region(rid) => {
                            state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default()
                        }
                        Prov::Unknown(_, Some(id)) => {
                            state.opaque_labels.get(&id).cloned().unwrap_or_default()
                        }
                        _ => FxHashSet::default(),
                    };
                    if !src_labels.is_empty() {
                        match &value {
                            SymValue::Ptr(SymPointer { prov: Prov::Region(rid), .. }) => {
                                if let Some(r) = state.regions.get_mut(*rid) {
                                    r.prov_labels.extend(src_labels);
                                }
                            }
                            SymValue::Ptr(SymPointer { prov: Prov::Unknown(_, Some(vid)), .. }) => {
                                state.opaque_labels.entry(*vid).or_default().extend(src_labels);
                            }
                            _ => {}
                        }
                    }
                }
                // Devirtualisation: a pointer load from a constant ops-struct global
                // at a concrete offset with a known function-pointer field resolves the
                // loaded value to a specific callee, so a later indirect call through
                // `dst` uses that summary instead of an opaque havoc.
                if ty.is_ptr() {
                    if let Prov::Region(rid) = p.prov {
                        if let Some(table) = self.global_fnptrs.get(&rid) {
                            if let Some(off) = self.ctx.as_const(p.offset).map(|bv| bv.unsigned()) {
                                if let Some(&fid) = table.get(&(off as u64)) {
                                    state.fn_ptrs.insert(*dst, fid);
                                }
                            }
                        }
                    }
                }
                // Taint-on-read for **scalars**: a scalar loaded from a tainted region (a
                // `taint-source`-labelled buffer — e.g. a `copy_from_user` destination)
                // inherits the region's taint labels. (The pointer case is handled above.)
                if !ty.is_ptr() {
                    let src_labels = match p.prov {
                        Prov::Region(rid) => {
                            state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default()
                        }
                        Prov::Unknown(_, Some(id)) => {
                            state.opaque_labels.get(&id).cloned().unwrap_or_default()
                        }
                        _ => FxHashSet::default(),
                    };
                    if !src_labels.is_empty() {
                        state.tainted.entry(*dst).or_default().extend(src_labels);
                    }
                }
                state.env.insert(*dst, value);
            }
            Inst::Store { ty, ptr, value, align, volatile } => {
                let p = self.eval_pointer(ptr, state);
                let asize = ty.size_bytes(&LAYOUT).unwrap_or(1);
                self.check_access((block, idx), &p, asize, *align as u64, SafetyProperty::ValidWrite, state);
                // Rust aliasing model (opt-in): a write through a pointer derived from a shared
                // `&T` borrow is an unambiguous borrow-stack violation. Refuted only on a
                // feasible path (record_temporal gates on a feasibility witness) — no false FAIL.
                if self.limits.aliasing_model {
                    if ptr.as_reg().is_some_and(|r| self.shared_borrow_regs.contains(&r)) {
                        self.record_temporal(
                            (block, idx),
                            SafetyProperty::NoAliasingViolation,
                            true,
                            state,
                            "no write through a shared (&T) reference",
                            "write through a shared reference (Rust aliasing violation)",
                        );
                    }
                    self.check_borrow_access((block, idx), ptr, true, &p, state);
                }
                // An atomic/volatile write (`WRITE_ONCE`/`atomic_set`) is race-free by
                // construction — excluded from the data-race pass.
                if !*volatile {
                    // A store whose stored *value* derives from a load is a genuine
                    // read-modify-write (`x = x + 1`) — flag it so the atomicity check treats
                    // only dependent writes as lost-update candidates (an independent `x = 5`
                    // overwrite is not a lost update). See `record_shared_access`.
                    let rmw = matches!(value, Operand::Reg(r) if self.load_derived.contains(r));
                    self.record_shared_access_kind(ptr, true, rmw, &p, state);
                }
                let v = self.eval_value(value, state);
                // Taint through memory: storing a tainted scalar into a region taints the
                // region, so a value later loaded from it stays tainted (a `user`-tainted
                // length written into a descriptor field and read back at a sink).
                if let Operand::Reg(r) = value {
                    if let Some(labels) = state.tainted.get(r).cloned() {
                        match &p.prov {
                            Prov::Region(rid) => {
                                if let Some(reg) = state.regions.get_mut(*rid) {
                                    reg.prov_labels.extend(labels);
                                }
                            }
                            Prov::Unknown(_, Some(id)) => {
                                state.opaque_labels.entry(*id).or_default().extend(labels);
                            }
                            _ => {}
                        }
                    }
                }
                state.heap.push(StoreRecord { target: p, value: v, size: asize });
                // A store may reassign a raw-pointer field, so the region a later `RefWitness`
                // load of that field should materialise is now a *different* object. Drop the
                // materialised-field cache (which the RefWitness path consults instead of the
                // store) — else two loads straddling the store would be treated as the *same*
                // region and `require-if-alias` could fire spuriously (a false FAIL).
                state.ref_regions.clear();
            }
            Inst::Dealloc { ptr, .. } => {
                let p = self.eval_pointer(ptr, state);
                self.record_free_event(ptr, &p, state);
                self.check_dealloc(block, idx, &p, state);
            }
            Inst::Call { dst, callee, args, ret_ty, ret_ref } => {
                self.check_lock_call((block, idx), callee, args, state);
                self.step_call((block, idx), dst.as_ref(), callee, args, ret_ty, *ret_ref, state);
                // Per-CPU accessor: tag the returned pointer's identity so accesses through it
                // are excluded from the data-race pass (per-CPU data is thread-local).
                if let (Some(d), Callee::Symbol(n)) = (dst, callee) {
                    if crate::sync::classes().percpu(n) {
                        if let Some(RefBase::Opaque(id)) =
                            state.env.get(d).and_then(Self::ptr_base_key)
                        {
                            state.percpu.insert(id);
                        }
                    }
                }
            }
            // `llvm.lifetime.start/end(ptr)`: the slot's live range. `end` marks the
            // pointed-to region **dead** (a later access before a new `start` is a
            // use-after-scope, caught by the existing NoUseAfterFree/NoDanglingDeref
            // checks); `start` re-lives it. Only a tracked region transitions; an opaque
            // pointer is ignored. Meet-joined at merges, so a partial end never false-FAILs.
            Inst::Intrinsic { name, args, .. } if name.starts_with("llvm.lifetime.") => {
                if let Some(p) = args.first() {
                    if let Prov::Region(rid) = self.eval_pointer(p, state).prov {
                        if let Some(r) = state.regions.get_mut(rid) {
                            r.state = if name.contains("lifetime.end") {
                                LifetimeState::Freed
                            } else {
                                LifetimeState::Live
                            };
                        }
                    }
                }
            }
            // A reborrow marker (opt-in aliasing model): `csolver.retag.mut` (a `&mut`) or
            // `csolver.retag.shared` (a `&T`). `args = [new-borrow reg, parent pointer]`. Push
            // the new borrow tag onto the parent pointer's region borrow stack — a `&mut` pops
            // the parent's other descendants (which the reborrow invalidates); a `&T` coexists.
            // A no-op unless the model is on. See `step_retag`.
            Inst::Intrinsic { name, args, .. }
                if self.limits.aliasing_model
                    && (name == "csolver.retag.mut" || name == "csolver.retag.shared") =>
            {
                self.step_retag(args, state);
            }
            Inst::Intrinsic { dst: Some(d), .. } => {
                let s = self.fresh_scalar(PTR_WIDTH);
                state.env.insert(*d, SymValue::Scalar(s));
            }
            Inst::SafetyCheck { condition, .. } => {
                let goal = self.eval_condition(condition, state);
                let decision = self.decide(&[goal], state, RefuteMode::Definite, &[]);
                self.record_scalar(block, idx, decision);
            }
            // Attach a provenance label (a contract `label`) — to the pointed-to region, or,
            // for an opaque pointer (a raw-pointer parameter), to its holding SSA register.
            // Delegated arm groups (split out mechanically; see the sibling files).
            inst @ (Inst::ProvLabel { .. }
            | Inst::ProvPropagate { .. }
            | Inst::CapRequire { .. }
            | Inst::CapRequireIfAlias { .. }
            | Inst::CapRequireIfAliasFields { .. }
            | Inst::TaintSource { .. }
            | Inst::TaintClear { .. }
            | Inst::TaintCheck { .. }
            | Inst::TypestateSet { .. }
            | Inst::TypestateRequire { .. }
            | Inst::TypestateYield { .. }
            | Inst::Refcount { .. }
            | Inst::TypestateLeakCheck { .. }
            | Inst::Barrier { .. }
            | Inst::Spawn { .. }
            | Inst::Join
            | Inst::Cas { .. }
            | Inst::SecretCheck { .. }) => self.step_contract(block, idx, inst, state),
            inst @ (Inst::RefWitness { .. } | Inst::MemIntrinsic { .. }) => {
                self.step_mem_inst(block, idx, inst, state)
            }
            Inst::Intrinsic { dst: None, .. } | Inst::Asm { .. } => {}
        }
    }
}
