use super::*;

impl Explorer<'_> {
    /// Check a `memcpy`/`memmove`/`memset`: the destination must be writable and
    /// in bounds for `len` bytes, and (for copy/move) the source readable and in
    /// bounds for `len` bytes. Each property is recorded as the conjunction over
    /// the touched pointers.
    pub(crate) fn check_mem_intrinsic(
        &mut self,
        at: (BlockId, usize),
        kind: MemKind,
        dst_op: &Operand,
        src_op: Option<&Operand>,
        len_op: &Operand,
        state: &PathState,
    ) {
        use SafetyProperty::*;
        let (block, idx) = at;
        let dst = self.eval_pointer(dst_op, state);
        let len_e = self.eval_scalar(len_op, state);
        let need_src = matches!(kind, MemKind::Copy | MemKind::Move);
        let src = if need_src {
            src_op.map(|s| self.eval_pointer(s, state))
        } else {
            None
        };

        // Snapshot region facts (copied out, so no borrow is held).
        let dst_facts = region_facts(&dst, state);
        let src_facts = src.as_ref().and_then(|p| region_facts(p, state));

        let dst_nn = dst_facts.is_some();
        let src_nn = !need_src || src_facts.is_some();
        self.record(block, idx, NoNullDeref, dst_nn && src_nn, "memcpy pointers are non-null", "a memcpy pointer may be null or have opaque provenance");

        let dst_live = dst_facts.is_some_and(|f| f.live);
        let src_live = !need_src || src_facts.is_some_and(|f| f.live);
        self.record(block, idx, NoUseAfterFree, dst_live && src_live, "memcpy regions are live", "a memcpy region may be freed");

        // In-bounds for the bulk length. Refutable (like `check_access`): on a region
        // whose size cannot wrap, a satisfying `off + len > size` is a genuine OOB, so
        // a user-controlled length overrunning a `copy_from_user`/`memcpy` buffer is a
        // FAIL with a witness. The source (if any) is checked prove-only — a `Refuted`
        // on it would need its own region's no-wrap premise; the destination write is
        // the dominant overflow class and carries the refutation.
        // A narrower length (a `zext i32 %n to i64` the executor kept at its source
        // width) is zero-extended to pointer width, so the bounds arithmetic is
        // width-consistent and the guard on the narrow value still applies.
        let len_e = self.widen_to_ptr(len_e);
        let src_inb = match (need_src, &src, src_facts) {
            (false, _, _) => true,
            (true, Some(p), Some(f)) => self.prove_in_bounds_len(p.offset, len_e, f.size, state),
            _ => false,
        };
        let dst_decision = match dst_region_nowrap(&dst, state) {
            Some((size, nowrap)) if src_inb => {
                let conj = self.in_bounds_len_conjuncts(dst.offset, len_e, size);
                self.decide(&conj, state, RefuteMode::Possible, &[nowrap])
            }
            _ => {
                let ok = dst_facts.is_some_and(|f| self.prove_in_bounds_len(dst.offset, len_e, f.size, state));
                if ok && src_inb { Decision::Proven } else { Decision::Unknown }
            }
        };
        self.record_mem(block, idx, InBounds, dst_decision, "the copy stays within both regions", "could not prove the copy stays in bounds");

        let dst_w = dst_facts.is_some_and(|f| f.perms.write);
        self.record(block, idx, ValidWrite, dst_w, "destination is writable", "destination is not writable");
        if need_src {
            let src_r = src_facts.is_some_and(|f| f.perms.read);
            self.record(block, idx, ValidRead, src_r, "source is readable", "source is not readable");
        }

        // **No forbidden overlap** (`memcpy` only — `memmove` is the overlapping form).
        // `memcpy` is UB if the source and destination byte ranges overlap. Only decidable
        // when both pointers share the SAME base object (same region id, or the same opaque
        // provenance): then the offsets `d`, `s` are comparable and the ranges `[d, d+len)`
        // and `[s, s+len)` overlap iff neither ends at or before the other begins. We prove
        // *no overlap* = `(d + len <=s s) OR (s + len <=s d)`; a refutation is a concrete
        // aliasing `memcpy(p+i, p+j, n)` with `|i-j| < n`. Different bases (or an opaque
        // destination/source) cannot be shown to overlap → recorded proven (no false FAIL).
        if matches!(kind, MemKind::Copy) {
            let same_base = match (&src, Self::ptr_base_key(&SymValue::Ptr(dst.clone()))) {
                (Some(sp), Some(db)) => {
                    Self::ptr_base_key(&SymValue::Ptr(sp.clone())) == Some(db)
                }
                _ => false,
            };
            match (same_base, &src) {
                (true, Some(sp)) => {
                    let end_d = self.ctx.bin(BvOp::Add, dst.offset, len_e);
                    let end_s = self.ctx.bin(BvOp::Add, sp.offset, len_e);
                    // d + len <= s  (dst ends before src begins) OR  s + len <= d.
                    let d_before_s = self.ctx.cmp(SCmp::Sle, end_d, sp.offset);
                    let s_before_d = self.ctx.cmp(SCmp::Sle, end_s, dst.offset);
                    let no_overlap = self.ctx.or(vec![d_before_s, s_before_d]);
                    // Refute overlap only under the region's no-wrap premise, so the witness
                    // offsets are genuine (a wrapped `d+len` cannot fake a non-overlap either).
                    let extra: Vec<ExprId> = dst_region_nowrap(&dst, state).map(|(_, nw)| nw).into_iter().collect();
                    let decision = self.decide(&[no_overlap], state, RefuteMode::Possible, &extra);
                    self.record_mem(block, idx, NoForbiddenOverlap, decision, "memcpy source and destination do not overlap", "the memcpy source and destination ranges overlap (use memmove)");
                }
                _ => self.record(block, idx, NoForbiddenOverlap, true, "memcpy source and destination do not overlap", ""),
            }
        }

        // Surface the assumptions the touched regions rest on.
        if dst_nn && src_nn && dst_live && src_live {
            for f in [dst_facts, src_facts].into_iter().flatten() {
                self.assumptions.insert(f.contract.unwrap_or(ALLOC_SUCCEEDS));
            }
        }
    }

    /// Prove `0 <= offset && offset + len <= size` (a `len`-byte access).
    pub(crate) fn prove_in_bounds_len(&mut self, offset: ExprId, len: ExprId, size: ExprId, state: &PathState) -> bool {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let end = self.ctx.bin(BvOp::Add, offset, len);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        // No-overflow: the extent `offset + len` must not wrap past 2^63. Without
        // this, a wrapped (negative) `end` satisfies `end <=s size` vacuously, so a
        // pathological huge offset/len would prove "in bounds" — a false PASS. With
        // `offset <=s end` and `end <=s size` (size a real, sub-2^63 region size),
        // `end` is pinned to the non-wrapped range, so it equals the true sum.
        let no_overflow = self.ctx.cmp(SCmp::Sle, offset, end);
        let upper = self.ctx.cmp(SCmp::Sle, end, size);
        self.prove(lower, state) && self.prove(no_overflow, state) && self.prove(upper, state)
    }

    /// Handle a call using the callee's summary: effect-aware heap handling and
    /// a provenance-preserving return binding.
    /// Apply a callee's derived provenance-transfer summary to the actual argument
    /// regions: add each `(arg, label)` to that argument's region, then union each
    /// `(dst, src)` source's labels into the destination's. Mirrors the direct
    /// `ProvLabel`/`ProvPropagate` semantics, one interprocedural step removed.
    pub(crate) fn apply_prov_transfer(&self, prov: &ProvTransfer, argvals: &[SymValue], state: &mut PathState) {
        let region = |i: usize| match argvals.get(i) {
            Some(SymValue::Ptr(p)) => match p.prov {
                Prov::Region(rid) => Some(rid),
                _ => None,
            },
            _ => None,
        };
        for &(a, label) in &prov.labels {
            if let Some(rid) = region(a) {
                if let Some(r) = state.regions.get_mut(rid) {
                    r.prov_labels.insert(label);
                }
            }
        }
        for &(d, s) in &prov.transfers {
            let Some(src) = region(s) else { continue };
            let Some(src_region) = state.regions.get(src) else { continue };
            let src_labels = src_region.prov_labels.clone();
            if src_labels.is_empty() {
                continue;
            }
            if let Some(rid) = region(d) {
                if let Some(r) = state.regions.get_mut(rid) {
                    r.prov_labels.extend(src_labels);
                }
            }
        }
    }

    /// The provenance labels attached to a pointer operand: a materialised region's own
    /// labels, or — for an **opaque pointer** — the labels on its provenance identity
    /// (`Prov::Unknown`'s id, which flows through `gep`/copy). Unifies both channels.
    /// Does `p` carry the `iomem` provenance label — i.e. is it a device-register mapping from
    /// the `ioremap` family (directly, or loaded from a field an `iomem` pointer was stored to)?
    /// The label id is resolved once from the shared contract interner. Reads the labels on the
    /// pointer's region or opaque provenance id (see [`Self::ptr_labels`], but taking a
    /// `SymPointer` directly since the caller already has it evaluated).
    pub(crate) fn pointer_is_iomem(&self, p: &SymPointer, state: &PathState) -> bool {
        let Some(iomem) = csolver_contracts::prov_interner().id("iomem") else { return false };
        let labels = match &p.prov {
            Prov::Region(rid) => state.regions.get(*rid).map(|r| &r.prov_labels),
            Prov::Unknown(_, Some(id)) => state.opaque_labels.get(id),
            _ => None,
        };
        labels.is_some_and(|l| l.contains(&iomem))
    }

    pub(crate) fn ptr_labels(&mut self, ptr: &Operand, state: &PathState) -> FxHashSet<u32> {
        match self.eval_pointer(ptr, state).prov {
            Prov::Region(rid) => state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default(),
            Prov::Unknown(_, Some(id)) => state.opaque_labels.get(&id).cloned().unwrap_or_default(),
            _ => FxHashSet::default(),
        }
    }

    /// Attach a provenance label to a pointer operand: its region if it has one, else its
    /// opaque provenance identity (so an opaque parameter — and any field address derived
    /// from it — becomes labelable without being modelled as a region; sound: `opaque_labels`
    /// touch no safety check but the provenance ones).
    pub(crate) fn add_ptr_label(&mut self, ptr: &Operand, label: u32, state: &mut PathState) {
        match self.eval_pointer(ptr, state).prov {
            Prov::Region(rid) => {
                if let Some(r) = state.regions.get_mut(rid) {
                    r.prov_labels.insert(label);
                }
            }
            Prov::Unknown(_, Some(id)) => {
                state.opaque_labels.entry(id).or_default().insert(label);
            }
            _ => {}
        }
    }

    /// The taint labels an r-value's result carries: the **union** of its register operands'
    /// scalar taint (a `tainted` length + 1 is still tainted; a cast/compare of a tainted
    /// value is tainted). Constants are untainted. The propagation rule of the taint lattice.
    pub(crate) fn rvalue_taint(&self, rv: &RValue, state: &PathState) -> FxHashSet<u32> {
        let ops: Vec<&Operand> = match rv {
            RValue::Use(o) => vec![o],
            RValue::Bin { lhs, rhs, .. } | RValue::Cmp { lhs, rhs, .. } => vec![lhs, rhs],
            RValue::Cast { operand, .. } => vec![operand],
            RValue::Select { cond, then_val, else_val } => vec![cond, then_val, else_val],
        };
        let mut t = FxHashSet::default();
        for o in ops {
            if let Operand::Reg(r) = o {
                if let Some(s) = state.tainted.get(r) {
                    t.extend(s.iter().copied());
                }
            }
        }
        t
    }

    /// Mark a value operand tainted with `taint`: a pointer taints its region (so bytes read
    /// from it are tainted), a scalar taints its register.
    pub(crate) fn taint_add(&mut self, op: &Operand, taint: u32, state: &mut PathState) {
        if matches!(self.eval_value(op, state), SymValue::Ptr(_)) {
            self.add_ptr_label(op, taint, state);
        } else if let Operand::Reg(r) = op {
            state.tainted.entry(*r).or_default().insert(taint);
        }
    }

    /// Whether a value operand is definitely tainted with `taint` — a scalar register's taint
    /// set, or (for a pointer) its region/opaque provenance labels.
    pub(crate) fn taint_has(&mut self, op: &Operand, taint: u32, state: &PathState) -> bool {
        if let Operand::Reg(r) = op {
            if state.tainted.get(r).is_some_and(|s| s.contains(&taint)) {
                return true;
            }
        }
        matches!(self.eval_value(op, state), SymValue::Ptr(_))
            && match self.eval_pointer(op, state).prov {
                Prov::Region(rid) => {
                    state.regions.get(rid).is_some_and(|r| r.prov_labels.contains(&taint))
                }
                Prov::Unknown(_, Some(id)) => {
                    state.opaque_labels.get(&id).is_some_and(|s| s.contains(&taint))
                }
                _ => false,
            }
    }

    /// Clear `taint` from a value operand (a recognised sanitiser): both its scalar register
    /// taint and, for a pointer, its region/opaque provenance labels.
    pub(crate) fn taint_remove(&mut self, op: &Operand, taint: u32, state: &mut PathState) {
        if let Operand::Reg(r) = op {
            if let Some(s) = state.tainted.get_mut(r) {
                s.remove(&taint);
            }
        }
        if matches!(self.eval_value(op, state), SymValue::Ptr(_)) {
            match self.eval_pointer(op, state).prov {
                Prov::Region(rid) => {
                    if let Some(r) = state.regions.get_mut(rid) {
                        r.prov_labels.remove(&taint);
                    }
                }
                Prov::Unknown(_, Some(id)) => {
                    if let Some(s) = state.opaque_labels.get_mut(&id) {
                        s.remove(&taint);
                    }
                }
                _ => {}
            }
        }
    }


    /// Record a **shared-memory access** for the lockset data-race check (G1): if `ptr`
    /// designates a *shareable* location (a global, or an object reached through a parameter —
    /// a stack local is thread-local and skipped) with a resolvable access class, note
    /// `(class, is_write, lock-classes held)`. The whole-program pass then flags a location
    /// accessed under no common lock, with a write, from ≥2 functions.
    pub(crate) fn record_shared_access(&mut self, ptr: &Operand, is_write: bool, p: &SymPointer, state: &PathState) {
        self.record_shared_access_kind(ptr, is_write, false, p, state);
    }

    /// Like [`Self::record_shared_access`] but with `rmw` = whether a write's stored value is
    /// load-derived (a genuine read-modify-write). A dependent write is trace kind 15 (`Rmw`);
    /// a plain write stays kind 3. Reads ignore `rmw`.
    pub(crate) fn record_shared_access_kind(&mut self, ptr: &Operand, is_write: bool, rmw: bool, p: &SymPointer, state: &PathState) {
        // Hardening: a shared **read** inside an RCU read-side critical section is race-free by
        // the RCU contract — exclude it (writers are still checked).
        if !is_write && state.rcu_depth > 0 {
            return;
        }
        // Sharedness: a global is definitionally shared; a param-derived opaque object may be
        // shared across threads. A stack/TLS/fresh-heap region is thread-local — skip it. A
        // per-CPU accessor's result is thread-local too (hardening).
        let shared = match &p.prov {
            Prov::Region(rid) => {
                matches!(state.regions.get(*rid).map(|r| r.kind), Some(RegionKind::Global))
            }
            Prov::Unknown(_, Some(id)) => !state.percpu.contains(id),
            _ => false,
        };
        if !shared {
            return;
        }
        let Some(class) = crate::lockclass::lock_class_of_arg(&self.lock_classes, ptr) else {
            return;
        };
        let mut lockset: Vec<String> = state.held_classes.values().cloned().collect();
        // An IRQ-disabled access holds a synthetic `@irqoff` lock (G9): consistent irqsave
        // protection then intersects to `@irqoff`; a plain-locked access to the same location
        // lacks it → the data-race pass flags the IRQ-unsafe access.
        if state.irq_off > 0 {
            lockset.push("@irqoff".to_string());
        }
        lockset.sort();
        lockset.dedup();
        // Ordered trace for the interleaving check (read=2, dependent-read=9, write=3), bounded
        // so a huge function does not grow an unbounded trace. A read through a load-derived
        // pointer is address-dependent (`rcu_dereference`-style) and does not reorder.
        if self.race_trace.len() < self.race_trace_cap {
            let kind = if is_write {
                if rmw {
                    15
                } else {
                    3
                }
            } else if matches!(ptr, Operand::Reg(r) if self.load_derived.contains(r)) {
                9
            } else {
                2
            };
            self.race_trace.push((kind, class.clone()));
        }
        self.race_accesses.insert((class, is_write, lockset));
    }

    /// Record a **free** in the interleaving trace (event kind 10) and as a write in the
    /// lockset relation — so a concurrent free-vs-use (cross-thread use-after-free) or two
    /// concurrent frees (cross-thread double-free) are found by the interleaving / data-race
    /// pass. Only for a shareable object (a global or a param-reached heap object).
    pub(crate) fn record_free_event(&mut self, ptr: &Operand, p: &SymPointer, state: &PathState) {
        let shared = match &p.prov {
            Prov::Region(rid) => {
                matches!(state.regions.get(*rid).map(|r| r.kind), Some(RegionKind::Global))
            }
            Prov::Unknown(_, Some(_)) => true,
            _ => false,
        };
        if !shared {
            return;
        }
        let Some(class) = crate::lockclass::lock_class_of_arg(&self.lock_classes, ptr) else {
            return;
        };
        let mut lockset: Vec<String> = state.held_classes.values().cloned().collect();
        lockset.sort();
        lockset.dedup();
        if self.race_trace.len() < self.race_trace_cap {
            self.race_trace.push((10, class.clone()));
        }
        // A free is a write to the object (it invalidates its bytes) — feeds the lockset race.
        self.race_accesses.insert((class, true, lockset));
    }

    /// Record a **typestate transition/requirement on a global-rooted object** in the interleaving
    /// trace (kind 14) for the cross-entry (cross-syscall) analysis. `k`: 0 = set, 1 = require, 2 =
    /// require-not. Only a global-rooted resource (`g:…` / `deref:…g:…`) is streamed — that is the
    /// only state that persists between independent syscall entries; a parameter-local resource is
    /// skipped. The payload encodes `k`, the class, and the interned protocol/state ids, unit-
    /// separated, for `find_cross_entry_typestate` to parse.
    pub(crate) fn record_global_typestate(&mut self, k: u8, val: &Operand, protocol: u32, st: u32) {
        if self.race_trace.len() >= self.race_trace_cap {
            return;
        }
        let Some(class) = crate::lockclass::lock_class_of_arg(&self.lock_classes, val) else {
            return;
        };
        // Global-rooted only: `g:name@off` or any `deref:` chased from one.
        let core = class.trim_start_matches("deref:");
        if !core.starts_with("g:") {
            return;
        }
        self.race_trace
            .push((14, format!("{k}\u{1f}{class}\u{1f}{protocol}\u{1f}{st}")));
    }

    /// The identity a typestate resource operand is keyed by: a pointer handle by its base
    /// object, a scalar (an `fd`) by its symbolic value. `None` for a pointer with no tracked
    /// base (then the resource cannot be named — the transition/obligation is skipped, sound).
    pub(crate) fn res_key(&mut self, op: &Operand, state: &PathState) -> Option<ResKey> {
        match self.eval_value(op, state) {
            SymValue::Ptr(_) => Self::ptr_base_key(&self.eval_value(op, state)).map(ResKey::Ptr),
            SymValue::Scalar(e) => Some(ResKey::Val(e)),
        }
    }

    /// Whether two symbolic pointers **alias the same region/identity** and that region's
    /// provenance lacks `cap` — decomposing a `Prov::Select` (a PHI/`select` join) on either
    /// side into its alternatives. Firing on one alternative is sound: that alternative is a
    /// feasible reaching path (the refutation's feasibility witness confirms it) on which the
    /// in-place-foreign write genuinely holds. This is what lets an in-place op whose src is a
    /// PHI of the (in-place) dst and an out-of-place value still be caught on the in-place arm.
    pub(crate) fn alias_lacks_cap(&mut self, sp: &SymPointer, dp: &SymPointer, cap: u32, state: &PathState) -> bool {
        // Decompose a Select on either side (bounded by the finite pointer structure).
        if let Prov::Select { then_ptr, else_ptr, .. } = &sp.prov {
            let (then_ptr, else_ptr) = ((**then_ptr).clone(), (**else_ptr).clone());
            return self.alias_lacks_cap(&then_ptr, dp, cap, state)
                || self.alias_lacks_cap(&else_ptr, dp, cap, state);
        }
        if let Prov::Select { then_ptr, else_ptr, .. } = &dp.prov {
            let (then_ptr, else_ptr) = ((**then_ptr).clone(), (**else_ptr).clone());
            return self.alias_lacks_cap(sp, &then_ptr, cap, state)
                || self.alias_lacks_cap(sp, &else_ptr, cap, state);
        }
        let same = match (&sp.prov, &dp.prov) {
            (Prov::Region(ra), Prov::Region(rb)) => ra == rb,
            // Same opaque object identity, and the two field offsets CAN be equal. The offset
            // is compared by SATISFIABILITY, not structurally: a `req->src` set from a
            // `phi [in-place-dst, out-of-place]` carries an ITE offset that equals the dst
            // offset only on the in-place edge — a structural `==` misses it, but that edge is
            // a genuine reachable in-place write. `record_temporal` gates the FAIL on
            // bug-finding/exact, so this raises recall without a false PASS (and, in strict
            // mode on an inexact merged path, stays UNKNOWN rather than becoming a false FAIL).
            (Prov::Unknown(_, Some(ia)), Prov::Unknown(_, Some(ib))) => {
                ia == ib && self.offsets_can_be_equal(sp.offset, dp.offset, state)
            }
            _ => false,
        };
        if !same {
            return false;
        }
        let labels = match sp.prov {
            Prov::Region(rid) => {
                state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default()
            }
            Prov::Unknown(_, Some(id)) => state.opaque_labels.get(&id).cloned().unwrap_or_default(),
            _ => FxHashSet::default(),
        };
        self.labels_lack_cap(&labels, cap)
    }

    /// The object-identity key of a pointer value: the region or the opaque id it is based
    /// on. `None` for a non-pointer, a null/derived-from-int pointer, or a `Select` join
    /// (ambiguous base) — callers treat `None` conservatively (e.g. drop the store record).
    pub(crate) fn ptr_base_key(v: &SymValue) -> Option<RefBase> {
        match v {
            SymValue::Ptr(p) => match &p.prov {
                Prov::Region(r) => Some(RefBase::Region(*r)),
                Prov::Unknown(_, Some(id)) => Some(RefBase::Opaque(*id)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether two offset expressions **can** be equal under the current path (not provably
    /// distinct). A structural match is the fast path; otherwise we ask the solver whether
    /// `a != b` is *unprovable* — if we cannot prove them distinct, an in-place aliasing is a
    /// feasible reaching state. Used only for the in-place capability gate, whose FAIL is
    /// gated on bug-finding/exact by `record_temporal`.
    pub(crate) fn offsets_can_be_equal(&mut self, a: ExprId, b: ExprId, state: &PathState) -> bool {
        if a == b {
            return true;
        }
        let ne = self.ctx.cmp(SCmp::Ne, a, b);
        !self.prove(ne, state)
    }

    /// Whether `labels` contains one that the provenance lattice proves does **not** grant
    /// `cap` (a label absent from the lattice grants everything — the sound default).
    pub(crate) fn labels_lack_cap(&self, labels: &FxHashSet<u32>, cap: u32) -> bool {
        labels
            .iter()
            .any(|l| self.prov_grants.get(l).is_some_and(|caps| !caps.contains(&cap)))
    }
}
