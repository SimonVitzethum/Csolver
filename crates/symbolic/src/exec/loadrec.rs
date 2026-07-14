use super::*;

impl Explorer<'_> {
    /// Resolve a load by scanning the symbolic store most-recent-first: a
    /// must-aliasing store supplies the value, a may-aliasing store makes the
    /// value ambiguous (fresh unknown), a no-aliasing store is skipped. This is
    /// what preserves a pointer's provenance across a store/load round-trip.
    /// Resolve a load against the store log, reporting both the value and its
    /// [`LoadOrigin`]. A value not pinned by a `Must`-aliasing store is a fresh
    /// unknown (an over-approximation); the caller drops `exact` for it, since a
    /// violating model could assign that unknown a value memory never holds.
    pub(crate) fn load_value(
        &mut self,
        p: &SymPointer,
        asize: u64,
        ty: &Type,
        state: &mut PathState,
    ) -> (SymValue, LoadOrigin) {
        for k in (0..state.heap.len()).rev() {
            let rec_size = state.heap[k].size;
            let target = state.heap[k].target.clone();
            match self.alias_check(&target, p, rec_size, asize, state) {
                AliasResult::No => continue,
                AliasResult::Must => return (state.heap[k].value.clone(), LoadOrigin::Stored),
                AliasResult::May => return (self.fresh_value(ty, POrigin::Load), LoadOrigin::Uncertain),
            }
        }
        // A load from a user-controlled region (filled by `copy_from_user`) reads
        // untrusted data: a *genuine adversarial input*, so it may drive a refutable
        // overflow. Model a scalar as a genuine symbol (like a parameter) rather than
        // an over-approximated one. Reported as `Stored` so the path stays exact —
        // the value is genuinely free, not an over-approximation to be distrusted.
        let user = matches!(p.prov, Prov::Region(rid) if state.regions.get(rid).is_some_and(|r| r.user_controlled));
        if user && !ty.is_ptr() {
            return (SymValue::Scalar(self.fresh_genuine_scalar(type_width(ty))), LoadOrigin::Stored);
        }
        // Read-consistency: no store aliases this location, so it is unwritten. Two reads of
        // the same never-written `(base, concrete offset, width)` must agree (unwritten memory
        // holds one fixed unknown value). Reuse the value first materialized here; materialize
        // (and cache) it otherwise. Only for a concrete offset — a symbolic offset stays a
        // fresh over-approximation. The cache is dropped on every heap havoc.
        //
        // The base is a region id OR an **opaque object id** (an interior field of a call
        // result / parameter, e.g. `areq->src` and `areq->dst` read twice off the same opaque
        // request) placed in a disjoint id namespace so the two spaces never collide. This is
        // what lets two loads of the same opaque field alias — sound: the returned value is a
        // fresh unknown either way, so read-consistency can only ADD an equality between two
        // reads of one location, never a false PASS (it makes nothing wrongly provable) nor a
        // false FAIL (the two reads genuinely are the same location, hence the same value).
        const OPAQUE_NS: usize = 1 << 48;
        let base = match p.prov {
            Prov::Region(rid) => Some(rid),
            Prov::Unknown(_, Some(id)) => Some((id as usize) | OPAQUE_NS),
            _ => None,
        };
        if let (Some(base), Some(off)) = (base, self.ctx.as_const(p.offset).map(|bv| bv.unsigned())) {
            let key = (base, off, ty.size_bytes(&LAYOUT).unwrap_or(0) as u32);
            if let Some(v) = state.unwritten_reads.get(&key) {
                return (v.clone(), LoadOrigin::Unwritten);
            }
            let v = self.fresh_value(ty, POrigin::Load);
            state.unwritten_reads.insert(key, v.clone());
            return (v, LoadOrigin::Unwritten);
        }
        (self.fresh_value(ty, POrigin::Load), LoadOrigin::Unwritten)
    }

    /// A fresh **genuine** input symbol (named `user…`, treated like a parameter by
    /// [`Explorer::goal_is_genuine`]): an untrusted value an attacker fully controls,
    /// so a violation it drives is genuinely reachable and refutable.
    pub(crate) fn fresh_genuine_scalar(&mut self, width: u32) -> ExprId {
        let name = format!("user{}", self.fresh);
        self.fresh += 1;
        self.ctx.symbol(name, width)
    }

    /// Zero-extend a scalar to pointer width (identity if already that wide) so a
    /// narrower length — a `zext` the executor modelled as width-preserving — takes
    /// part in pointer-width bounds arithmetic without a width mismatch.
    pub(crate) fn widen_to_ptr(&mut self, e: ExprId) -> ExprId {
        self.ctx.zext(e, PTR_WIDTH)
    }

    /// Does `p` point into a freshly-allocated region (one with no caller
    /// contract)? Such a region's bytes are *uninitialized* until written.
    pub(crate) fn is_fresh_alloc(&self, p: &SymPointer, state: &PathState) -> bool {
        match &p.prov {
            // An `assumed`-size region (a machine-code stack frame or a VLA) may hold
            // data initialized *outside* the tracked extent — a caller-passed stack
            // argument above `rbp`, say — so a read of a byte we did not see written is
            // not a definite uninitialized-read bug: leave it UNKNOWN, never refute.
            Prov::Region(rid) => {
                state.regions.get(*rid).is_some_and(|r| r.contract.is_none() && !r.assumed)
            }
            _ => false,
        }
    }

    /// Record a definite read of uninitialized memory as a `ValidRead`
    /// refutation (UB: reading never-written allocated bytes). Overwrites any
    /// permission-worded predicate from `check_access` so the report names the
    /// real cause.
    pub(crate) fn record_uninit_read(&mut self, block: BlockId, idx: usize, model: Model) {
        let entry = self
            .mem
            .entry((block, idx, SafetyProperty::ValidRead))
            .or_insert(MemAgg {
                all_proven: true,
                refutation: None,
                predicate: String::new(),
                residual: String::new(),
            });
        entry.all_proven = false;
        entry.refutation.get_or_insert(model);
        entry.predicate = "reads initialized memory".to_string();
        entry.residual = "reads uninitialized (never-written) freshly-allocated memory".to_string();
    }

    /// Whether the range `[base, base+n)` contains a chunk that **no store definitely
    /// determines** — i.e. some copied byte is uninitialized. Scans in 8-byte words (plus
    /// a byte tail), bounded to a fixed number of chunks so a huge buffer cannot blow up
    /// the check; a `LoadOrigin::Unwritten` chunk (every store `No`-aliases it) is a
    /// definite never-written region. Only *definite* uninit counts (a `May`/`Stored`
    /// chunk does not), so this never fabricates a leak.
    pub(crate) fn range_has_unwritten_bytes(&mut self, base: &SymPointer, n: u64, state: &mut PathState) -> bool {
        const MAX_CHUNKS: u64 = 512; // cap the scan (covers 4 KiB at 8-byte words)
        let word = 8u64;
        let full = n / word;
        let tail = n % word;
        let scanned = full.min(MAX_CHUNKS);
        for k in 0..scanned {
            let delta = self.ctx.int(PTR_WIDTH, (k * word) as u128);
            let off = self.ctx.bin(BvOp::Add, base.offset, delta);
            let p = SymPointer { prov: base.prov.clone(), offset: off, align: 1, borrow: None };
            let (_, origin) = self.load_value(&p, word, &Type::int(64), state);
            if matches!(origin, LoadOrigin::Unwritten) {
                return true;
            }
        }
        // The sub-word tail (only when the whole-word scan wasn't truncated).
        if tail > 0 && full <= MAX_CHUNKS {
            let delta = self.ctx.int(PTR_WIDTH, (full * word) as u128);
            let off = self.ctx.bin(BvOp::Add, base.offset, delta);
            let p = SymPointer { prov: base.prov.clone(), offset: off, align: 1, borrow: None };
            let ty = Type::int((tail * 8) as u32);
            let (_, origin) = self.load_value(&p, tail, &ty, state);
            if matches!(origin, LoadOrigin::Unwritten) {
                return true;
            }
        }
        false
    }

    /// Record a `copy_to_user` disclosure of never-written source bytes as a
    /// `NoInfoLeak` refutation (a kernel information leak: uninitialized memory
    /// copied out to userspace).
    pub(crate) fn record_info_leak(&mut self, block: BlockId, idx: usize, model: Model) {
        let entry = self
            .mem
            .entry((block, idx, SafetyProperty::NoInfoLeak))
            .or_insert(MemAgg {
                all_proven: true,
                refutation: None,
                predicate: String::new(),
                residual: String::new(),
            });
        entry.all_proven = false;
        entry.refutation.get_or_insert(model);
        entry.predicate = "copies only initialized bytes to userspace".to_string();
        entry.residual =
            "discloses uninitialized (never-written) kernel memory to userspace".to_string();
    }

    /// Classify the alias relationship between two accesses `a` (`sizea` bytes)
    /// and `b` (`sizeb` bytes) under the current path condition.
    pub(crate) fn alias_check(
        &mut self,
        a: &SymPointer,
        b: &SymPointer,
        sizea: u64,
        sizeb: u64,
        state: &PathState,
    ) -> AliasResult {
        match (&a.prov, &b.prov) {
            // Same allocation: decide by offsets.
            (Prov::Region(r1), Prov::Region(r2)) if r1 == r2 => {
                self.offsets_alias(a, b, sizea, sizeb, state)
            }
            // Distinct allocations never alias.
            (Prov::Region(_), Prov::Region(_)) => AliasResult::No,
            // Same opaque object identity (the unique `Prov::Unknown` id minted per opaque
            // pointer, which flows through `gep`/copy — the same identity `opaque_labels` and
            // `RefBase::Opaque` key on): two accesses to the same opaque object decide by
            // offset exactly like a region, so a field store into an opaque base
            // (`store p, areq->dst`) is read back (`load areq->dst`) — read-your-writes over
            // an opaque object. Sound: an intervening writing call clears the store list
            // (`heap.clear()`), so a stale store is never forwarded across a havoc.
            (Prov::Unknown(_, Some(i1)), Prov::Unknown(_, Some(i2))) if i1 == i2 => {
                self.offsets_alias(a, b, sizea, sizeb, state)
            }
            // Distinct or unidentified opaque / null provenance: be conservative.
            _ => AliasResult::May,
        }
    }

    /// Decide aliasing of two pointers already known to address the **same** object
    /// (same region or same opaque identity) purely by their offsets and access sizes.
    pub(crate) fn offsets_alias(
        &mut self,
        a: &SymPointer,
        b: &SymPointer,
        sizea: u64,
        sizeb: u64,
        state: &PathState,
    ) -> AliasResult {
        let eq = self.ctx.cmp(SCmp::Eq, a.offset, b.offset);
        if sizea >= sizeb && self.prove(eq, state) {
            return AliasResult::Must;
        }
        let asz = self.ctx.int(PTR_WIDTH, sizea as u128);
        let bsz = self.ctx.int(PTR_WIDTH, sizeb as u128);
        let a_end = self.ctx.bin(BvOp::Add, a.offset, asz);
        let b_end = self.ctx.bin(BvOp::Add, b.offset, bsz);
        let a_before_b = self.ctx.cmp(SCmp::Sle, a_end, b.offset);
        let b_before_a = self.ctx.cmp(SCmp::Sle, b_end, a.offset);
        if self.prove(a_before_b, state) || self.prove(b_before_a, state) {
            return AliasResult::No;
        }
        AliasResult::May
    }

    pub(crate) fn record(
        &mut self,
        block: BlockId,
        idx: usize,
        prop: SafetyProperty,
        proven: bool,
        proven_desc: &str,
        residual: &str,
    ) {
        let entry = self.mem.entry((block, idx, prop)).or_insert(MemAgg {
            all_proven: true,
            refutation: None,
            predicate: proven_desc.to_string(),
            residual: residual.to_string(),
        });
        entry.all_proven &= proven;
    }

    /// Record a memory obligation decided as [`Decision`] (carrying a refutation
    /// model when definitely violated).
    /// A `return` of a pointer into this frame's own stack is a dangling return:
    /// the storage dies the instant the frame is torn down, so the caller holds a
    /// pointer to freed stack (use-after-return). Recorded at the terminator slot
    /// (`insts.len()`), bug-finding-only. A stack region can only be a local
    /// `alloca` of this function whose address escaped (an un-promoted alloca), so
    /// a stack-provenance return is a definite defect — no interprocedural analysis
    /// needed. Params/heap (`Region(Heap)`) and globals are never flagged.
    pub(crate) fn check_return(&mut self, block: BlockId, op: &Operand, state: &PathState) {
        let idx = self.f.block(block).map_or(0, |b| b.insts.len());
        // Record the obligation on **every** return, not only on a violation. A scalar cannot
        // dangle, and a pointer that does not resolve into this frame's stack does not either —
        // both are a *proof*, and recording it is what discharges the obligation the verifier
        // enumerates at each `Return(Some(_))`. Recording only the violating case left every
        // **safe** return with no decision at all, so its `no_dangling_deref` obligation fell to
        // `UNKNOWN` ("reached but not decided") and — being one undecided obligation — gated the
        // whole function to `UNKNOWN`. That was the single dominant residual class.
        let dangling = match self.eval_value(op, state) {
            SymValue::Ptr(p) => self.points_into_frame_stack(&p, state),
            SymValue::Scalar(_) => false,
        };
        self.record_temporal(
            (block, idx),
            SafetyProperty::NoDanglingDeref,
            dangling,
            state,
            "does not return a pointer into this frame's stack",
            "returns a pointer into a local stack allocation (dangling after return)",
        );
    }

    /// Whether `p`'s provenance resolves to a stack region of the current frame
    /// (directly, or on either arm of a `select`/PHI join).
    pub(crate) fn points_into_frame_stack(&self, p: &SymPointer, state: &PathState) -> bool {
        match &p.prov {
            Prov::Region(rid) => {
                matches!(state.regions.get(*rid).map(|r| r.kind), Some(RegionKind::Stack))
            }
            Prov::Select { then_ptr, else_ptr, .. } => {
                self.points_into_frame_stack(then_ptr, state)
                    || self.points_into_frame_stack(else_ptr, state)
            }
            _ => false,
        }
    }

    pub(crate) fn record_mem(
        &mut self,
        block: BlockId,
        idx: usize,
        prop: SafetyProperty,
        decision: Decision,
        proven_desc: &str,
        residual: &str,
    ) {
        let entry = self.mem.entry((block, idx, prop)).or_insert(MemAgg {
            all_proven: true,
            refutation: None,
            predicate: proven_desc.to_string(),
            residual: residual.to_string(),
        });
        match decision {
            Decision::Proven => {}
            Decision::Unknown => entry.all_proven = false,
            Decision::Refuted(model) => {
                entry.all_proven = false;
                entry.refutation.get_or_insert(model);
            }
        }
    }

    /// Aggregate a scalar `SafetyCheck` decision across paths.
    pub(crate) fn record_scalar(&mut self, block: BlockId, idx: usize, decision: Decision) {
        let entry = self.scalar.entry((block, idx)).or_insert(ScalarAgg {
            all_proven: true,
            refutation: None,
        });
        match decision {
            Decision::Proven => {}
            Decision::Unknown => entry.all_proven = false,
            Decision::Refuted(model) => {
                entry.all_proven = false;
                entry.refutation.get_or_insert(model);
            }
        }
    }

    // --- expression evaluation ---------------------------------------------
}
