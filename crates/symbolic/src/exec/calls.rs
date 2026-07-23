use super::*;

impl Explorer<'_> {
    /// AA self-deadlock detection (bug-finding). Maintains the per-path set of held
    /// locks by the identity of the lock pointer's base object; re-acquiring a base
    /// already held is a definite deadlock (refuted with a reachability witness). A
    /// release drops the base. Every call records a `DataRace` decision so the
    /// obligation the verifier enumerates (bug-finding only) is never left Open on a
    /// non-lock call. Only external `Callee::Symbol` locks are recognised (the kernel
    /// lock primitives are declarations, not in-TU definitions).
    pub(crate) fn check_lock_call(
        &mut self,
        at: (BlockId, usize),
        callee: &Callee,
        args: &[Operand],
        state: &mut PathState,
    ) {
        let (block, idx) = at;
        // Every call records `TypestateViolation` proven by default (the verifier enumerates it
        // at each `Inst::Call` for the interprocedural refcount check); an actual underflow in
        // `step_call` refutes it. Without this a plain call would leave the obligation Open.
        self.record(block, idx, SafetyProperty::TypestateViolation, true, "the reference count stays non-negative across calls", "");
        let name = match callee {
            Callee::Symbol(n) => n.as_str(),
            _ => {
                self.record(block, idx, SafetyProperty::DataRace, true, "no lock re-acquired while held", "");
                self.record(block, idx, SafetyProperty::SleepInAtomic, true, "no sleeping call while a spinlock is held", "");
                return;
            }
        };
        // The synchronisation classification, collected from the contract files before
        // solving (crates/contracts/data/kernel_sync.contract) — see `crate::sync`.
        let sync = crate::sync::classes();
        // RCU read-side critical section: track nesting depth so a shared read inside it is
        // excluded from the data-race pass (race-free by the RCU contract).
        if sync.rcu_read_lock(name) {
            state.rcu_depth += 1;
        } else if sync.rcu_read_unlock(name) {
            state.rcu_depth = state.rcu_depth.saturating_sub(1);
        }
        // IRQ-disabled section (G9): an access here holds the synthetic `@irqoff` lock, so a
        // location protected against IRQs inconsistently (irqsave here, plain lock there) races.
        if sync.irq_disable(name) {
            state.irq_off += 1;
        } else if sync.irq_enable(name) {
            state.irq_off = state.irq_off.saturating_sub(1);
        }
        let acquire = sync.lock_acquire(name);
        // The lock argument: the contract's declared index for an acquire, arg0 otherwise
        // (the release-drop below inspects every pointer argument anyway).
        let lock_arg = acquire.map_or(0, |s| s.arg);
        let base =
            args.get(lock_arg).map(|a| self.eval_value(a, state)).and_then(|v| Self::ptr_base_key(&v));
        // Sleep-in-atomic: a blocking/sleeping call while a spinlock is *definitely* held is a
        // deadlock/scheduler-corruption bug — refuted with a reachability witness. Every other
        // call records the obligation proven, so it is never left Open.
        if sync.blocking(name) && !state.spin_held.is_empty() {
            self.record_temporal(
                (block, idx),
                SafetyProperty::SleepInAtomic,
                true,
                state,
                "no sleeping call while a spinlock is held",
                "a call that may sleep runs while a spinlock is held (sleep-in-atomic)",
            );
        } else {
            self.record(block, idx, SafetyProperty::SleepInAtomic, true, "no sleeping call while a spinlock is held", "");
        }
        if let Some(spec) = acquire {
            // Lock-order edges (ABBA, G6): name the acquired lock's *class* from its
            // pointer argument, and for every distinct lock class already held on this
            // path emit an ordered edge (held → acquired). A B→A edge somewhere else in
            // the program then closes an ABBA cycle. The base's class is recorded below,
            // so a further nested acquire sees this lock as a predecessor.
            let newclass = args
                .get(lock_arg)
                .and_then(|a| crate::lockclass::lock_class_of_arg(&self.lock_classes, a));
            if let Some(nc) = &newclass {
                for held in state.held_classes.values() {
                    if held != nc {
                        self.lock_edges.insert((held.clone(), nc.clone()));
                    }
                }
                // Ordered interleaving trace: acquire = 0.
                if self.race_trace.len() < self.race_trace_cap {
                    self.race_trace.push((0, nc.clone()));
                }
            }
            match base {
                // Re-acquiring a lock already held on this path: a definite AA deadlock.
                Some(b) if state.locks_held.contains(&b) => {
                    let model = self.feasibility_witness(state);
                    let entry = self.mem.entry((block, idx, SafetyProperty::DataRace)).or_insert(MemAgg {
                        all_proven: true,
                        refutation: None,
                        predicate: "no lock re-acquired while held".to_string(),
                        residual: String::new(),
                    });
                    entry.all_proven = false;
                    if let Some(m) = model {
                        entry.refutation.get_or_insert(m);
                    }
                    entry.residual = "re-acquires a lock already held on this path (AA self-deadlock)".to_string();
                }
                Some(b) => {
                    state.locks_held.insert(b);
                    self.record(block, idx, SafetyProperty::DataRace, true, "no lock re-acquired while held", "");
                }
                // Unknown lock identity: cannot decide — record as proven (a `None`
                // never fabricates a deadlock; it only omits the check). Sound.
                None => self.record(block, idx, SafetyProperty::DataRace, true, "no lock re-acquired while held", ""),
            }
            // Record this lock's class against its base so a nested acquire emits an edge
            // from it, and a matched release drops it.
            if let (Some(b), Some(nc)) = (base, newclass) {
                state.held_classes.insert(b, nc);
            }
            // A **spinning** lock also enters atomic context — track it separately, so a
            // later blocking call is caught (a sleepable `mutex`/`down` is not tracked here).
            if spec.spin {
                if let Some(b) = base {
                    state.spin_held.insert(b);
                }
            }
        } else {
            // Any other call: a call handed a held lock's base MAY release it — a matched
            // unlock (`spin_unlock`/`spin_unlock_irqrestore`/…), an unlock wrapper, or a
            // callee that unlocks internally. Conservatively drop every held base passed to
            // this call as a pointer argument, so a later re-acquire is NOT a false
            // double-lock. Sound: this only ever *forgets* a lock (lower recall), never
            // fabricates one — a genuine `lock(l); … lock(l)` with no intervening call
            // taking `l` still refutes.
            for a in args {
                if let Some(b) = Self::ptr_base_key(&self.eval_value(a, state)) {
                    state.locks_held.remove(&b);
                    state.spin_held.remove(&b);
                    // Ordered interleaving trace: release = 1 (recorded for the dropped class).
                    if let Some(cls) = state.held_classes.remove(&b) {
                        if self.race_trace.len() < self.race_trace_cap {
                            self.race_trace.push((1, cls));
                        }
                    }
                }
            }
            self.record(block, idx, SafetyProperty::DataRace, true, "no lock re-acquired while held", "");
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn step_call(
        &mut self,
        at: (BlockId, usize),
        dst: Option<&RegId>,
        callee: &Callee,
        args: &[Operand],
        ret_ty: &Type,
        ret_ref: Option<RefResult>,
        state: &mut PathState,
    ) {
        let (block, idx) = at;
        let argvals: Vec<SymValue> = args.iter().map(|a| self.eval_value(a, state)).collect();
        // Resolve the callee. An indirect call whose target register was devirtualised
        // from a constant ops-struct load (see `global_fnptrs`) is treated as a direct
        // call to that function: its summary gives precise effects (writes/frees/return
        // provenance) instead of the opaque havoc an unknown call would force. Recorded
        // as an assumption — the resolution trusts the constant table's field layout.
        let resolved_fid = match callee {
            Callee::Direct(fid) => Some(*fid),
            Callee::Indirect(Operand::Reg(r)) => {
                let hit = state.fn_ptrs.get(r).copied();
                if hit.is_some() {
                    self.assumptions.insert("devirtualized-indirect-call");
                }
                hit
            }
            _ => None,
        };
        // Closed-world points-to devirtualisation (call-target resolution ONLY). When the region-
        // precise `fn_ptrs` above did not resolve, the whole-program points-to may know the single
        // function this indirect target register designates (a heap/param `obj->ops->fn()`). We use
        // it purely to pick the callee — the loaded pointer keeps its real (opaque) provenance, so
        // its null/uninit/bounds checks below are untouched: a genuinely null/uninitialised target
        // still faults first, and the resolved effect is used only on the paths that proceed.
        let devirt_name: Option<String> = match callee {
            Callee::Indirect(Operand::Reg(r)) if resolved_fid.is_none() => {
                self.devirt.get(r).cloned()
            }
            _ => None,
        };
        if devirt_name.is_some() {
            self.assumptions.insert("closed-world-devirt");
        }
        // Valid indirect target (a CFI slice): an indirect call is a definite control-flow-
        // integrity bug when the target pointer is provably (a) **null** (a null/uninit
        // callback) or (b) into a **stack or heap region** — executing data as code (the
        // classic jump-to-injected-shellcode). Stack/heap are never legitimately executable
        // (a trampoline needs an explicitly mprotect'd stack we do not model), so a data-
        // region target is a genuine violation; a devirtualised, symbol, or opaque
        // (unknown-but-assumed-valid) pointer is NOT flagged. Bug-finding-only, refuted with a
        // witness on a feasible path.
        if let Callee::Indirect(op) = callee {
            let mut violation = false;
            if resolved_fid.is_none() && devirt_name.is_none() {
                if let SymValue::Ptr(p) = self.eval_value(op, state) {
                    violation = match &p.prov {
                        Prov::Null => true,
                        Prov::Region(rid) => matches!(
                            state.regions.get(*rid).map(|r| r.kind),
                            Some(RegionKind::Stack | RegionKind::Heap)
                        ),
                        _ => false,
                    };
                }
            }
            self.record_temporal(
                (block, idx),
                SafetyProperty::ValidIndirectTarget,
                violation,
                state,
                "indirect call target is a valid function pointer",
                "indirect call through a null pointer or into non-executable stack/heap data",
            );
        }

        let summary = resolved_fid
            .and_then(|fid| self.summaries.get(&fid).cloned())
            // Whole-program: a cross-file `Symbol(name)` call resolves to the remote
            // callee's summary by name, so its effects are modelled precisely instead
            // of havoc'd. Sound: a name with no summary (a true external / unresolved)
            // still falls through to the opaque havoc below.
            .or_else(|| match callee {
                Callee::Symbol(name) => self.name_summaries.get(name).cloned(),
                _ => None,
            })
            // A points-to-devirtualised indirect call resolves to its target's whole-program
            // summary by name (precise effects instead of havoc). A name with no summary — e.g. a
            // file-local `static` callee, excluded from the name-keyed summaries to avoid cross-file
            // collisions — still falls through to the opaque havoc below (sound, just less precise).
            .or_else(|| devirt_name.as_ref().and_then(|n| self.name_summaries.get(n).cloned()));

        // Double-free through a freeing *wrapper*: a callee that definitely frees its
        // parameter `k` (`Summary.frees_arg`) re-frees a base an earlier freeing call
        // already freed. Done BEFORE `state.exact` is cleared below, so it refutes with a
        // witness on an exact path exactly like a `Dealloc` double-free; then the freed
        // base is recorded. Every other call records `NoDoubleFree` proven, so the
        // per-call obligation is never left Open. (The coarse `frees` havoc below is
        // unchanged, so liveness/PASS is unaffected — this only *adds* a definite check.)
        match summary.as_ref().and_then(|s| s.frees_arg) {
            Some(k) => match argvals.get(k).and_then(Self::ptr_base_key) {
                Some(b) => {
                    // Cross-thread free/use race (a freeing wrapper call, e.g. `kfree`).
                    if let (Some(op), Some(SymValue::Ptr(pp))) = (args.get(k), argvals.get(k)) {
                        let pp = pp.clone();
                        self.record_free_event(op, &pp, state);
                    }
                    let dup = state.freed_bases.contains(&b);
                    self.record_temporal((block, idx), SafetyProperty::NoDoubleFree, dup, state, "no double free through freeing calls", "re-frees a pointer an earlier freeing call already freed");
                    state.freed_bases.insert(b);
                }
                None => self.record(block, idx, SafetyProperty::NoDoubleFree, true, "no double free through freeing calls", ""),
            },
            None => self.record(block, idx, SafetyProperty::NoDoubleFree, true, "no double free through freeing calls", ""),
        }

        // Interprocedural reference count (get/put lifetime protocols across functions): apply
        // the callee's net refcount effect on each pointer argument's object. A decrement that
        // takes the count below zero is an underflow (a premature free → use-after-free), caught
        // even when the `get` and `put` live in different functions / syscalls.
        if let Some(effs) = summary.as_ref().map(|s| s.refcount_effect.clone()) {
            for (param, protocol, delta) in effs {
                let Some(SymValue::Ptr(pp)) = argvals.get(param) else { continue };
                let Some(key) = Self::ptr_base_key(&SymValue::Ptr(pp.clone())).map(ResKey::Ptr)
                else {
                    continue;
                };
                if delta >= 0 {
                    *state.refcounts.entry((key, protocol)).or_insert(0) += delta;
                } else if let Some(&c) = state.refcounts.get(&(key, protocol)) {
                    // A net put only underflows a count *established in this scope* (a prior get);
                    // an untracked param the caller holds is left alone (sound).
                    state.refcounts.insert((key, protocol), c + delta);
                    if c + delta < 0 {
                        self.record_temporal(
                            (block, idx),
                            SafetyProperty::TypestateViolation,
                            true,
                            state,
                            "the reference count stays non-negative across calls",
                            "a cross-function reference-count put underflows (premature free / use-after-free)",
                        );
                    }
                }
            }
        }

        // A call is an over-approximation point (havoc'd heap/return unless a
        // precise summary applies); conservatively mark the path inexact so we
        // never refute through a call. Proofs are unaffected (this only gates
        // refutation, not PASS). This clearing — together with the loop-header and
        // path-merge clearing — is the **load-bearing soundness gate**: refuting on an
        // inexact path (where the symbolic state is an over-approximation) would fabricate
        // false counterexamples, so strict `verify` deliberately trades recall for it and
        // `--bugs` re-widens refutation only to genuine-input goals. It cannot be relaxed
        // in general without breaking soundness (see docs/soundness-invariants.md).
        state.exact = false;

        // Effects: a writing or freeing callee invalidates the symbolic heap;
        // a *freeing* callee additionally invalidates region liveness (we do
        // not know which region it freed, so no region's liveness can be proved
        // afterwards). Without this, a use after a freeing call would be a false
        // PASS. A **contracted reference region** (`&[T]`/`&T`/`&mut T`) is
        // *borrowed*, though: the caller holds the borrow for the call's whole
        // duration, so the callee cannot deallocate it — its liveness survives
        // the call. Only *owned* regions (a local `alloc`, `contract == None`)
        // can be moved into and freed by a callee. (Without this a `&[T]` passed
        // to any helper — e.g. `s.is_empty()` — would defeat every later access.)
        // Register-only inline asm (`<inline asm nomem>`, decided from its constraint
        // string by the frontend: no memory clobber, no output memory operand) writes and
        // frees no tracked memory — so it does NOT havoc the heap/provenance, unlike an
        // unknown call. Sound: a memory-clobbering asm keeps the `<inline asm>` marker and
        // the full havoc below.
        let asm = matches!(callee, Callee::Symbol(n) if n.starts_with("<inline asm"));
        let nomem_asm = matches!(callee, Callee::Symbol(n) if n == "<inline asm nomem>");
        let (writes, frees) = if nomem_asm {
            (false, false)
        } else if asm {
            // A memory-clobbering inline asm (`~{memory}`) may WRITE memory but does not free —
            // so it havocs the heap yet must not be treated as a freeing call (which would
            // false-flag a later `kfree` of the same object as a double-free).
            (true, false)
        } else {
            summary.as_ref().map_or((true, true), |s| (s.writes, s.frees))
        };
        if writes || frees {
            // In BUG-FINDING mode, assume an opaque call writes only through the objects
            // reachable from its pointer arguments: preserve store records whose target
            // object is identity-disjoint from every argument (so field provenance set up
            // before an unrelated helper — a refcount warn / atomic-op asm on a *different*
            // object — survives to a later in-place check). This is a recall heuristic
            // (a callee could in principle reach an object via a global or a nested pointer),
            // surfaced as an assumption; strict `verify` keeps the fully-sound havoc.
            if self.bug_finding {
                let arg_bases: HashSet<RefBase> =
                    argvals.iter().filter_map(Self::ptr_base_key).collect();
                let before = state.heap.len();
                state
                    .heap
                    .retain(|rec| Self::ptr_base_key(&SymValue::Ptr(rec.target.clone()))
                        .is_some_and(|b| !arg_bases.contains(&b)));
                if state.heap.len() != before {
                    self.assumptions.insert("opaque-call-writes-through-args-only");
                }
            } else {
                state.heap.clear();
            }
            // The precision caches are conservatively dropped regardless (cheap to rebuild;
            // read-your-writes for the in-place check runs off the store list above).
            state.unwritten_reads.clear();
            state.ref_regions.clear();
        }
        if frees {
            for r in &mut state.regions {
                // A callee can only free *heap* memory it was handed ownership
                // of. Contracted regions are borrowed for the call's duration,
                // and freeing a stack region is UB in the callee — refuted there
                // by `check_dealloc`'s non-heap check (the guarantee this
                // assumption composes with). So a local alloca's liveness
                // survives every call.
                if r.state == LifetimeState::Live
                    && r.contract.is_none()
                    && matches!(r.kind, RegionKind::Heap)
                {
                    r.state = LifetimeState::Freed;
                }
            }
        }

        // Provenance transfer: the callee's summary records how a call moves provenance
        // labels between its pointer arguments (a wrapper around a `sg_set_page`-style
        // primitive, derived without a hand-written contract). Apply it to the actual
        // argument regions, so a foreign element propagates through the wrapper.
        if let Some(prov) = summary.as_ref().map(|s| s.prov.clone()) {
            self.apply_prov_transfer(&prov, &argvals, state);
        }

        // Out-parameter stack escape: the callee unconditionally stored the address of one of
        // its own (now-popped) stack locals through parameter K (`*out = &x`). Model that by
        // storing a dangling pointer (into a fresh already-freed region) at the argument's
        // location, so the caller reading it back and dereferencing is a definite use-after-free.
        if let Some(escapes) = summary.as_ref().map(|s| s.escapes_stack.clone()) {
            for k in escapes {
                if let Some(SymValue::Ptr(target)) = argvals.get(k) {
                    let rid = self.materialize_freed_region(state);
                    let dangling = SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: 1,
                        borrow: None,
                    });
                    state.heap.push(StoreRecord {
                        target: target.clone(),
                        value: dangling,
                        size: (PTR_WIDTH / 8) as u64,
                    });
                }
            }
        }

        if let Some(d) = dst {
            let value = match summary.as_ref().map(|s| &s.ret) {
                Some(RetSummary::PtrFromArg { arg, offset }) => {
                    self.instantiate_ptr(*arg, offset, &argvals, ret_ty)
                }
                Some(RetSummary::Scalar(aff)) => {
                    SymValue::Scalar(self.instantiate_affine(aff, &argvals))
                }
                // The callee returns a pointer into its own stack frame on every path;
                // that frame is popped at the return, so the result is dangling here.
                // Materialise it as an already-freed region — a caller deref is then a
                // definite use-after-free (the interprocedural face of NoDanglingDeref).
                Some(RetSummary::DanglingStack) => {
                    let rid = self.materialize_freed_region(state);
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: 1,
                        borrow: None,
                    })
                }
                // The callee returns a fresh heap allocation on every path (an allocator
                // wrapper): hand the caller a live heap region of the recovered size, so its
                // accesses are checked instead of falling to an opaque pointer. Rests on
                // `alloc-succeeds`, exactly like a direct `kmalloc`.
                Some(&RetSummary::Alloc { size }) => {
                    self.assumptions.insert(ALLOC_SUCCEEDS);
                    let rid = self.materialize_heap_region(size, state);
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: 1,
                        borrow: None,
                    })
                }
                // The callee returns a valid typed reference (a field accessor,
                // `return sk->sk_prot;`) on every path — the frontend recovered the pointee
                // size as a `RefWitness`. Hand the caller a sized valid-reference region (the
                // same region the `RefWitness` arm builds), so accesses through the result are
                // decided instead of the opaque `POrigin::Call`. A raw-pointer field (`assumed`)
                // is valid only under `--assume-valid-params`; without the opt-in the call
                // still havocs (no false PASS). A real `&T` field is unconditional.
                Some(&RetSummary::ValidRef { size, align, writable, assumed }) => {
                    if assumed && !self.assume_valid_params {
                        self.fresh_value(ret_ty, POrigin::Call)
                    } else {
                        if assumed {
                            self.assumptions.insert(PARAM_VALID);
                        }
                        let rid = self.materialize_ref_region(size, writable, assumed, state);
                        SymValue::Ptr(SymPointer {
                            prov: Prov::Region(rid),
                            offset: self.ctx.int(PTR_WIDTH, 0),
                            align: (align as u64).max(1),
                            borrow: None,
                        })
                    }
                }
                // No precise summary, but the result type is a reference: it is
                // valid by Rust's type invariant (a safe callee cannot return a
                // dangling `&T`). Materialise a valid-reference region instead of
                // an opaque pointer — the interprocedural counterpart of the
                // by-value-aggregate `RefWitness`.
                None if ret_ref.is_some() => {
                    let RefResult { size, writable } = ret_ref.unwrap_or(RefResult {
                        size: None,
                        writable: false,
                    });
                    let rid = self.materialize_ref_region(size, writable, false, state);
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: 1,
                        borrow: None,
                    })
                }
                // Opt-in: assume an unsummarised call's pointer result is a valid pointer
                // (external/unanalysed callee — the dominant `opaque call result` cause). A
                // non-null live region of *unknown* size (bounds prove-only, so no false FAIL
                // from a guessed size). Unsound in general (a call may return null / an error
                // pointer); surfaced as `valid-returns`. Non-pointer results stay scalar.
                _ if self.limits.assume_valid_returns && ret_ty.is_ptr() => {
                    self.assumptions.insert("valid-returns");
                    let rid = self.materialize_ref_region(None, true, true, state);
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: 1,
                        borrow: None,
                    })
                }
                _ => self.fresh_value(ret_ty, POrigin::Call),
            };
            // Typed-pointer sizing for a **call result**: an unsummarised callee's pointer that
            // the caller then indexes as `gep %struct.T, ptr %r` designates a `struct T` of known
            // size (`Module::reg_ptr_hints`). Give it a sized region under `--assume-valid-params`
            // — the same rule as a loaded field pointer or an `inttoptr` — so accesses through it
            // are decided instead of falling to the opaque `POrigin::Call` (the dominant residual).
            // A precise summary (`PtrFromArg`/`Alloc`/…) already produced a region, which passes
            // through untouched; only an *opaque* result is sized.
            let value = self.size_hinted_pointer(*d, value, state);
            state.env.insert(*d, value);
        }
    }

    /// Create a fresh live region modelling a valid reference (`&T`/`&mut T`):
    /// exact pointee size (refutable) or unknown size (prove-only), readable and
    /// writable per mutability, resting on the `valid-reference` assumption. The
    /// same region shape [`Inst::RefWitness`] builds; returns the region id.
    pub(crate) fn materialize_ref_region(
        &mut self,
        size: Option<u64>,
        writable: bool,
        assumed: bool,
        state: &mut PathState,
    ) -> usize {
        let (size_e, nowrap) = match size {
            Some(n) => {
                let truth = self.ctx.boolean(true);
                (self.ctx.int(PTR_WIDTH, n as u128), Some(truth))
            }
            None => (self.fresh_scalar(PTR_WIDTH), None),
        };
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let nonneg = self.ctx.cmp(SCmp::Sle, zero, size_e);
        state.facts.push(nonneg);
        let rid = state.regions.len();
        state.regions.push(SymRegion {
            kind: RegionKind::Global,
            size: size_e,
            base_align: 1,
            state: LifetimeState::Live,
            perms: Permissions { read: true, write: writable, exec: false },
            contract: Some(VALID_REFERENCE),
            size_nowrap: nowrap,
            sentinel: None,
            user_controlled: false,
            assumed,
            prov_labels: FxHashSet::default(),
        });
        rid
    }

    /// **Typed-pointer sizing** (opt-in `--assume-valid-params`): if `dst`'s register the
    /// frontend typed (`Module::reg_ptr_hints` — from the `getelementptr` that indexes it, or a
    /// DWARF local's declared type) and `v` is an *opaque* pointer, replace it with a sized
    /// `assumed` region of that type. This decides accesses through it (bounds / null / alignment
    /// / liveness) instead of leaving them UNKNOWN, and it is what covers the pervasive kernel
    /// idioms whose result is typed by its use: a **loaded** field pointer, an **`inttoptr`**
    /// result (`current` read from the per-cpu base), and a **`container_of`** result (a
    /// backward-offset pointer used as `struct T *`). Non-opaque values (a real region already
    /// recovered) pass through. `assumed` ⇒ a constant offset past the recovered size is not
    /// refuted (no false FAIL when the object is embedded in a larger one); only a genuine
    /// input-driven overrun is.
    pub(crate) fn size_hinted_pointer(&mut self, dst: RegId, v: SymValue, state: &mut PathState) -> SymValue {
        if !self.limits.assume_valid_params
            || !matches!(v, SymValue::Ptr(SymPointer { prov: Prov::Unknown(..), .. }))
        {
            return v;
        }
        let Some(hint) = self.reg_ptr_hints.get(&dst).copied() else {
            return v;
        };
        // **container_of / intrusive-list member** (a hand-rolled walk whose container carries no
        // `struct T` gep): the pointer is a member at `container_offset` inside a `container_size`-
        // byte node. Materialise the *whole node* and place the pointer at that offset, so the
        // backward `container_of` subtraction (`ptr - container_offset`) lands at the node base
        // (in-object). The node validity/size rests on the same `--assume-valid-params` opt-in.
        if let Some((csize, coff)) = hint.container() {
            self.assumptions.insert(PARAM_VALID);
            let rid = self.materialize_ref_region(Some(csize), true, true, state);
            return SymValue::Ptr(SymPointer {
                prov: Prov::Region(rid),
                offset: self.ctx.int(PTR_WIDTH, coff as u128),
                align: 1,
                borrow: None,
            });
        }
        if hint.size == 0 {
            return v;
        }
        self.assumptions.insert(PARAM_VALID);
        let tail = self.limits.assume_struct_tail && hint.tail > hint.size;
        if tail {
            self.assumptions.insert(STRUCT_TAIL);
        }
        let rid = self.materialize_ref_region(Some(hint.region_size(tail)), true, true, state);
        let align = hint.region_align();
        state.regions[rid].base_align = align;
        SymValue::Ptr(SymPointer {
            prov: Prov::Region(rid),
            offset: self.ctx.int(PTR_WIDTH, 0),
            align,
            borrow: None,
        })
    }

    /// Create a fresh **live heap region** modelling the result of an allocator wrapper
    /// (`RetSummary::Alloc`): `size` bytes when known (bounds then refutable), else a fresh
    /// non-negative unknown size (bounds prove-only). Read+write, live, non-null. In flat
    /// machine-code memory (a binary front-end) bounds stay prove-only, mirroring the direct
    /// heap-alloc rule (`ExecLimits::flat_memory`) so a heap OOB is not refuted where the
    /// register model cannot reconstruct the bounds guard.
    pub(crate) fn materialize_heap_region(&mut self, size: Option<u64>, state: &mut PathState) -> usize {
        let (size_e, mut nowrap) = match size {
            Some(n) => (self.ctx.int(PTR_WIDTH, n as u128), Some(self.ctx.boolean(true))),
            None => (self.fresh_scalar(PTR_WIDTH), None),
        };
        if self.limits.flat_memory {
            nowrap = None;
        }
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let nonneg = self.ctx.cmp(SCmp::Sle, zero, size_e);
        state.facts.push(nonneg);
        let rid = state.regions.len();
        state.regions.push(SymRegion {
            kind: RegionKind::Heap,
            size: size_e,
            base_align: 1,
            state: LifetimeState::Live,
            perms: Permissions { read: true, write: true, exec: false },
            contract: None,
            size_nowrap: nowrap,
            sentinel: None,
            user_controlled: false,
            assumed: false,
            prov_labels: FxHashSet::default(),
        });
        rid
    }

    /// Create a fresh region that is **already freed**, modelling a pointer a callee
    /// returned into its own (now-popped) stack frame. Sized by a fresh non-negative
    /// scalar (the size is irrelevant — any deref refutes on liveness first). A load or
    /// store through the returned pointer is a definite use-after-free.
    pub(crate) fn materialize_freed_region(&mut self, state: &mut PathState) -> usize {
        let size_e = self.fresh_scalar(PTR_WIDTH);
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let nonneg = self.ctx.cmp(SCmp::Sle, zero, size_e);
        state.facts.push(nonneg);
        let rid = state.regions.len();
        state.regions.push(SymRegion {
            kind: RegionKind::Stack,
            size: size_e,
            base_align: 1,
            state: LifetimeState::Freed,
            perms: Permissions { read: true, write: true, exec: false },
            contract: None,
            size_nowrap: None,
            sentinel: None,
            user_controlled: false,
            assumed: false,
            prov_labels: FxHashSet::default(),
        });
        rid
    }

    /// Rebuild a pointer return value `arg + offset(args)`, keeping `arg`'s
    /// provenance.
    pub(crate) fn instantiate_ptr(
        &mut self,
        arg: usize,
        offset: &Affine,
        argvals: &[SymValue],
        ret_ty: &Type,
    ) -> SymValue {
        match argvals.get(arg) {
            Some(SymValue::Ptr(base)) => {
                let delta = self.instantiate_affine(offset, argvals);
                let new_off = self.ctx.bin(BvOp::Add, base.offset, delta);
                SymValue::Ptr(SymPointer {
                    prov: base.prov.clone(),
                    offset: new_off,
                    align: base.align,
                    borrow: base.borrow, // a summarized offset stays within the same borrow
                })
            }
            _ => self.fresh_value(ret_ty, POrigin::Call),
        }
    }

    /// Build the expression `constant + Σ coeff_k · arg_k` in the solver context.
    pub(crate) fn instantiate_affine(&mut self, aff: &Affine, argvals: &[SymValue]) -> ExprId {
        let mut acc = self.const_expr(aff.constant);
        for (&k, &coeff) in &aff.terms {
            let arg = match argvals.get(k) {
                Some(SymValue::Scalar(e)) => *e,
                _ => self.fresh_scalar(PTR_WIDTH),
            };
            let c = self.const_expr(coeff);
            let term = self.ctx.bin(BvOp::Mul, arg, c);
            acc = self.ctx.bin(BvOp::Add, acc, term);
        }
        acc
    }

    /// A signed integer constant as a `PTR_WIDTH` expression (faithful for
    /// negatives via subtraction).
    pub(crate) fn const_expr(&mut self, v: i128) -> ExprId {
        if v >= 0 {
            self.ctx.int(PTR_WIDTH, v as u128)
        } else {
            let zero = self.ctx.int(PTR_WIDTH, 0);
            let mag = self.ctx.int(PTR_WIDTH, (-v) as u128);
            self.ctx.bin(BvOp::Sub, zero, mag)
        }
    }

    // --- obligation decisions ----------------------------------------------
}
