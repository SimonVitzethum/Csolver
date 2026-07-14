use super::*;

impl Explorer<'_> {
    /// Append one `(kind, class)` event to the bounded interleaving trace (no-op past the cap).
    fn push_race_event(&mut self, kind: u8, class: String) {
        if self.race_trace.len() < self.race_trace_cap {
            self.race_trace.push((kind, class));
        }
    }

    /// The contract-driven instruction arms of [`Explorer::step`] (provenance, taint,
    /// typestate, refcount, concurrency events) — split out mechanically.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn step_contract(&mut self, block: BlockId, idx: usize, inst: &Inst, state: &mut PathState) {
        match inst {
            Inst::ProvLabel { ptr, label } => {
                self.add_ptr_label(ptr, *label, state);
            }
            // Propagate provenance: `dst` absorbs `src`'s labels (a contract `propagate` — a
            // container taking in an element). A foreign element thus makes the container only
            // as capable as its least-capable member.
            Inst::ProvPropagate { dst, src } => {
                let src_labels = self.ptr_labels(src, state);
                for l in src_labels {
                    self.add_ptr_label(dst, l, state);
                }
            }
            // Require the pointed-to region/pointer to grant `cap` (a contract `require`). A
            // provenance set containing a label that provably lacks the capability is a
            // definite violation — refuted with the path-feasibility witness (a FAIL on an
            // exact / bug-finding path, else UNKNOWN). An unlabelled pointer grants everything
            // (sound: no false FAIL). Mirrors `record_temporal`.
            Inst::CapRequire { ptr, cap } => {
                let labels = self.ptr_labels(ptr, state);
                let lacks = self.labels_lack_cap(&labels, *cap);
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::WriteCapability,
                    lacks,
                    state,
                    "the access target's provenance grants the required capability",
                    "the access target's provenance may not grant the required capability",
                );
            }
            // Conditional capability: fire ONLY when `a` and `b` have the SAME provenance
            // identity (an in-place `src == dst` op — same region or same opaque register) and
            // that provenance lacks `cap`. When they are distinct (the safe out-of-place path)
            // it never fires — the precise gate that catches in-place-write-to-foreign without
            // false-FAILing the copy.
            Inst::CapRequireIfAlias { a, b, cap } => {
                let (pa, pb) = (self.eval_pointer(a, state), self.eval_pointer(b, state));
                let lacks = self.alias_lacks_cap(&pa, &pb, *cap, state);
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::WriteCapability,
                    lacks,
                    state,
                    "an in-place operation's aliased region grants the required capability",
                    "an in-place operation writes a region whose provenance may not grant it",
                );
            }
            // The inlined-request form: read the two field pointers back from the object
            // INTERNALLY (via read-your-writes, no safety obligation on these analyzer reads),
            // then apply the same in-place-alias check. Fires iff both fields hold the same
            // region and it lacks the capability.
            Inst::CapRequireIfAliasFields { obj, off_a, off_b, cap } => {
                let base = self.eval_pointer(obj, state);
                let field = |ex: &mut Self, off: u64, st: &mut PathState| -> SymValue {
                    let off_e = ex.ctx.int(PTR_WIDTH, off as u128);
                    let field_ptr = SymPointer {
                        prov: base.prov.clone(),
                        offset: ex.ctx.bin(BvOp::Add, base.offset, off_e),
                        align: 1,
                        borrow: None,
                    };
                    ex.load_value(&field_ptr, PTR_WIDTH as u64 / 8, &Type::ptr(Type::int(8)), st).0
                };
                let (sv, dv) = (field(self, *off_a, state), field(self, *off_b, state));
                let lacks = match (&sv, &dv) {
                    (SymValue::Ptr(sp), SymValue::Ptr(dp)) => {
                        self.alias_lacks_cap(sp, dp, *cap, state)
                    }
                    _ => false,
                };
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::WriteCapability,
                    lacks,
                    state,
                    "an in-place operation's aliased field region grants the required capability",
                    "an in-place operation writes a field region whose provenance may not grant it",
                );
            }
            // Directional taint (injection J / tainted-length F / info-flow D).
            Inst::TaintSource { val, taint } => {
                self.taint_add(val, *taint, state);
            }
            Inst::TaintClear { val, taint } => {
                self.taint_remove(val, *taint, state);
            }
            // A tainted value reaching a sink is refuted (a definite taint on this path — the
            // taint map is meet-joined, so no false FAIL under a partly-tainted phi). An
            // untainted / sanitised value passes. Mirrors `CapRequire`.
            Inst::TaintCheck { val, taint } => {
                let tainted = self.taint_has(val, *taint, state);
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::TaintedSink,
                    tainted,
                    state,
                    "no untrusted (tainted) value reaches this sink",
                    "an untrusted (tainted) value reaches an unsafe sink (injection / tainted length)",
                );
            }
            // Typestate transition: move the named resource into `state` within `protocol`.
            Inst::TypestateSet { val, protocol, state: st } => {
                if let Some(key) = self.res_key(val, state) {
                    state.typestates.insert((key, *protocol), *st);
                }
                // Cross-entry (cross-syscall) stream: a typestate transition on a global-rooted
                // object persists between independent syscall entries (kind 14, `set`). Paired with
                // a `require-not` of the same state in another entry → cross-entry use-after-state.
                self.record_global_typestate(0, val, *protocol, *st);
            }
            // Typestate obligation: the resource must (not) be in `state`. A definite match
            // to the forbidden state on this path is refuted (use-after-close, missing-check).
            // An untracked resource (`None`, or no recorded state) is treated as *not* in any
            // named state — so `require-not` never false-FAILs an unseen handle, and `require`
            // (must-be-in-state) fires when the state was never established. Sound for bug-
            // finding; the meet-join guarantees a refutation is on a definite path.
            Inst::TypestateRequire { val, protocol, state: st, negate } => {
                let cur = self
                    .res_key(val, state)
                    .and_then(|key| state.typestates.get(&(key, *protocol)).copied());
                let in_state = cur == Some(*st);
                let violated = if *negate { in_state } else { !in_state };
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::TypestateViolation,
                    violated,
                    state,
                    "the resource is in a protocol state this operation allows",
                    "the resource is used in a state its protocol forbids (use-after-close / missing-check)",
                );
                // Cross-entry stream: a `require`(-not) on a global-rooted object (kind 14, `req`/
                // `reqnot`) — the "use" side of a cross-syscall use-after-state.
                self.record_global_typestate(if *negate { 2 } else { 1 }, val, *protocol, *st);
            }
            // Protocol-wide yield (TOCTOU): every resource of `protocol` in state `from`
            // moves to `to` — a `check` invalidated by an intervening yield.
            Inst::TypestateYield { protocol, from, to } => {
                let hits: Vec<(ResKey, u32)> = state
                    .typestates
                    .iter()
                    .filter(|((_, p), s)| p == protocol && *s == from)
                    .map(|((k, p), _)| (*k, *p))
                    .collect();
                for key in hits {
                    state.typestates.insert(key, *to);
                }
            }
            // Reference-count change: inc/dec the resource's count; a `dec` below zero is an
            // underflow (premature free → UAF), refuted on a definite path.
            Inst::Refcount { val, protocol, dec, checked } => {
                // Ordered trace for the concurrent-refcount-race check: an unchecked get (kind 12)
                // and a put (kind 13). A put may drop the count to zero and free; a plain get that
                // races it can raise a zeroed count and resurrect a dying object (UAF). A *checked*
                // get (`*_not_zero`) refuses that, so it emits no race event.
                if self.race_trace.len() < self.race_trace_cap && (*dec || !*checked) {
                    if let Some(class) = crate::lockclass::lock_class_of_arg(&self.lock_classes, val) {
                        self.race_trace.push((if *dec { 13 } else { 12 }, class));
                    }
                }
                if let Some(key) = self.res_key(val, state) {
                    if *dec {
                        // A put on an object whose count was **established in this scope** (a prior
                        // get, tracked in the map) below zero is an underflow (premature free /
                        // UAF). A put on an *untracked* object — a bare parameter the caller holds
                        // with an unknown count — is not an underflow (sound: no false FAIL on a
                        // helper that just drops the caller's reference).
                        let tracked = state.refcounts.get(&(key, *protocol)).copied();
                        match tracked {
                            Some(c) => {
                                let underflow = c <= 0;
                                state.refcounts.insert((key, *protocol), c - 1);
                                self.record_temporal(
                                    (block, idx),
                                    SafetyProperty::TypestateViolation,
                                    underflow,
                                    state,
                                    "the reference count stays non-negative",
                                    "a reference-count decrement underflows (premature free / use-after-free)",
                                );
                            }
                            None => self.record(block, idx, SafetyProperty::TypestateViolation, true, "the reference count stays non-negative", ""),
                        }
                    } else {
                        *state.refcounts.entry((key, *protocol)).or_insert(0) += 1;
                        self.record(block, idx, SafetyProperty::TypestateViolation, true, "the reference count stays non-negative", "");
                    }
                }
            }
            // Leak check at return: a resource still in the leak `state` that did not escape
            // via the returned value is a resource leak.
            Inst::TypestateLeakCheck { protocol, state: st, escaping } => {
                let escapes = escaping
                    .as_ref()
                    .and_then(|op| self.res_key(op, state));
                let leaked = state.typestates.iter().any(|((k, p), s)| {
                    p == protocol && s == st && Some(*k) != escapes
                });
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::TypestateViolation,
                    leaked,
                    state,
                    "every acquired resource is released or returned",
                    "a resource acquired on this path is neither released nor returned (leak)",
                );
            }
            // A memory barrier: record a fence in the interleaving trace (weak-memory model).
            // Trace kind 4 = full (`smp_mb`), 5 = write (`smp_wmb`), 6 = read (`smp_rmb`).
            // For a `smp_store_release`/`smp_load_acquire` the call also accesses the flag: a
            // **release** (write barrier) fences prior stores THEN writes the flag (order
            // [fence, write]); an **acquire** (read barrier) reads the flag THEN fences later
            // loads (order [read, fence]) — matching the inlined-atomic lowering in block.rs.
            Inst::Barrier { kind, access } => {
                let class = access
                    .as_ref()
                    .and_then(|v| crate::lockclass::lock_class_of_arg(&self.lock_classes, v));
                match (*kind, class) {
                    // release store: fence, then the flag write.
                    (1, Some(cls)) => {
                        self.push_race_event(5, String::new());
                        self.push_race_event(3, cls);
                    }
                    // acquire load: the flag read, then the fence.
                    (2, Some(cls)) => {
                        self.push_race_event(2, cls);
                        self.push_race_event(6, String::new());
                    }
                    // a standalone fence (or an unclassifiable location): just the barrier.
                    (k, _) => self.push_race_event(4 + k, String::new()),
                }
            }
            // Thread spawn/join: record a happens-before event (kind 7 = spawn with the child's
            // function name, 8 = join) for the weak-memory model.
            Inst::Spawn { child } => {
                if self.race_trace.len() < self.race_trace_cap {
                    self.race_trace.push((7, child.clone()));
                }
            }
            Inst::Join => {
                if self.race_trace.len() < self.race_trace_cap {
                    self.race_trace.push((8, String::new()));
                }
            }
            // Compare-and-swap (ABA): record a CAS event on the location's class.
            Inst::Cas { val } => {
                if let Some(class) = crate::lockclass::lock_class_of_arg(&self.lock_classes, val) {
                    if self.race_trace.len() < self.race_trace_cap {
                        self.race_trace.push((11, class));
                    }
                }
            }
            // Constant-time: a secret-tainted value must not decide a branch or index memory.
            Inst::SecretCheck { val, taint } => {
                let secret = self.taint_has(val, *taint, state);
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::SecretDependent,
                    secret,
                    state,
                    "no secret-dependent branch or memory index",
                    "a secret-tainted value decides a branch or memory index (timing/cache side channel)",
                );
            }
            // Only ever called with the variants matched above (see `step`).
            _ => {}
        }
    }
}
