use super::*;

impl Explorer<'_> {
    /// The `RefWitness` / `MemIntrinsic` arms of [`Explorer::step`] — split out mechanically.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn step_mem_inst(&mut self, block: BlockId, idx: usize, inst: &Inst, state: &mut PathState) {
        match inst {
            Inst::RefWitness { dst, size, align, writable, assumed, src } => {
                // A raw-pointer field (`assumed`) is a valid reference only under the
                // `assume_valid_params` opt-in; otherwise leave the loaded pointer with
                // its opaque provenance (sound — accesses through it stay UNKNOWN).
                if *assumed && !self.assume_valid_params {
                    return;
                }
                if *assumed {
                    self.assumptions.insert(PARAM_VALID);
                }
                // Field identity: if the reference was loaded from a known field address that
                // resolves to a concrete `(base, offset)` — a tracked region OR an opaque
                // provenance id — reuse the region materialised for that field on an earlier
                // load, so two loads of the same field alias (an in-place `src == dst` through
                // field loads is then recognised). Cleared on heap havoc, so a reassigned
                // field re-materialises.
                let key = src.as_ref().and_then(|s| {
                    let p = self.eval_pointer(s, state);
                    let base = match p.prov {
                        Prov::Region(rid) => RefBase::Region(rid),
                        Prov::Unknown(_, Some(id)) => RefBase::Opaque(id),
                        _ => return None,
                    };
                    self.ctx.as_const(p.offset).map(|o| (base, o.unsigned()))
                });
                // The base object's provenance labels, so a field materialised from a
                // `foreign` object is itself foreign (taint-on-read).
                let src_labels =
                    src.as_ref().map(|s| self.ptr_labels(s, state)).unwrap_or_default();
                // A valid reference to a fresh live region (see `materialize_ref_region`): a
                // known size is refutable, an unknown size (slice/`str`) prove-only.
                let rid = match key.and_then(|k| state.ref_regions.get(&k).copied()) {
                    Some(rid) => rid,
                    None => {
                        let rid = self.materialize_ref_region(*size, *writable, *assumed, state);
                        state.regions[rid].prov_labels.extend(src_labels);
                        if let Some(k) = key {
                            state.ref_regions.insert(k, rid);
                        }
                        rid
                    }
                };
                let zero = self.ctx.int(PTR_WIDTH, 0);
                state.env.insert(
                    *dst,
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: zero,
                        align: (*align).max(1) as u64,
                        borrow: None,
                    }),
                );
            }
            Inst::MemIntrinsic { kind, dst, src, len } => {
                self.check_mem_intrinsic((block, idx), *kind, dst, src.as_ref(), len, state);
                // `copy_from_user` fills the destination with untrusted data: mark
                // that region user-controlled, so values later loaded from it are
                // genuine adversarial inputs (a length read back can drive an OOB).
                if matches!(kind, MemKind::UserFill) {
                    if let Prov::Region(rid) = self.eval_pointer(dst, state).prov {
                        if let Some(r) = state.regions.get_mut(rid) {
                            r.user_controlled = true;
                        }
                    }
                    // Double-fetch (TOCTOU): key the USER source address by `(base, concrete
                    // offset)`; a re-fetch of an address already read on this path is a
                    // definite double-fetch — refuted (a value validated on the first read
                    // can differ on the second, since user memory is adversary-controlled).
                    // A symbolic source (no concrete key) cannot be proven must-aliasing, so
                    // no re-fetch is established there — sound (proved, no false FAIL).
                    let dfkey = src.as_ref().and_then(|s| {
                        let sp = self.eval_pointer(s, state);
                        let base = Self::ptr_base_key(&SymValue::Ptr(sp.clone()))?;
                        self.ctx.as_const(sp.offset).map(|o| (base, o.unsigned()))
                    });
                    match dfkey {
                        Some(key) => {
                            let dup = state.user_fetches.contains(&key);
                            self.record_temporal(
                                (block, idx),
                                SafetyProperty::DoubleFetch,
                                dup,
                                state,
                                "no user address is fetched twice on this path",
                                "re-fetches a user address already read on this path (double-fetch TOCTOU)",
                            );
                            state.user_fetches.insert(key);
                        }
                        None => self.record(
                            block,
                            idx,
                            SafetyProperty::DoubleFetch,
                            true,
                            "no user address is fetched twice on this path",
                            "",
                        ),
                    }
                    // The written bytes are untrusted user data; a load from the
                    // now-user-controlled region yields a genuine symbol (see
                    // `load_value`). Leave no stored value to intercept that read,
                    // and keep the path exact — the value is genuinely free, not an
                    // over-approximation. (Just invalidate stale stored values.)
                    state.heap.clear();
        state.unwritten_reads.clear();
        state.ref_regions.clear();
                    return;
                }
                // `copy_to_user` discloses the source buffer to userspace: if it is a
                // freshly-allocated kernel buffer whose copied bytes were never written,
                // that is an information leak (uninitialized heap/stack disclosed). Uses
                // the same unwritten-read machinery as a scalar uninit read: an exact path
                // where the source range has no aliasing store is a definite leak, witnessed.
                if matches!(kind, MemKind::UserDrain) {
                    let exact_before = state.exact;
                    let srcp = self.eval_pointer(dst, state);
                    if exact_before && self.is_fresh_alloc(&srcp, state) {
                        let n = match len {
                            Operand::Const(Const::Int(bv)) => u64::try_from(bv.unsigned()).ok(),
                            _ => None,
                        };
                        if let Some(n) = n.filter(|n| *n > 0) {
                            // Scan the WHOLE copied range (not just the first word): a leak
                            // fires if any chunk is definitely never-written — so a buffer
                            // whose head is written but whose tail is uninitialized (a
                            // too-large `copy_to_user`) is caught, not only a wholly-fresh one.
                            if self.range_has_unwritten_bytes(&srcp, n, state) {
                                if let Some(model) = self.feasibility_witness(state) {
                                    self.record_info_leak(block, idx, model);
                                }
                            }
                        }
                    }
                    // A pure read: nothing to model on the (kernel) side beyond the
                    // obligations already recorded by `check_mem_intrinsic`.
                    return;
                }
                // Model the bulk *write*. Clearing the heap alone is not enough:
                // the destination bytes are now written, and forgetting that made
                // every later load from a fresh alloca a "definite uninitialized
                // read" — a false FAIL on rustc's pervasive aggregate-copy pattern
                // (`store; memcpy; load`).
                let concrete_len = match len {
                    Operand::Const(Const::Int(bv)) => u64::try_from(bv.unsigned()).ok(),
                    _ => None,
                };
                // For a concrete-length copy, forward the source value (read
                // *before* the heap is invalidated): a `Must`-aliasing source
                // store supplies the actually-copied value, keeping the path
                // exact. Anything else yields a fresh unknown.
                let value_ty = Type::int(concrete_len.map_or(64, |n| (n * 8).clamp(8, 128) as u32));
                let forwarded = match (kind, src, concrete_len) {
                    (MemKind::Copy | MemKind::Move, Some(s), Some(n)) => {
                        let sp = self.eval_pointer(s, state);
                        let (v, origin) = self.load_value(&sp, n, &value_ty, state);
                        Some((v, matches!(origin, LoadOrigin::Stored)))
                    }
                    _ => None,
                };
                // A bulk write invalidates the symbolic heap's stored values.
                state.heap.clear();
        state.unwritten_reads.clear();
        state.ref_regions.clear();
                match concrete_len {
                    Some(n) => {
                        let dstp = self.eval_pointer(dst, state);
                        let (value, exact) = forwarded.unwrap_or_else(|| {
                            (self.fresh_value(&value_ty, POrigin::Load), false)
                        });
                        // A fresh stand-in for the written bytes must not feed an
                        // "exact" counterexample witness.
                        if !exact {
                            state.exact = false;
                        }
                        state.heap.push(StoreRecord { target: dstp, value, size: n });
                    }
                    // Unknown extent: the destination is written but no record can
                    // size it soundly — no definite (witnessed) verdicts past here.
                    None => state.exact = false,
                }
            }
            // Only ever called with the variants matched above (see `step`).
            _ => {}
        }
    }
}
