use super::*;

impl Explorer<'_> {
    pub(crate) fn check_access(
        &mut self,
        at: (BlockId, usize),
        p: &SymPointer,
        asize: u64,
        aalign: u64,
        perm_prop: SafetyProperty,
        state: &PathState,
    ) {
        use SafetyProperty::*;
        let (block, idx) = at;

        // A `select`/PHI join: check each alternative under its guard and let the
        // per-obligation records conjoin (an access is safe iff safe on both). The
        // outer offset (any pointer arithmetic done on the join) adds to both.
        if let Prov::Select { cond, then_ptr, else_ptr } = &p.prov {
            let (cond, then_ptr, else_ptr) = (*cond, then_ptr.clone(), else_ptr.clone());
            let ncond = self.ctx.not(cond);
            let outer = p.offset;
            let branch = |ex: &mut Self, sub: &SymPointer| SymPointer {
                prov: sub.prov.clone(),
                offset: ex.ctx.bin(BvOp::Add, sub.offset, outer),
                align: sub.align,
                borrow: sub.borrow,
            };
            let pa = branch(self, &then_ptr);
            let pb = branch(self, &else_ptr);
            let mut sa = state.clone();
            sa.pathcond.push(cond);
            let mut sb = state.clone();
            sb.pathcond.push(ncond);
            self.check_access(at, &pa, asize, aalign, perm_prop, &sa);
            self.check_access(at, &pb, asize, aalign, perm_prop, &sb);
            return;
        }

        // Null. A tracked region is non-null; so is an opaque pointer whose provenance id is
        // marked `nonnull` (an LLVM `nonnull` parameter, e.g. Zig `*T`) — the mark flows through
        // gep/copy on the id, so a derived access is non-null too (only NoNullDeref, not bounds).
        let non_null = matches!(p.prov, Prov::Region(_))
            || matches!(p.prov, Prov::Unknown(_, Some(id)) if state.nonnull_provs.contains(&id))
            // A `if (p != null)` guard on the path proves non-null even for an opaque pointer:
            // the guard scalarised `p` to the same stable `ptr#id` symbol (see `scalarize`), so
            // if the path condition implies that address is non-zero the dereference is non-null.
            // Prove-only — a pointer with no such guard stays UNKNOWN (never a false FAIL).
            || (matches!(p.prov, Prov::Unknown(_, Some(_))) && {
                let addr = self.scalarize(SymValue::Ptr(p.clone()));
                let zero = self.ctx.int(PTR_WIDTH, 0);
                let goal = self.ctx.cmp(SCmp::Ne, addr, zero);
                self.prove(goal, state)
            });
        // MMIO trust (`--assume-valid-mmio`): an access through an `iomem`-labelled pointer — a
        // device-register mapping whose extent is the device's, known only at the mapping site —
        // is *assumed* within the mapping. Prove-only: every memory obligation is discharged, but
        // nothing is refuted (a symbolic register offset could genuinely be out of range — a real
        // driver bug — so with the flag off it stays UNKNOWN, and with it on we never fabricate a
        // FAIL either). Placed before the opaque-provenance bailout, which is exactly the residual
        // it closes: a loaded `void __iomem *` field carries the label but no region.
        if self.limits.assume_valid_mmio && self.pointer_is_iomem(p, state) {
            self.assumptions.insert(VALID_MMIO);
            for prop in [NoNullDeref, NoUseAfterFree, InBounds, Alignment, perm_prop] {
                self.record(block, idx, prop, true, "MMIO mapping access is assumed valid", "");
            }
            return;
        }

        self.record(block, idx, NoNullDeref, non_null, "pointer is non-null", "pointer may be null or have opaque provenance");

        let Prov::Region(rid) = p.prov else {
            let residual = p.prov.provenance_residual();
            for prop in [NoUseAfterFree, InBounds, Alignment, perm_prop] {
                self.record(block, idx, prop, false, "requires known provenance", residual);
            }
            return;
        };
        // A stale region id (a dropped-region pointer that reached here via a heap
        // reload / block arg / select branch, past `eval_value`'s sanitization) is
        // treated as unknown provenance instead of indexing out of bounds — sound (the
        // access is left unproven, never a false PASS).
        let Some(region) = state.regions.get(rid) else {
            let residual = Prov::Unknown(POrigin::RegionDrop, None).provenance_residual();
            for prop in [NoUseAfterFree, InBounds, Alignment, perm_prop] {
                self.record(block, idx, prop, false, "requires known provenance", residual);
            }
            return;
        };
        let rstate = region.state;
        let rperms = region.perms;
        let rkind = region.kind;
        let rsize = region.size;
        let contract = region.contract;
        let size_nowrap = region.size_nowrap;
        let region_assumed = region.assumed;
        let base_align = region.base_align;

        // Use-after-free: on an exact path a `Freed` region was definitely
        // deallocated, so the access is a certain UAF — refuted with a witness.
        let live = rstate == LifetimeState::Live;
        self.record_temporal((block, idx), NoUseAfterFree, !live, state, "region is live", "region may be freed (use-after-free)");

        // In-bounds: 0 <= offset && offset + asize <= size. Refutable (a real
        // OOB witness) whenever the region's byte size is known not to wrap
        // (concrete, or a symbolic `count * stride` with the recorded
        // `count <= isize::MAX/stride` bound): then a satisfying violation is a
        // genuine reachable OOB, since the only remaining free variable is the
        // access offset and the size cannot be a wrapped too-small value.
        let conjuncts = self.in_bounds_conjuncts(p.offset, asize, rsize);
        let (mut mode, extra) = match size_nowrap {
            Some(fact) => (RefuteMode::Possible, vec![fact]),
            None => (RefuteMode::Off, vec![]),
        };
        // An *assumed* region's size is a caller-supplied guess, not a proven bound
        // (see `SymRegion::assumed`). Refute an OOB against it only when the access
        // offset is actually driven by a genuine adversarial input; a constant offset
        // (`container_of`'s backward step, a fixed field past the guessed size) is an
        // artifact of the guess — reporting it would be a false FAIL.
        if region_assumed && !self.expr_has_genuine_leaf(p.offset) {
            mode = RefuteMode::Off;
        }
        let decision = self.decide(&conjuncts, state, mode, &extra);
        self.record_mem(block, idx, InBounds, decision, "access stays within the allocation", "could not prove the access stays in bounds");

        // Alignment. First the concrete guarantee (`p.align` is the gcd-folded alignment through
        // pointer arithmetic). When that does not establish it, fall back to a **symbolic proof**:
        // if the region base is at least `aalign`-aligned, the address is aligned iff the offset is,
        // so prove `offset ≡ 0 (mod aalign)` (i.e. `offset & (aalign-1) == 0`) under the path. This
        // decides masked (`p & ~7`) and guarded (`if (off % 8 == 0)`) offsets the gcd cannot see.
        // Proof-only: a genuinely unaligned access (common and legal in packed/network code) is left
        // UNKNOWN, never refuted — no false FAIL.
        let aligned = aalign <= 1
            || p.align.is_multiple_of(aalign)
            || (aalign.is_power_of_two() && base_align >= aalign && {
                let w = self.ctx.width(p.offset);
                let mask = self.ctx.int(w, (aalign - 1) as u128);
                let masked = self.ctx.bin(BvOp::And, p.offset, mask);
                let zero = self.ctx.int(w, 0);
                let goal = self.ctx.cmp(SCmp::Eq, masked, zero);
                self.prove(goal, state)
            });
        self.record(block, idx, Alignment, aligned, "address meets the required alignment", "could not prove the required alignment");

        // Permission. A write into a region that provably lacks write permission is a
        // real violation. When that region is a definitely read-only GLOBAL — a store
        // into `.rodata` / a `constant` object, which faults at runtime — it is refuted
        // (a FAIL with a witness) like any other definite memory violation. Any other
        // non-writable region (a contract-derived `const`/`readonly` parameter, which C
        // legitimately casts away) stays a prove-only UNKNOWN, so this adds no false FAIL.
        if matches!(perm_prop, ValidWrite) && !rperms.write && matches!(rkind, RegionKind::Global) {
            self.record_temporal(
                (block, idx),
                ValidWrite,
                true,
                state,
                "region grants the write permission",
                "write into a read-only (constant/.rodata) region",
            );
        } else {
            let granted = match perm_prop {
                ValidRead => rperms.read,
                ValidWrite => rperms.write,
                _ => true,
            };
            self.record(block, idx, perm_prop, granted, "region grants the access permission", "region does not grant the access permission");
        }

        if non_null && live {
            self.assumptions.insert(contract.unwrap_or(ALLOC_SUCCEEDS));
        }
    }

    pub(crate) fn check_ptr_arith(&mut self, block: BlockId, idx: usize, p: &SymPointer, state: &PathState) {
        use SafetyProperty::ValidPointerArith;
        // A join: the arithmetic stays in-object iff it does for each alternative
        // under its guard.
        if let Prov::Select { cond, then_ptr, else_ptr } = &p.prov {
            let (cond, then_ptr, else_ptr) = (*cond, then_ptr.clone(), else_ptr.clone());
            let ncond = self.ctx.not(cond);
            let outer = p.offset;
            let branch = |ex: &mut Self, sub: &SymPointer| SymPointer {
                prov: sub.prov.clone(),
                offset: ex.ctx.bin(BvOp::Add, sub.offset, outer),
                align: sub.align,
                borrow: sub.borrow,
            };
            let pa = branch(self, &then_ptr);
            let pb = branch(self, &else_ptr);
            let mut sa = state.clone();
            sa.pathcond.push(cond);
            let mut sb = state.clone();
            sb.pathcond.push(ncond);
            self.check_ptr_arith(block, idx, &pa, &sa);
            self.check_ptr_arith(block, idx, &pb, &sb);
            return;
        }
        // MMIO trust: forming a register offset off an `iomem` mapping is assumed in-object
        // (`--assume-valid-mmio`), matching the access bypass in `check_access`. Prove-only.
        if self.limits.assume_valid_mmio && self.pointer_is_iomem(p, state) {
            self.assumptions.insert(VALID_MMIO);
            self.record(block, idx, ValidPointerArith, true, "MMIO register offset is assumed in-object", "");
            return;
        }
        let Prov::Region(rid) = p.prov else {
            self.record(block, idx, ValidPointerArith, false, "requires known provenance", p.prov.provenance_residual());
            return;
        };
        // A stale region id — a pointer into a region a control-flow merge dropped —
        // whose id now points past this path's `regions`. `eval_value` rewrites such
        // pointers on a register read, but one can still reach here via a heap reload, a
        // block argument, or a `select` branch; treat it as unknown provenance rather
        // than indexing out of bounds. Sound: the arithmetic is left unproven, never a
        // false PASS.
        let Some(region) = state.regions.get(rid) else {
            self.record(block, idx, ValidPointerArith, false, "requires known provenance", Prov::Unknown(POrigin::RegionDrop, None).provenance_residual());
            return;
        };
        let rsize = region.size;
        let contract = region.contract;
        // In-object or one-past-end: 0 <= offset <= size. Refutation off here:
        // the *access* in-bounds check (in `check_access`) is the one that
        // carries the OOB counterexample; the intermediate pointer arithmetic is
        // only proved.
        let conjuncts = self.in_range_conjuncts(p.offset, rsize);
        let decision = self.decide(&conjuncts, state, RefuteMode::Off, &[]);
        let proven = matches!(decision, Decision::Proven);
        self.record_mem(block, idx, ValidPointerArith, decision, "result stays within the object (or one-past-end)", "could not prove the offset stays in-object");
        if proven {
            self.assumptions.insert(contract.unwrap_or(ALLOC_SUCCEEDS));
        }
    }

    pub(crate) fn check_dealloc(&mut self, block: BlockId, idx: usize, p: &SymPointer, state: &mut PathState) {
        use SafetyProperty::NoDoubleFree;
        let Prov::Region(rid) = p.prov else {
            self.record(block, idx, NoDoubleFree, false, "requires known provenance", "freed pointer provenance is not tracked");
            return;
        };
        // A stale (dropped-region) id is treated as unknown provenance, not an OOB index.
        if state.regions.get(rid).is_none() {
            self.record(block, idx, NoDoubleFree, false, "requires known provenance", "freed pointer provenance is not tracked (region dropped at path merge)");
            return;
        }
        if state.regions[rid].contract.is_some() {
            // Freeing caller-owned (borrowed) memory is not ours to prove safe.
            self.record(block, idx, NoDoubleFree, false, "caller-owned region", "freeing a borrowed (caller-owned) region is not provably valid");
            return;
        }
        if !matches!(state.regions[rid].kind, RegionKind::Heap) {
            // Only allocator memory can be deallocated: freeing a stack slot /
            // global / TLS region is UB regardless of its state. This is also
            // the callee-side guarantee behind the caller-side assumption that
            // a call never frees a stack region (see `step_call`) — the pair
            // must stay in sync or the composition is unsound.
            self.record_temporal((block, idx), NoDoubleFree, true, state, "frees allocator memory", "freeing non-heap (stack/global) memory is undefined behaviour");
            return;
        }
        let rstate = state.regions[rid].state;
        if rstate != LifetimeState::Live {
            // On an exact path the region was definitely freed already, so this
            // is a certain double free — refuted with a witness.
            self.record_temporal((block, idx), NoDoubleFree, true, state, "region must be live to free", "region may already be freed (double free)");
            return;
        }
        // Must free the base pointer (offset == 0).
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let goal = self.ctx.cmp(SCmp::Eq, p.offset, zero);
        let at_base = self.prove(goal, state);
        self.record(block, idx, NoDoubleFree, at_base, "frees the base of a live allocation exactly once", "could not prove the freed pointer is the live base");
        if at_base {
            self.assumptions.insert(ALLOC_SUCCEEDS);
            state.regions[rid].state = LifetimeState::Freed;
        }
    }

    /// The conjuncts of in-bounds: `0 <= offset`, no-overflow of the extent, and
    /// `offset + asize <= size`. The middle conjunct (`offset <= offset+asize`)
    /// rules out a wrapped `end` that would satisfy the upper bound vacuously (see
    /// [`Self::prove_in_bounds_len`]).
    pub(crate) fn in_bounds_conjuncts(&mut self, offset: ExprId, asize: u64, size: ExprId) -> [ExprId; 3] {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let asize_e = self.ctx.int(PTR_WIDTH, asize as u128);
        let end = self.ctx.bin(BvOp::Add, offset, asize_e);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let no_overflow = self.ctx.cmp(SCmp::Sle, offset, end);
        let upper = self.ctx.cmp(SCmp::Sle, end, size);
        [lower, no_overflow, upper]
    }

    /// `0 <= offset`, no-overflow, and `offset + len <= size` for a **symbolic**
    /// byte length `len` (a bulk copy). The refutable form of
    /// [`prove_in_bounds_len`].
    pub(crate) fn in_bounds_len_conjuncts(&mut self, offset: ExprId, len: ExprId, size: ExprId) -> [ExprId; 3] {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let end = self.ctx.bin(BvOp::Add, offset, len);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let no_overflow = self.ctx.cmp(SCmp::Sle, offset, end);
        let upper = self.ctx.cmp(SCmp::Sle, end, size);
        [lower, no_overflow, upper]
    }

    /// The goal "the allocation byte size does not overflow the pointer width",
    /// for a size of the form `var * C` (a variable count times a *constant*
    /// element/product `C`). Overflow is exactly `var >u (UINT_MAX / C)`, so the
    /// goal is the constant-bound comparison `var <=u UINT_MAX / C` — no wide
    /// multiply, so the solver discharges it cheaply and can witness a violation.
    ///
    /// Returns `None` (obligation trivially satisfied) when the size is a bare
    /// constant, has no constant factor `> 1`, or has *two or more* variable
    /// factors (`n * m` — a wide multiply this path deliberately does not model;
    /// its overflow, if any, still surfaces downstream as an OOB against the
    /// wrapped region size). Sound: a `None` only ever *omits* a check.
    pub(crate) fn size_overflow_goal(&mut self, size: ExprId) -> Option<ExprId> {
        let factors = self.mul_factors(size);
        let mut c: u128 = 1;
        let mut var: Option<ExprId> = None;
        for f in factors {
            match self.ctx.node(f) {
                Node::Const(bv) => c = c.checked_mul(bv.unsigned())?,
                _ => {
                    // More than one variable factor: not this path's job.
                    if var.replace(f).is_some() {
                        return None;
                    }
                }
            }
        }
        let var = var?;
        if c <= 1 {
            return None;
        }
        let umax = (1u128 << PTR_WIDTH) - 1;
        let bound = self.ctx.int(PTR_WIDTH, umax / c);
        Some(self.ctx.cmp(SCmp::Ule, var, bound))
    }

    /// Flatten a tree of `BvOp::Mul` nodes into its leaf factors (a non-mul is one
    /// factor). So `(n * size) * stride` yields `[n, size, stride]`.
    pub(crate) fn mul_factors(&self, e: ExprId) -> Vec<ExprId> {
        let mut out = Vec::new();
        let mut stack = vec![e];
        while let Some(x) = stack.pop() {
            match self.ctx.node(x) {
                Node::Bin { op: BvOp::Mul, a, b } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => out.push(x),
            }
        }
        out
    }

    /// The fact `count <=u isize::MAX / stride`, so `count * stride` does not
    /// wrap and the byte size is faithful. Sound under `alloc-succeeds` /
    /// `slice-abi` (a successful allocation / valid slice has a size that fits).
    pub(crate) fn size_no_wrap_fact(&mut self, count: ExprId, stride: u64) -> ExprId {
        let max_count = ISIZE_MAX / (stride.max(1) as u128);
        let bound = self.ctx.int(PTR_WIDTH, max_count);
        self.ctx.cmp(SCmp::Ule, count, bound)
    }

    /// The conjuncts of in-range: `0 <= offset` and `offset <= size`
    /// (one-past-end allowed).
    pub(crate) fn in_range_conjuncts(&mut self, offset: ExprId, size: ExprId) -> [ExprId; 2] {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let upper = self.ctx.cmp(SCmp::Sle, offset, size);
        [lower, upper]
    }

    /// A reborrow marker (`csolver.retag.mut`/`.shared`), for the opt-in aliasing model.
    /// `args[0]` is the new borrow tag (register), `args[1]` the parent pointer. The parent's
    /// tag is read **dynamically** from the parent pointer's [`SymPointer::borrow`] (so it flows
    /// through memory/phi), and the new tag is stamped onto the reborrow's pointer value. A
    /// **unique** (`&mut`) reborrow pushes its tag, popping the parent's other descendants — a
    /// reborrow invalidates its siblings (Stacked/Tree-Borrows). A root reborrow (parent has no tag —
    /// e.g. a `&mut` parameter) invalidates every prior borrow of the region. If the parent is
    /// no longer live, the region is *poisoned* (checks skipped — sound, never a false FAIL).
    pub(crate) fn step_retag(&mut self, args: &[Operand], state: &mut PathState) {
        let (Some(new_tag), Some(parent_op)) =
            (args.first().and_then(|o| o.as_reg()), args.get(1).cloned())
        else {
            return;
        };
        let parent_ptr = self.eval_pointer(&parent_op, state);
        let Prov::Region(rid) = parent_ptr.prov else {
            return;
        };
        if matches!(state.region_borrows.get(&rid), Some(None)) {
            return; // already poisoned
        }
        // The parent's borrow tag flows on the pointer value (through memory/phi too); `None`
        // is a root reborrow of an untracked pointer (e.g. a `&mut` parameter's owner).
        let parent_tag = parent_ptr.borrow;
        let unique = self.borrow_info.unique.get(&new_tag).copied().unwrap_or(true);
        // Stamp the new borrow tag onto the reborrow's pointer value so it flows onward.
        if let Some(SymValue::Ptr(p)) = state.env.get_mut(&new_tag) {
            p.borrow = Some(new_tag);
        }
        let mut stack = state.region_borrows.get(&rid).cloned().flatten().unwrap_or_default();
        let new_val = if !unique {
            // A **shared** (`&T`) reborrow: add the tag without popping siblings — shared borrows
            // coexist (an under-approximation of Stacked Borrows' read effect: only ever *adds* a
            // live tag, so it can never turn a valid access into a false FAIL). A later `&mut`
            // write through a lower tag still pops it (see the write case in `check_borrow_access`).
            if !stack.contains(&new_tag) {
                stack.push(new_tag);
            }
            Some(stack)
        } else {
            match parent_tag {
                None => Some(vec![new_tag]), // root **mutable** reborrow — invalidates all prior borrows
                Some(pt) => match stack.iter().position(|&t| t == pt) {
                    Some(pos) => {
                        stack.truncate(pos + 1);
                        stack.push(new_tag);
                        Some(stack)
                    }
                    None => None, // parent no longer live → poison (sound)
                },
            }
        };
        state.region_borrows.insert(rid, new_val);
    }

    /// Check an access through `ptr` against its region's borrow stack (opt-in aliasing model).
    /// If the accessing pointer's borrow tag is no longer live on the region — it was popped by
    /// an aliasing `&mut` reborrow or write — the access is a **use-after-invalidation** (UB).
    /// A write also pops the borrows created after the accessed tag (they are invalidated).
    /// Only fires on a definitely-invalidated tag over a *tracked* region — sound, no false FAIL.
    pub(crate) fn check_borrow_access(
        &mut self,
        at: (BlockId, usize),
        is_write: bool,
        p: &SymPointer,
        state: &mut PathState,
    ) {
        let (Some(tag), Prov::Region(rid)) = (p.borrow, &p.prov) else {
            return; // pointer carries no borrow tag, or has no tracked region
        };
        let rid = *rid;
        let Some(Some(stack)) = state.region_borrows.get(&rid) else {
            return; // region untracked or poisoned
        };
        match stack.iter().position(|&t| t == tag) {
            Some(pos) => {
                if is_write {
                    if let Some(Some(s)) = state.region_borrows.get_mut(&rid) {
                        s.truncate(pos + 1);
                    }
                }
            }
            None => self.record_temporal(
                at,
                SafetyProperty::NoAliasingViolation,
                true,
                state,
                "no use of a mutable borrow after it was invalidated",
                "use of a &mut borrow after an aliasing &mut invalidated it (Rust borrow-stack violation)",
            ),
        }
    }
}
