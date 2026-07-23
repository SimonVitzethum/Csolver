use super::*;

/// Every symbol name referenced by an operand of `f` (`Const::Symbol` /
/// `Const::SymbolOffset`), for seeding the referenced-globals regions.
pub(crate) fn referenced_symbols(f: &Function) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut op = |o: &Operand| match o {
        Operand::Const(Const::Symbol(n)) | Operand::Const(Const::SymbolOffset(n, _)) => {
            out.push(n.clone())
        }
        _ => {}
    };
    for b in &f.blocks {
        for inst in &b.insts {
            match inst {
                Inst::Alloc { count, .. } => op(count),
                Inst::Load { ptr, .. } => op(ptr),
                Inst::Store { ptr, value, .. } => {
                    op(ptr);
                    op(value);
                }
                Inst::PtrOffset { base, index, .. } => {
                    op(base);
                    op(index);
                }
                Inst::FieldPtr { base, .. } => op(base),
                Inst::RefWitness { src, .. } => {
                    if let Some(s) = src {
                        op(s);
                    }
                }
                Inst::Assign { value, .. } => match value {
                    RValue::Use(o) => op(o),
                    RValue::Bin { lhs, rhs, .. } | RValue::Cmp { lhs, rhs, .. } => {
                        op(lhs);
                        op(rhs);
                    }
                    RValue::Cast { operand, .. } => op(operand),
                    RValue::Select { cond, then_val, else_val } => {
                        op(cond);
                        op(then_val);
                        op(else_val);
                    }
                },
                Inst::Call { args, .. } | Inst::Intrinsic { args, .. } => {
                    args.iter().for_each(&mut op)
                }
                Inst::MemIntrinsic { dst, src, len, .. } => {
                    op(dst);
                    if let Some(sp) = src {
                        op(sp);
                    }
                    op(len);
                }
                Inst::Dealloc { ptr, .. } => op(ptr),
                Inst::ProvLabel { ptr, .. } | Inst::CapRequire { ptr, .. } => op(ptr),
                Inst::ProvPropagate { dst, src } => { op(dst); op(src); }
                Inst::CapRequireIfAlias { a, b, .. } => { op(a); op(b); }
                Inst::CapRequireIfAliasFields { obj, .. } => op(obj),
                Inst::TaintSource { val, .. }
                | Inst::TaintCheck { val, .. }
                | Inst::TaintClear { val, .. }
                | Inst::TypestateSet { val, .. }
                | Inst::TypestateRequire { val, .. }
                | Inst::Refcount { val, .. }
                | Inst::SecretCheck { val, .. } => op(val),
                Inst::TypestateLeakCheck { escaping, .. } => {
                    if let Some(e) = escaping {
                        op(e);
                    }
                }
                Inst::TypestateYield { .. } | Inst::Barrier { .. } | Inst::Spawn { .. } | Inst::Join | Inst::Cas { .. } => {}
                Inst::SafetyCheck { .. } | Inst::Asm { .. } => {}
            }
        }
        match &b.term {
            Terminator::Return(Some(o)) => op(o),
            Terminator::CondBr { cond, then_args, else_args, .. } => {
                op(cond);
                then_args.iter().for_each(&mut op);
                else_args.iter().for_each(&mut op);
            }
            Terminator::Br { args, .. } => args.iter().for_each(&mut op),
            Terminator::Switch { value, .. } => op(value),
            Terminator::Return(None) | Terminator::Unreachable => {}
        }
    }
    out
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn discharge_inner(
    f: &Function,
    limits: ExecLimits,
    summaries: &HashMap<FuncId, Summary>,
    name_summaries: &HashMap<String, Summary>,
    contracts: &[Option<PtrContract>],
    field_contracts: &[Vec<FieldContract>],
    scalar_pre: &[Option<(i128, i128)>],
    globals: &HashMap<String, GlobalDef>,
    prov_grants: &HashMap<u32, HashSet<u32>>,
    global_fn_ptrs: &HashMap<String, Vec<(u64, FuncId)>>,
    global_ptr_fields: &HashMap<String, Vec<(u64, String)>>,
    analysis_in: Option<&IntervalAnalysis>,
    reg_ptr_hints: &HashMap<RegId, PtrHint>,
    mmio_region: Option<csolver_ir::MmioHandler>,
    devirt: &HashMap<RegId, String>,
) -> SymbolicReport {
    // Reuse the caller's interval analysis when supplied (the verifier already
    // computes it for interval-based discharge), so it is not recomputed here —
    // a single clone instead of a second fixpoint. Falls back to computing it.
    let analysis = match analysis_in {
        Some(a) => a.clone(),
        None => analyze_intervals(f),
    };
    let zones = analyze_zones(f);
    let inductions = analyze_induction(f);
    let dominators = Dominators::new(analysis.cfg());
    let loops = Loops::detect(analysis.cfg(), &dominators);

    // Per loop header: the set of registers the loop body may redefine (so they
    // can be havoc'd — not just the header's own parameters), and whether the
    // body may free memory (so region lifetimes can be invalidated). These are
    // what make a single body pass a *sound* over-approximation of all
    // iterations.
    let mut headers: HashSet<BlockId> = HashSet::new();
    let mut loop_modified: HashMap<BlockId, Vec<RegId>> = HashMap::new();
    let mut loop_frees: HashMap<BlockId, bool> = HashMap::new();
    let mut loop_bodies: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for l in loops.all() {
        let header = analysis.cfg().block_id(l.header);
        headers.insert(header);
        let mut modified: HashSet<RegId> = HashSet::new();
        let mut frees = false;
        let mut body: Vec<BlockId> = Vec::new();
        for &node in &l.body {
            let bid = analysis.cfg().block_id(node);
            body.push(bid);
            if let Some(b) = f.block(bid) {
                modified.extend(b.params.iter().map(|(r, _)| *r));
                for inst in &b.insts {
                    if let Some(r) = inst.defined_reg() {
                        modified.insert(r);
                    }
                    if matches!(inst, Inst::Dealloc { .. }) {
                        frees = true;
                    }
                }
            }
        }
        // Deterministic order: the havoc assigns fresh symbol ids in this order, and
        // a witness names induction symbols (`ind…`), so a `HashSet`'s arbitrary order
        // would make the reported counterexample non-deterministic.
        let mut modified: Vec<RegId> = modified.into_iter().collect();
        modified.sort_unstable_by_key(|r| r.0);
        loop_modified.insert(header, modified);
        loop_frees.insert(header, frees);
        loop_bodies.insert(header, body);
    }

    let mut ex = Explorer {
        ctx: ExprCtx::new(),
        fresh: 0,
        prov_ids: 0,
        bug_finding: limits.bug_finding,
        exported: limits.exported,
        assume_valid_params: limits.assume_valid_params,
        reg_ptr_hints,
        devirt,
        mmio_region,
        visits: 0,
        truncated: false,
        pruned_succs: FxHashSet::default(),
        visited_blocks: FxHashSet::default(),
        limits,
        // Trace length bound = the function's instruction count — the exact upper bound on how many
        // events a trace can hold (each event comes from one instruction), so it never truncates
        // artificially; the interleaving search's own budget bounds the cost of a long trace.
        race_trace_cap: f.blocks.iter().map(|b| b.insts.len()).sum::<usize>().max(1),
        deadline: limits.time_budget.map(|b| std::time::Instant::now() + b),
        scalar: HashMap::new(),
        mem: HashMap::new(),
        assumptions: HashSet::new(),
        analysis,
        zones,
        inductions,
        dominators,
        headers,
        loop_modified,
        loop_frees,
        loop_bodies,
        summaries: summaries.clone(),
        name_summaries: name_summaries.clone(),
        prov_grants: prov_grants.clone(),
        field_offsets: HashMap::new(),
        field_frontier: HashMap::new(),
        scalar_ptr_cause: classify_scalar_ptr_defs(f),
        global_rids: HashMap::new(),
        global_fnptrs: HashMap::new(),
        prove_cache: FxHashMap::default(),
        sym_memo: FxHashMap::default(),
        lock_classes: crate::lockclass::resolve_lock_classes(f),
        lock_edges: HashSet::new(),
        race_accesses: HashSet::new(),
        load_derived: load_derived_regs(f),
        race_trace: Vec::new(),
        // Opt-in Rust aliasing model: the shared-borrow register set + borrow-tag derivation
        // (both empty/default otherwise, so the model is inert when the flag is off).
        shared_borrow_regs: if limits.aliasing_model { shared_borrow_regs(f) } else { HashSet::new() },
        borrow_info: if limits.aliasing_model { borrow_info(f) } else { BorrowInfo::default() },
        f,
    };

    let mut env: FxHashMap<RegId, SymValue> = FxHashMap::default();
    let mut regions: Vec<SymRegion> = Vec::new();
    let mut facts: Vec<ExprId> = Vec::new();
    // A C `(buf, len)` pairing is a *convention*, not an ABI guarantee: a caller may pass a
    // length that does not describe the buffer, and the contract is trusted (it can prove an
    // access in bounds), so honouring it by default could turn a real overrun into a false PASS.
    // Off by default, therefore: drop the contract and let the parameter be uncontracted, which
    // is precisely the behaviour before the pairing existed. Rust's `SizeSpec::ParamElements`
    // (assumption `slice-abi`, no override) is unaffected — there the ABI does guarantee it.
    let gated: Vec<Option<PtrContract>>;
    let contracts: &[Option<PtrContract>] = if limits.assume_param_buffer_len {
        contracts
    } else {
        gated = contracts
            .iter()
            .map(|c| match c {
                Some(c) if c.assumption == Some(PARAM_BUFFER_LEN) => None,
                other => *other,
            })
            .collect();
        &gated
    };
    // Pass 1: every parameter without a pointer contract (so length parameters
    // a slice contract refers to are available in pass 2).
    for (i, (reg, ty)) in f.params.iter().enumerate() {
        if contracts.get(i).and_then(|c| c.as_ref()).is_none() {
            // Name scalar parameters `arg{i}` so a counterexample model is
            // readable; pointer parameters get the usual opaque placeholder.
            let v = if ty.is_ptr() {
                // **Typed-pointer sizing for an UNcontracted pointer parameter** (opt-in
                // `--assume-valid-params`): when the body indexes it as `gep %struct.T, ptr %p`,
                // the parameter designates a `struct T` of known size — the same rule already
                // applied to a loaded field pointer, an `inttoptr`, and a call result. Gives the
                // parameter a sized `assumed` region instead of an opaque pointer, so accesses
                // through it are decided. `assumed` ⇒ a constant offset past the recovered size
                // is not refuted (no false FAIL when the object is embedded in a larger one).
                match reg_ptr_hints.get(reg).copied().filter(|h| h.size > 0) {
                    Some(hint) if limits.assume_valid_params => {
                        // The C "context behind the struct" idiom (`tfm + 1`): under
                        // `--assume-struct-tail` the object is sized to cover the reach the code
                        // itself takes past the declared type, instead of stopping at it.
                        let tail = limits.assume_struct_tail && hint.tail > hint.size;
                        if tail {
                            ex.assumptions.insert(STRUCT_TAIL);
                        }
                        let size_e = ex.ctx.int(PTR_WIDTH, hint.region_size(tail) as u128);
                        let zero = ex.ctx.int(PTR_WIDTH, 0);
                        let nonneg = ex.ctx.cmp(SCmp::Sle, zero, size_e);
                        facts.push(nonneg);
                        let truth = ex.ctx.boolean(true);
                        let align = hint.region_align();
                        let rid = regions.len();
                        regions.push(SymRegion {
                            kind: RegionKind::Heap,
                            size: size_e,
                            base_align: align,
                            state: LifetimeState::Live,
                            perms: Permissions { read: true, write: true, exec: false },
                            contract: Some(PARAM_VALID),
                            size_nowrap: Some(truth),
                            sentinel: None,
                            user_controlled: false,
                            assumed: true,
                            prov_labels: FxHashSet::default(),
                        });
                        SymValue::Ptr(SymPointer {
                            prov: Prov::Region(rid),
                            offset: zero,
                            align,
                            borrow: None,
                        })
                    }
                    _ => ex.fresh_value(ty, POrigin::Param),
                }
            } else {
                let width = type_width(ty);
                let sym = ex.ctx.symbol(format!("arg{i}"), width);
                // Interprocedural scalar precondition: a NON-entry function's integer
                // parameter is bounded by the union of the ranges its (all visible) callers
                // pass — so an index derived from it is proven in bounds instead of flagged
                // at a value no caller can produce. Not applied to an adversarial entry,
                // whose parameters are attacker-controlled. Prove-only (a `caller-range`
                // assumption), so an out-of-range witness is not a real counterexample.
                // A parameter wider than the bit-precise domain (`MAX_WIDTH` = 128 bits — an
                // `i256`/`i512` crypto big-integer) cannot be encoded as a `BitVector`: building
                // the precondition constants would panic (`ctx.int(width>128, …)`). Skip the
                // seeding for such a parameter — it stays a free symbol (sound: no bound asserted,
                // never a false verdict). This unblocks whole-program scans of corpora containing
                // wide-integer code (crypto), where `scalar_pre` is populated and single-file
                // verification — which has none — never reached this construction.
                if !limits.exported && width <= csolver_solver::bitblast::MAX_WIDTH {
                    if let Some(Some((lo, hi))) = scalar_pre.get(i) {
                        let mask = |v: i128| if width >= 128 { v as u128 } else { (v as u128) & ((1u128 << width) - 1) };
                        let lo_e = ex.ctx.int(width, mask(*lo));
                        let hi_e = ex.ctx.int(width, mask(*hi));
                        let ge = ex.ctx.cmp(SCmp::Sle, lo_e, sym);
                        let le = ex.ctx.cmp(SCmp::Sle, sym, hi_e);
                        facts.push(ge);
                        facts.push(le);
                        ex.assumptions.insert(SCALAR_PRECONDITION);
                    }
                }
                SymValue::Scalar(sym)
            };
            env.insert(*reg, v);
        }
    }
    // Member-provenance seed stores, filled alongside the param regions below and
    // installed as the path's initial heap so the first load of each seeded field
    // reads back a valid pointer.
    let mut initial_heap: Vec<StoreRecord> = Vec::new();
    // Non-null opaque-provenance ids seeded from `SizeSpec::NonNull` contracts.
    let mut nonnull_provs: FxHashSet<u32> = FxHashSet::default();
    // Pass 2: contracted pointer parameters become known live regions.
    for (i, (reg, ty)) in f.params.iter().enumerate() {
        let Some(c) = contracts.get(i).and_then(|c| c.as_ref()) else {
            continue;
        };
        // A `nonnull`-only parameter is NOT a region — it is a non-null opaque pointer:
        // its provenance id is recorded so `NoNullDeref` proves through it (and derived
        // pointers), while bounds/liveness stay unknown (a `nonnull` pointer may dangle).
        if c.size == SizeSpec::NonNull {
            let v = ex.fresh_value(ty, POrigin::Param);
            if let SymValue::Ptr(SymPointer { prov: Prov::Unknown(_, Some(id)), .. }) = &v {
                nonnull_provs.insert(*id);
            }
            env.insert(*reg, v);
            continue;
        }
        let (size, assumption, nowrap) = match c.size {
            // A concrete byte size cannot wrap; nothing extra is needed (`true`).
            SizeSpec::Bytes(n) => {
                let truth = ex.ctx.boolean(true);
                (ex.ctx.int(PTR_WIDTH, n as u128), PARAM_CONTRACTS, Some(truth))
            }
            SizeSpec::ParamElements { len_param, elem_size } => {
                let len_reg = f.params[len_param as usize].0;
                let len_e = match env.get(&len_reg) {
                    Some(SymValue::Scalar(e)) => *e,
                    _ => ex.fresh_scalar(PTR_WIDTH),
                };
                // Rust's slice length is a `usize`, already pointer-width; a C length is
                // typically a narrower `int`/`u32`. Widen it before the multiply, or the size
                // expression mixes widths and no bound over it can be proved. Zero-extension is
                // the right widening: a length is unsigned, and the pointer arithmetic the
                // access performs zero-extends it the same way.
                let len_e = if ex.ctx.width(len_e) < PTR_WIDTH {
                    ex.ctx.zext(len_e, PTR_WIDTH)
                } else {
                    len_e
                };
                let es = ex.ctx.int(PTR_WIDTH, elem_size as u128);
                let size = ex.ctx.bin(BvOp::Mul, len_e, es);
                // A valid slice has `len * size_of::<T>() <= isize::MAX`, so the
                // length times the element size does not wrap (`slice-abi`).
                let nowrap = ex.size_no_wrap_fact(len_e, elem_size);
                (size, SLICE_ABI, Some(nowrap))
            }
            // An aggregate of unknown layout: a fresh symbolic size. Field accesses
            // are proved in bounds by construction (`struct-abi`), so the region is
            // prove-only (no refutation — `size_nowrap = None`).
            SizeSpec::Opaque => (ex.fresh_scalar(PTR_WIDTH), STRUCT_ABI, None),
            // Handled above (a non-region, non-null opaque pointer) — never reaches here.
            SizeSpec::NonNull => continue,
        };
        // A precondition-style contract (internal function / closure /
        // synthesized minimum) proves but never refutes: `size_nowrap = None`
        // switches the in-bounds obligation to prove-only.
        let nowrap = if c.refutable { nowrap } else { None };
        let zero = ex.ctx.int(PTR_WIDTH, 0);
        let nonneg = ex.ctx.cmp(SCmp::Sle, zero, size);
        facts.push(nonneg);
        let rid = regions.len();
        regions.push(SymRegion {
            kind: RegionKind::Heap,
            size,
            base_align: 1,
            state: LifetimeState::Live,
            perms: Permissions {
                read: c.readable,
                write: c.writable,
                exec: false,
            },
            // A synthesized contract names its own trust basis (e.g. the
            // internal-call-site derivation) instead of the declared-attribute
            // assumption its `SizeSpec` would imply.
            contract: Some(c.assumption.unwrap_or(assumption)),
            size_nowrap: nowrap,
            sentinel: c.sentinel,
            user_controlled: false,
            assumed: false,
            prov_labels: FxHashSet::default(),
        });
        env.insert(
            *reg,
            SymValue::Ptr(SymPointer {
                prov: Prov::Region(rid),
                offset: zero,
                align: c.align.max(1) as u64,
                borrow: None,
            }),
        );
        // Member-provenance: seed every field this parameter's call sites all fill
        // with a valid pointer. The pointee is a fresh live region; its address is
        // stored at the field's byte offset within this parameter's region — the
        // very offset the callee's `PtrOffset` field access computes — so the
        // load of the field reads back a pointer with provenance. Prove-only (a
        // precondition), so the seeded region never refutes.
        for fc in field_contracts.get(i).map(Vec::as_slice).unwrap_or(&[]) {
            let SizeSpec::Bytes(psize) = fc.pointee.size else { continue };
            let psize_e = ex.ctx.int(PTR_WIDTH, psize as u128);
            let prid = regions.len();
            regions.push(SymRegion {
                kind: RegionKind::Heap,
                size: psize_e,
                base_align: 1,
                state: LifetimeState::Live,
                perms: Permissions {
                    read: fc.pointee.readable,
                    write: fc.pointee.writable,
                    exec: false,
                },
                contract: Some(fc.pointee.assumption.unwrap_or(PARAM_CONTRACTS)),
                size_nowrap: None,
                sentinel: None,
                user_controlled: false,
                assumed: false,
                prov_labels: FxHashSet::default(),
            });
            let palign = fc.pointee.align.max(1) as u64;
            let off_e = ex.ctx.int(PTR_WIDTH, fc.offset as u128);
            initial_heap.push(StoreRecord {
                target: SymPointer { prov: Prov::Region(rid), offset: off_e, align: palign, borrow: None },
                value: SymValue::Ptr(SymPointer {
                    prov: Prov::Region(prid),
                    offset: zero,
                    align: palign,
                    borrow: None,
                }),
                size: PTR_WIDTH as u64 / 8,
            });
        }
    }
    // Referenced global/static definitions become regions that live for the
    // whole program: never freed, readable, writable iff not `constant`, with
    // an initializer (so a load from one is *not* an uninitialized read).
    // Sorted by name so region ids — and therefore every downstream id — are
    // deterministic.
    let mut names: Vec<String> = referenced_symbols(f)
        .into_iter()
        .filter(|n| globals.contains_key(n))
        .collect();
    names.sort();
    names.dedup();
    // Transitively include the **global targets** of constant `.field = &other_global`
    // initializers, so a `G->field->fn()` dispatch reaches `other_global`'s region and its
    // function-pointer table even when `other_global` is not referenced by name in this function.
    // A bounded closure (each name is expanded once); re-sorted for deterministic region ids.
    {
        let mut i = 0;
        while i < names.len() {
            if let Some(fields) = global_ptr_fields.get(&names[i]) {
                for (_, target) in fields.clone() {
                    if globals.contains_key(&target) && !names.contains(&target) {
                        names.push(target);
                    }
                }
            }
            i += 1;
        }
        names.sort();
        names.dedup();
    }
    let mut name_rid: HashMap<String, usize> = HashMap::new();
    for name in &names {
        let g = globals[name];
        let rid = regions.len();
        let size = ex.ctx.int(PTR_WIDTH, g.size as u128);
        let truth = ex.ctx.boolean(true);
        regions.push(SymRegion {
            kind: RegionKind::Global,
            size,
            // A global's base address is aligned to its declared `align`, so a
            // masked/guarded offset from it can be proved aligned (see
            // `check_access`). Unspecified alignment is 1 (proofs then fall back,
            // never assume).
            base_align: (g.align as u64).max(1),
            state: LifetimeState::Live,
            perms: Permissions { read: true, write: g.writable, exec: false },
            contract: Some(GLOBAL_MEMORY),
            size_nowrap: Some(truth),
            sentinel: None,
            user_controlled: false,
            assumed: false,
            prov_labels: FxHashSet::default(),
        });
        // A constant ops-struct/vtable global carries a devirtualisation table:
        // record it against the region id so a field load can resolve its target.
        if let Some(table) = global_fn_ptrs.get(name) {
            ex.global_fnptrs.insert(rid, table.iter().copied().collect());
        }
        ex.global_rids.insert(name.clone(), (rid, g.align.max(1) as u64));
        name_rid.insert(name.clone(), rid);
    }
    // Seed the constant `.field = &other_global` initializer stores: a load of `G.field` then
    // reads back a pointer to `other_global`'s region (via the ordinary store-load forwarding), so
    // the `G->field->fn()` dispatch resolves `field` to that region and the subsequent fn-ptr load
    // devirtualises through its table. Sound and unconditional — a constant global's initializer
    // is ground truth. Deterministic (iterates the sorted `names`).
    for name in &names {
        let (Some(fields), Some(&src_rid)) =
            (global_ptr_fields.get(name), name_rid.get(name)) else { continue };
        for (offset, target) in fields {
            let Some(&tgt_rid) = name_rid.get(target) else { continue };
            let zero = ex.ctx.int(PTR_WIDTH, 0);
            let off = ex.ctx.int(PTR_WIDTH, *offset as u128);
            let talign = (globals[target].align as u64).max(1);
            initial_heap.push(StoreRecord {
                target: SymPointer { prov: Prov::Region(src_rid), offset: off, align: 1, borrow: None },
                value: SymValue::Ptr(SymPointer {
                    prov: Prov::Region(tgt_rid),
                    offset: zero,
                    align: talign,
                    borrow: None,
                }),
                size: (PTR_WIDTH / 8) as u64,
            });
        }
    }

    // MMIO dispatch precondition (`Module::mmio_handlers`): a `MemoryRegionOps.read/.write`
    // handler `(void *opaque, hwaddr addr, unsigned size)` is only ever called by the memory
    // core, which guarantees `1 ≤ size ≤ 8` and (when the region size is known) `addr + size ≤
    // region_size`. These are real invariants of how the handler is invoked, so seeding them is
    // precision — it removes the false FAILs that arise from treating a handler as an entry with
    // a free `addr`/`size` (`addr` a huge register offset the dispatch never forms, `size` 0 or
    // enormous), while a genuine `region_size > backing array` overrun still refutes.
    if let Some(handler) = ex.mmio_region {
        if let (Some(SymValue::Scalar(addr)), Some(SymValue::Scalar(size))) =
            (f.params.get(1).and_then(|(r, _)| env.get(r)).cloned(),
             f.params.get(handler.size_param as usize).and_then(|(r, _)| env.get(r)).cloned())
        {
            let sw = ex.ctx.width(size);
            let one = ex.ctx.int(sw, 1);
            let eight = ex.ctx.int(sw, 8);
            facts.push(ex.ctx.cmp(SCmp::Ule, one, size));
            facts.push(ex.ctx.cmp(SCmp::Ule, size, eight));
            if let Some(bytes) = handler.region_size {
                let size64 = if sw < PTR_WIDTH { ex.ctx.zext(size, PTR_WIDTH) } else { size };
                let end = ex.ctx.bin(BvOp::Add, addr, size64);
                let cap = ex.ctx.int(PTR_WIDTH, bytes as u128);
                // `addr ≤ region_size` bounds the offset AND (since region_size is a small
                // constant) rules out a near-`u64::MAX` addr whose `addr + size` would *wrap*
                // below the cap — without it the `end ≤ cap` fact alone would spuriously admit
                // a huge offset. `end ≤ cap` then pins the exact tail. Both hold in QEMU (the
                // dispatch forms `addr` as a valid in-region offset).
                facts.push(ex.ctx.cmp(SCmp::Ule, addr, cap));
                facts.push(ex.ctx.cmp(SCmp::Ule, end, cap));
            }
        }
    }

    let state = PathState {
        env,
        regions,
        pathcond: Vec::new(),
        facts,
        heap: initial_heap,
        unwritten_reads: FxHashMap::default(),
        ref_regions: FxHashMap::default(),
        opaque_labels: FxHashMap::default(),
        nonnull_provs,
        region_borrows: FxHashMap::default(),
        tainted: FxHashMap::default(),
        typestates: FxHashMap::default(),
        refcounts: FxHashMap::default(),
        rcu_depth: 0,
        irq_off: 0,
        percpu: FxHashSet::default(),
        fn_ptrs: FxHashMap::default(),
        locks_held: FxHashSet::default(),
        spin_held: FxHashSet::default(),
        held_classes: FxHashMap::default(),
        user_fetches: FxHashSet::default(),
        freed_bases: FxHashSet::default(),
        exact: true,
    };
    ex.run_merged(state);

    if ex.truncated {
        return SymbolicReport {
            truncated: true,
            ..Default::default()
        };
    }

    let decided = ex
        .scalar
        .into_iter()
        .map(|(k, agg)| {
            let outcome = match agg.refutation {
                Some(model) => SymOutcome::Refuted(model),
                None if agg.all_proven => SymOutcome::Proven,
                None => SymOutcome::Unknown,
            };
            (k, outcome)
        })
        .collect();
    let mem = ex
        .mem
        .into_iter()
        .map(|(k, agg)| {
            (
                k,
                MemDecision {
                    proven: agg.all_proven,
                    refutation: agg.refutation,
                    predicate: agg.predicate,
                    residual: if agg.all_proven { String::new() } else { agg.residual },
                },
            )
        })
        .collect();
    let mut assumptions: Vec<String> = ex.assumptions.into_iter().map(String::from).collect();
    assumptions.sort();
    let mut lock_edges: Vec<(String, String)> = ex.lock_edges.into_iter().collect();
    lock_edges.sort();
    let mut race_accesses: Vec<(String, bool, Vec<String>)> = ex.race_accesses.into_iter().collect();
    race_accesses.sort();

    SymbolicReport {
        decided,
        mem,
        assumptions,
        lock_edges,
        race_accesses,
        race_trace: ex.race_trace,
        truncated: false,
        // Pruned into, never entered => every live path to it is proven infeasible.
        dead_blocks: ex.pruned_succs.difference(&ex.visited_blocks).copied().collect(),
    }
}
