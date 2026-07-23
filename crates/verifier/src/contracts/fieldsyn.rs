use super::*;

/// Interprocedural **member-provenance**: for each contracted pointer parameter,
/// which of its aggregate fields provably holds a *valid pointer*, folded to the
/// weakest guarantee across all (visible) call sites.
///
/// A raw pointer member (`Wrap.data: int32_t*`) carries no validity from its
/// type — but if every call site builds the aggregate by storing `&valid` into
/// that field before the call, the callee's load of it yields a valid pointer.
/// This recovers that, resting on the same call-site-completeness basis as
/// [`synthesize`] (internal linkage or closed-world). Returned per `(callee,
/// param)`; only for parameters that already carry a region contract (declared
/// or in `params`), so the engine has a region to attach the field to.
///
/// Soundness: a field is kept only if **every** site provably stores a valid
/// pointer there, with no clobber between the store and the call. The caller
/// scan is deliberately conservative — straight-line within a basic block, and
/// any intervening call, `memcpy`/`memset`, or free discards the slots (they
/// could rewrite the field) — so a missed store only ever *drops* a field
/// (UNKNOWN), never asserts one that a caller does not establish.
pub(crate) fn synthesize_fields(
    module: &Module,
    params: &HashMap<(FuncId, u32), PtrContract>,
    closed_world: bool,
) -> HashMap<(FuncId, u32), Vec<FieldContract>> {
    let escaped = address_taken_names(module);
    // (callee, param) → intersection of per-site field guarantees, keyed by byte
    // offset. `None` once a site provides nothing (a non-region argument), which
    // drops all fields.
    let mut folded: HashMap<(FuncId, u32), Option<HashMap<u64, SiteGuarantee>>> = HashMap::new();

    let eligible = |g: FuncId, i: u32| -> bool {
        let Some(f) = module.function(g) else { return false };
        let complete = closed_world || module.internal.contains(&f.id);
        complete
            && !escaped.contains(&f.name)
            && f.params.get(i as usize).is_some_and(|(_, t)| t.is_ptr())
            // The parameter must carry a region contract for a field to attach to.
            && (params.contains_key(&(g, i)) || module.param_contracts.contains_key(&(g, i)))
    };

    for caller in &module.functions {
        let defs = local_defs(caller, caller.id, &module.param_contracts, &module.layout, params, &module.reg_ptr_hints, false);
        for block in &caller.blocks {
            // Per-block straight-line state (reset at each block entry, so
            // cross-block field setup is conservatively not credited):
            //  - `field_of`: a register that is `root + constant byte offset`,
            //    built from `PtrOffset` chains rooted at a known region.
            //  - `slot`: which `(root, byte offset)` provably holds a valid ptr.
            //  - `escaped`: roots whose address may have leaked (passed to a call
            //    or stored into memory), so a later callee could reach and rewrite
            //    them — their slots are dropped on every subsequent call.
            let mut field_of: HashMap<RegId, (RegId, u64)> = HashMap::new();
            let mut slot: HashMap<(RegId, u64), SiteGuarantee> = HashMap::new();
            let mut escaped: HashSet<RegId> = HashSet::new();
            // The region root a pointer register refers to, if any (itself if it is
            // a root, or the base of its constant-offset chain).
            let root_of = |field_of: &HashMap<RegId, (RegId, u64)>, r: &RegId| -> Option<RegId> {
                if defs.contains_key(r) {
                    Some(*r)
                } else {
                    field_of.get(r).map(|(root, _)| *root)
                }
            };
            for inst in &block.insts {
                match inst {
                    // Track a constant-offset pointer relative to a region root.
                    Inst::PtrOffset { dst, base: Operand::Reg(base), index, elem } => {
                        let delta = match index {
                            Operand::Const(Const::Int(bv)) => u64::try_from(bv.unsigned())
                                .ok()
                                .and_then(|n| n.checked_mul(elem.size_bytes(&module.layout)?)),
                            _ => None,
                        };
                        match (delta, field_of.get(base).copied(), defs.contains_key(base)) {
                            // `(root + d0) + delta`. A tracked field pointer chains
                            // to its root *first* — a struct-field gep's intermediate
                            // (`tmp = base + 0`) is itself promoted to a region root
                            // by `local_defs` (for the `&a[k]` case), so without this
                            // precedence the field would re-root onto that
                            // intermediate instead of the aggregate actually passed.
                            (Some(d), Some((root, d0)), _) => {
                                if let Some(total) = d0.checked_add(d) {
                                    field_of.insert(*dst, (root, total));
                                }
                            }
                            // `root + delta`: `base` is a true region root.
                            (Some(d), None, true) => {
                                field_of.insert(*dst, (*base, d));
                            }
                            _ => {}
                        }
                    }
                    Inst::Store { ptr: Operand::Reg(pr), value, .. } => {
                        // A stored *value* that is a region pointer leaks that root.
                        if let Operand::Reg(vr) = value {
                            if let Some(r) = root_of(&field_of, vr) {
                                escaped.insert(r);
                                slot.retain(|(root, _), _| *root != r);
                            }
                        }
                        // Resolve the store target to a (root, offset) slot: either
                        // a tracked field pointer, or a region root itself (offset 0).
                        let target = field_of
                            .get(pr)
                            .copied()
                            .or_else(|| defs.contains_key(pr).then_some((*pr, 0)));
                        match target {
                            Some(slotkey) => match value {
                                Operand::Reg(vr) if defs.contains_key(vr) => {
                                    slot.insert(slotkey, defs[vr]);
                                }
                                // Storing an unknown value clears that slot.
                                _ => {
                                    slot.remove(&slotkey);
                                }
                            },
                            // A store through an untracked pointer could alias any
                            // field — conservatively discard everything.
                            None => slot.clear(),
                        }
                    }
                    Inst::Store { .. } => slot.clear(),
                    // Every call — direct, indirect, or to an external symbol — may
                    // write through the pointers it is handed. Harvest first (only a
                    // resolved, eligible *direct* callee can be credited), then apply
                    // the clobber for *all* call kinds so an external `clobber(&w)`
                    // that could rewrite the field is never silently ignored.
                    Inst::Call { callee, args, .. } => {
                        if let Callee::Direct(g) = callee {
                            // A root already escaped has no slots (cleared when it
                            // leaked), so it contributes nothing.
                            if args.len()
                                == module.function(*g).map_or(usize::MAX, |c| c.params.len())
                            {
                                for (i, arg) in args.iter().enumerate() {
                                    let key = (*g, i as u32);
                                    if !eligible(*g, i as u32) {
                                        continue;
                                    }
                                    let site: HashMap<u64, SiteGuarantee> = match arg {
                                        Operand::Reg(root) if defs.contains_key(root) => slot
                                            .iter()
                                            .filter(|((r, _), _)| r == root)
                                            .map(|((_, off), g)| (*off, *g))
                                            .collect(),
                                        // A non-region argument guarantees no fields.
                                        _ => HashMap::new(),
                                    };
                                    intersect_site(folded.entry(key).or_insert(None), site);
                                }
                            }
                        }
                        // This callee could write through any root it receives, or
                        // through any root that previously escaped (it may hold a
                        // stashed pointer). Drop exactly those roots' slots; a root
                        // that never leaked and is not passed here is unreachable to
                        // the callee, so its field guarantees survive.
                        for arg in args {
                            if let Operand::Reg(a) = arg {
                                if let Some(r) = root_of(&field_of, a) {
                                    escaped.insert(r);
                                }
                            }
                        }
                        slot.retain(|(root, _), _| !escaped.contains(root));
                    }
                    // A `memcpy`/`memset` writes only through its destination — the
                    // root that pointer denotes (plus escaped roots). A local buffer
                    // initializer (`char buf[16] = {0}` → a `memset` of `buf`) must
                    // not wipe an unrelated field guarantee. If the destination does
                    // not root to a known region, conservatively discard everything.
                    Inst::MemIntrinsic { dst: Operand::Reg(d), .. } => {
                        match root_of(&field_of, d) {
                            Some(r) => {
                                escaped.insert(r);
                                slot.retain(|(root, _), _| !escaped.contains(root));
                            }
                            None => slot.clear(),
                        }
                    }
                    // An intrinsic, an unresolvable memcpy target, or a free may
                    // write through a pointer we cannot resolve — discard all.
                    Inst::Intrinsic { .. } | Inst::MemIntrinsic { .. } | Inst::Dealloc { .. } => {
                        slot.clear()
                    }
                    _ => {}
                }
            }
        }
    }

    folded
        .into_iter()
        .filter_map(|(key, fields)| {
            let fields = fields?;
            if fields.is_empty() {
                return None;
            }
            let mut v: Vec<FieldContract> = fields
                .into_iter()
                .map(|(offset, g)| FieldContract {
                    offset,
                    pointee: PtrContract {
                        size: SizeSpec::Bytes(g.size),
                        align: g.align,
                        readable: g.readable,
                        writable: g.writable,
                        assumption: Some(if module.internal.contains(&key.0) {
                            INTERNAL_CALL_CONTRACT
                        } else {
                            CLOSED_WORLD_CONTRACT
                        }),
                        refutable: false,
                        sentinel: None,
                    },
                })
                .collect();
            v.sort_by_key(|fc| fc.offset);
            Some((key, v))
        })
        .collect()
}

/// Whole-program member-provenance **without linking**: the same map as
/// `synthesize_fields(&merge_modules(mods, …), params, closed_world)`, over the
/// separate modules. Global escaped set / declared contracts / callee resolution
/// as in [`synthesize_program`]; the per-caller field-slot analysis is body-local,
/// hence identical to the linked one. `params` (the whole-program pointer contracts)
/// and the result are keyed by merge-compatible global ids.
#[allow(dead_code)] // wired into the verifier by Phase 2; until then only tests use it
pub(crate) fn synthesize_fields_program(
    mods: &[&Module],
    params: &HashMap<(FuncId, u32), PtrContract>,
    closed_world: bool,
) -> HashMap<(FuncId, u32), Vec<FieldContract>> {
    let (name_to_id, remaps) = csolver_ir::merge_id_plan(mods);
    let layout = mods.first().map_or(csolver_ir::DataLayout::LP64, |m| m.layout);
    let mut global_fn: HashMap<FuncId, &csolver_ir::Function> = HashMap::new();
    let mut internal: HashSet<FuncId> = HashSet::new();
    let mut escaped_names: HashSet<String> = HashSet::new();
    let mut global_pc: HashMap<(FuncId, u32), PtrContract> = HashMap::new();
    for (mi, m) in mods.iter().enumerate() {
        escaped_names.extend(address_taken_names(m));
        for f in &m.functions {
            let gid = remaps[mi][&f.id];
            global_fn.insert(gid, f);
            if m.internal.contains(&f.id) {
                internal.insert(gid);
            }
        }
        for (&(fid, idx), c) in &m.param_contracts {
            global_pc.insert((remaps[mi][&fid], idx), *c);
        }
    }

    let eligible = |g: FuncId, i: u32| -> bool {
        let Some(f) = global_fn.get(&g) else { return false };
        let complete = closed_world || internal.contains(&g);
        complete
            && !escaped_names.contains(&f.name)
            && f.params.get(i as usize).is_some_and(|(_, t)| t.is_ptr())
            && (params.contains_key(&(g, i)) || global_pc.contains_key(&(g, i)))
    };

    // Field synthesis does not use A2 pointer-hint grounding (scoped to pointer contracts).
    let no_hints: HashMap<(FuncId, RegId), PtrHint> = HashMap::new();
    let mut folded: HashMap<(FuncId, u32), Option<HashMap<u64, SiteGuarantee>>> = HashMap::new();
    for (mi, m) in mods.iter().enumerate() {
        let resolve = |callee: &Callee| -> Option<FuncId> {
            match callee {
                Callee::Direct(old) => remaps[mi].get(old).copied(),
                Callee::Symbol(nm) => name_to_id.get(nm).copied(),
                Callee::Indirect(_) => None,
            }
        };
        for caller in &m.functions {
            let caller_gid = remaps[mi][&caller.id];
            let defs = local_defs(caller, caller_gid, &global_pc, &layout, params, &no_hints, false);
            for block in &caller.blocks {
                let mut field_of: HashMap<RegId, (RegId, u64)> = HashMap::new();
                let mut slot: HashMap<(RegId, u64), SiteGuarantee> = HashMap::new();
                let mut escaped: HashSet<RegId> = HashSet::new();
                let root_of = |field_of: &HashMap<RegId, (RegId, u64)>, r: &RegId| -> Option<RegId> {
                    if defs.contains_key(r) {
                        Some(*r)
                    } else {
                        field_of.get(r).map(|(root, _)| *root)
                    }
                };
                for inst in &block.insts {
                    match inst {
                        Inst::PtrOffset { dst, base: Operand::Reg(base), index, elem } => {
                            let delta = match index {
                                Operand::Const(Const::Int(bv)) => u64::try_from(bv.unsigned())
                                    .ok()
                                    .and_then(|n| n.checked_mul(elem.size_bytes(&layout)?)),
                                _ => None,
                            };
                            match (delta, field_of.get(base).copied(), defs.contains_key(base)) {
                                (Some(d), Some((root, d0)), _) => {
                                    if let Some(total) = d0.checked_add(d) {
                                        field_of.insert(*dst, (root, total));
                                    }
                                }
                                (Some(d), None, true) => {
                                    field_of.insert(*dst, (*base, d));
                                }
                                _ => {}
                            }
                        }
                        Inst::Store { ptr: Operand::Reg(pr), value, .. } => {
                            if let Operand::Reg(vr) = value {
                                if let Some(r) = root_of(&field_of, vr) {
                                    escaped.insert(r);
                                    slot.retain(|(root, _), _| *root != r);
                                }
                            }
                            let target = field_of
                                .get(pr)
                                .copied()
                                .or_else(|| defs.contains_key(pr).then_some((*pr, 0)));
                            match target {
                                Some(slotkey) => match value {
                                    Operand::Reg(vr) if defs.contains_key(vr) => {
                                        slot.insert(slotkey, defs[vr]);
                                    }
                                    _ => {
                                        slot.remove(&slotkey);
                                    }
                                },
                                None => slot.clear(),
                            }
                        }
                        Inst::Store { .. } => slot.clear(),
                        Inst::Call { callee, args, .. } => {
                            if let Some(g) = resolve(callee) {
                                if args.len()
                                    == global_fn.get(&g).map_or(usize::MAX, |c| c.params.len())
                                {
                                    for (i, arg) in args.iter().enumerate() {
                                        let key = (g, i as u32);
                                        if !eligible(g, i as u32) {
                                            continue;
                                        }
                                        let site: HashMap<u64, SiteGuarantee> = match arg {
                                            Operand::Reg(root) if defs.contains_key(root) => slot
                                                .iter()
                                                .filter(|((r, _), _)| r == root)
                                                .map(|((_, off), g)| (*off, *g))
                                                .collect(),
                                            _ => HashMap::new(),
                                        };
                                        intersect_site(folded.entry(key).or_insert(None), site);
                                    }
                                }
                            }
                            for arg in args {
                                if let Operand::Reg(a) = arg {
                                    if let Some(r) = root_of(&field_of, a) {
                                        escaped.insert(r);
                                    }
                                }
                            }
                            slot.retain(|(root, _), _| !escaped.contains(root));
                        }
                        Inst::MemIntrinsic { dst: Operand::Reg(d), .. } => {
                            match root_of(&field_of, d) {
                                Some(r) => {
                                    escaped.insert(r);
                                    slot.retain(|(root, _), _| !escaped.contains(root));
                                }
                                None => slot.clear(),
                            }
                        }
                        Inst::Intrinsic { .. } | Inst::MemIntrinsic { .. } | Inst::Dealloc { .. } => {
                            slot.clear()
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    folded
        .into_iter()
        .filter_map(|(key, fields)| {
            let fields = fields?;
            if fields.is_empty() {
                return None;
            }
            let mut v: Vec<FieldContract> = fields
                .into_iter()
                .map(|(offset, g)| FieldContract {
                    offset,
                    pointee: PtrContract {
                        size: SizeSpec::Bytes(g.size),
                        align: g.align,
                        readable: g.readable,
                        writable: g.writable,
                        assumption: Some(if internal.contains(&key.0) {
                            INTERNAL_CALL_CONTRACT
                        } else {
                            CLOSED_WORLD_CONTRACT
                        }),
                        refutable: false,
                        sentinel: None,
                    },
                })
                .collect();
            v.sort_by_key(|fc| fc.offset);
            Some((key, v))
        })
        .collect()
}
