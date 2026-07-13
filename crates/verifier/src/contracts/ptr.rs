use super::*;

/// Synthesize contracts for internal functions' uncontracted pointer
/// parameters, to a fixpoint. Returns an overlay map; declared contracts win.
///
/// The iteration is grounded *from below*: a parameter is contracted only in
/// the round where **all** its sites become derivable, and a site is derivable
/// only through declared contracts, constant allocas, or contracts created in
/// strictly earlier rounds — which are final by induction (their own inputs
/// were final when they were computed). So no contract ever justifies itself
/// through a cycle, values never change after creation, and the loop adds at
/// least one parameter per round or stops.
pub(crate) fn synthesize(
    module: &Module,
    closed_world: bool,
) -> HashMap<(FuncId, u32), PtrContract> {
    let mut acc: HashMap<(FuncId, u32), PtrContract> = HashMap::new();
    loop {
        let round = synthesize_round(module, &acc, closed_world);
        let mut grew = false;
        for (k, v) in round {
            grew |= acc.insert(k, v).is_none();
        }
        if !grew {
            return acc;
        }
    }
}

/// One synthesis round: derive using declared contracts plus the contracts
/// accumulated in earlier rounds (`prior`).
pub(crate) fn synthesize_round(
    module: &Module,
    prior: &HashMap<(FuncId, u32), PtrContract>,
    closed_world: bool,
) -> HashMap<(FuncId, u32), PtrContract> {
    let escaped = address_taken_names(module);

    // Eligible (callee, param-index) pairs: complete call sites (internal
    // linkage, or *any* function under closed-world), address never taken,
    // pointer-typed, no declared contract.
    let mut candidates: HashSet<(FuncId, u32)> = HashSet::new();
    for f in &module.functions {
        let complete = closed_world || module.internal.contains(&f.id);
        if !complete || escaped.contains(&f.name) {
            continue;
        }
        for (i, (_, ty)) in f.params.iter().enumerate() {
            let key = (f.id, i as u32);
            if ty.is_ptr()
                && !module.param_contracts.contains_key(&key)
                && !prior.contains_key(&key)
            {
                candidates.insert(key);
            }
        }
    }
    if candidates.is_empty() {
        return HashMap::new();
    }

    // Fold every call site's guarantee. `None` in the map = the parameter saw a
    // site it could not derive — permanently ineligible.
    let mut folded: HashMap<(FuncId, u32), Option<SiteGuarantee>> = HashMap::new();
    for caller in &module.functions {
        let defs = local_defs(caller, caller.id, &module.param_contracts, &module.layout, prior);
        for inst in caller.blocks.iter().flat_map(|b| &b.insts) {
            let Inst::Call { callee: Callee::Direct(g), args, .. } = inst else {
                continue;
            };
            let Some(callee) = module.function(*g) else { continue };
            // Positional argument/parameter correspondence is required.
            if args.len() != callee.params.len() {
                for i in 0..callee.params.len() as u32 {
                    if candidates.contains(&(*g, i)) {
                        folded.insert((*g, i), None);
                    }
                }
                continue;
            }
            for (i, arg) in args.iter().enumerate() {
                let key = (*g, i as u32);
                if !candidates.contains(&key) {
                    continue;
                }
                let site = derive_site(arg, &defs);
                let entry = folded.entry(key).or_insert(site);
                *entry = match (*entry, site) {
                    (Some(a), Some(b)) => Some(SiteGuarantee {
                        size: a.size.min(b.size),
                        align: a.align.min(b.align),
                        readable: a.readable && b.readable,
                        writable: a.writable && b.writable,
                    }),
                    _ => None,
                };
            }
        }
    }

    folded
        .into_iter()
        .filter_map(|(key, g)| {
            let g = g?;
            // Trust basis: internal linkage *proves* the call sites complete;
            // otherwise completeness rests on the closed-world assertion.
            let assumption = if module.internal.contains(&key.0) {
                INTERNAL_CALL_CONTRACT
            } else {
                CLOSED_WORLD_CONTRACT
            };
            Some((
                key,
                PtrContract {
                    size: SizeSpec::Bytes(g.size),
                    align: g.align,
                    readable: g.readable,
                    writable: g.writable,
                    assumption: Some(assumption),
                    // A synthesized contract is the *weakest* call-site
                    // guarantee; a witness against it may combine argument
                    // values no single caller produces — prove-only.
                    refutable: false,
                    sentinel: None,
                },
            ))
        })
        .collect()
}

/// Whole-program pointer-contract synthesis **without linking**: the same map as
/// `synthesize(&merge_modules(mods, …), closed_world)`, run over the separate
/// modules. Same fixpoint as [`synthesize`], each round delegating to
/// [`synthesize_round_program`]. `acc`/`prior` are keyed by merge-compatible global
/// ids.
#[allow(dead_code)] // wired into the verifier by Phase 2; until then only tests use it
pub(crate) fn synthesize_program(
    mods: &[&Module],
    closed_world: bool,
) -> HashMap<(FuncId, u32), PtrContract> {
    let mut acc: HashMap<(FuncId, u32), PtrContract> = HashMap::new();
    loop {
        let round = synthesize_round_program(mods, &acc, closed_world);
        let mut grew = false;
        for (k, v) in round {
            grew |= acc.insert(k, v).is_none();
        }
        if !grew {
            return acc;
        }
    }
}

/// One link-free synthesis round — the same as
/// `synthesize_round(&merge_modules(mods, …), prior, closed_world)` over the
/// separate modules: global escaped set (union), global declared contracts (each
/// module's remapped to global ids), each caller's call resolved to the same global
/// id the linked module would call directly (Direct in-module, Symbol cross-module),
/// and the weakest (intersection) call-site guarantee folded per candidate parameter.
pub(crate) fn synthesize_round_program(
    mods: &[&Module],
    prior: &HashMap<(FuncId, u32), PtrContract>,
    closed_world: bool,
) -> HashMap<(FuncId, u32), PtrContract> {
    let (name_to_id, remaps) = csolver_ir::merge_id_plan(mods);
    let layout = mods.first().map_or(csolver_ir::DataLayout::LP64, |m| m.layout);
    let mut global_fn: HashMap<FuncId, &csolver_ir::Function> = HashMap::new();
    let mut internal: HashSet<FuncId> = HashSet::new();
    let mut escaped: HashSet<String> = HashSet::new();
    let mut global_pc: HashMap<(FuncId, u32), PtrContract> = HashMap::new();
    for (mi, m) in mods.iter().enumerate() {
        escaped.extend(address_taken_names(m));
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

    let mut candidates: HashSet<(FuncId, u32)> = HashSet::new();
    for (&gid, f) in &global_fn {
        let complete = closed_world || internal.contains(&gid);
        if !complete || escaped.contains(&f.name) {
            continue;
        }
        for (i, (_, ty)) in f.params.iter().enumerate() {
            let key = (gid, i as u32);
            if ty.is_ptr() && !global_pc.contains_key(&key) && !prior.contains_key(&key) {
                candidates.insert(key);
            }
        }
    }
    if candidates.is_empty() {
        return HashMap::new();
    }

    let resolve = |mi: usize, callee: &Callee| -> Option<FuncId> {
        match callee {
            Callee::Direct(old) => remaps[mi].get(old).copied(),
            Callee::Symbol(nm) => name_to_id.get(nm).copied(),
            Callee::Indirect(_) => None,
        }
    };

    let mut folded: HashMap<(FuncId, u32), Option<SiteGuarantee>> = HashMap::new();
    for (mi, m) in mods.iter().enumerate() {
        for caller in &m.functions {
            let caller_gid = remaps[mi][&caller.id];
            let defs = local_defs(caller, caller_gid, &global_pc, &layout, prior);
            for inst in caller.blocks.iter().flat_map(|b| &b.insts) {
                let Inst::Call { callee, args, .. } = inst else { continue };
                let Some(g) = resolve(mi, callee) else { continue };
                let Some(callee_fn) = global_fn.get(&g) else { continue };
                if args.len() != callee_fn.params.len() {
                    for i in 0..callee_fn.params.len() as u32 {
                        if candidates.contains(&(g, i)) {
                            folded.insert((g, i), None);
                        }
                    }
                    continue;
                }
                for (i, arg) in args.iter().enumerate() {
                    let key = (g, i as u32);
                    if !candidates.contains(&key) {
                        continue;
                    }
                    let site = derive_site(arg, &defs);
                    let entry = folded.entry(key).or_insert(site);
                    *entry = match (*entry, site) {
                        (Some(a), Some(b)) => Some(SiteGuarantee {
                            size: a.size.min(b.size),
                            align: a.align.min(b.align),
                            readable: a.readable && b.readable,
                            writable: a.writable && b.writable,
                        }),
                        _ => None,
                    };
                }
            }
        }
    }

    folded
        .into_iter()
        .filter_map(|(key, g)| {
            let g = g?;
            let assumption = if internal.contains(&key.0) {
                INTERNAL_CALL_CONTRACT
            } else {
                CLOSED_WORLD_CONTRACT
            };
            Some((
                key,
                PtrContract {
                    size: SizeSpec::Bytes(g.size),
                    align: g.align,
                    readable: g.readable,
                    writable: g.writable,
                    assumption: Some(assumption),
                    refutable: false,
                    sentinel: None,
                },
            ))
        })
        .collect()
}
