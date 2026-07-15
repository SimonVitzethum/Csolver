use super::*;

pub(crate) fn verify_module_inner(
    module: &Module,
    config: &Config,
    threads: usize,
    ctx: Option<WholeProgramContext<'_>>,
) -> ModuleReport {
    // Promote non-escaping scalar stack slots to SSA first: unoptimized front-end
    // output spills locals (loop counters, pointer parameters) to allocas, which
    // defeats induction bounds and store-load provenance. Semantics-preserving, so
    // sound; it only lets the analysis see what `-O1` would have.
    let promoted = mem2reg::promote_module(module);
    let module = &promoted;
    let summaries = config.use_symbolic.then(|| summarize_module(module));
    // In whole-program mode the per-file synthesis MUST run open-world — a single file
    // is not the whole program, so its call sites are incomplete — and the closed-world
    // precision is supplied instead by the name-keyed overlay (`ctx`), which was derived
    // over the whole tree. Outside whole-program mode, honour the caller's setting.
    let unit_cw = if ctx.is_some() { false } else { config.closed_world };
    // Interprocedural: contracts synthesized from the (complete) call sites of
    // internal functions overlay the declared ones (declared always wins).
    let synthesized = contracts::synthesize(module, unit_cw);
    // Interprocedural member-provenance: which fields of a contracted parameter
    // every call site fills with a valid pointer (empty unless internal/closed).
    let field_synth = contracts::synthesize_fields(module, &synthesized, unit_cw);
    // Interprocedural scalar value-range preconditions: the range each integer parameter
    // is bounded to by the union of its (complete) call sites — so a callee proves an index
    // in bounds using its callers' validation (e.g. a `switch (optname) case A..B:` guard).
    let scalar_synth = contracts::synthesize_scalars(module, unit_cw);
    let mut functions = verify_functions(
        module,
        summaries.as_ref(),
        ctx,
        &synthesized,
        &field_synth,
        &scalar_synth,
        config,
        threads,
    );

    // Assign global obligation ids by a serial pass in function order — this
    // reproduces exactly the sequential ids a serial run would give, regardless of
    // the order in which the workers finished.
    let mut next_id: u32 = 0;
    for fr in &mut functions {
        for o in &mut fr.outcomes {
            o.obligation.id = ObligationId(next_id);
            next_id += 1;
        }
    }

    // Functions a frontend could not lower are reported as UNKNOWN (never a
    // silent omission), so the module verdict reflects that they were not
    // verified.
    for (uname, reason) in &module.unanalyzed {
        let id = ObligationId(next_id);
        next_id += 1;
        let location = Location::level_only(config.level).in_function(uname.as_str());
        let obligation = ProofObligation::new(
            id,
            SafetyProperty::ValidReference,
            location,
            "the function body is analyzable",
        );
        let result = ObligationResult::Open {
            residual: vec![ResidualObligation {
                predicate: "whole function body".into(),
                reason: format!("not analyzed by the frontend: {reason}"),
            }],
            suggested: vec![],
        };
        functions.push(FunctionReport {
            function: uname.clone(),
            verdict: Verdict::Unknown,
            outcomes: vec![ObligationOutcome { obligation, result }],
            truncated: false,
            lock_edges: Vec::new(),
            race_accesses: Vec::new(),
            race_trace: Vec::new(),
        });
    }

    let verdict = Verdict::combine_all(functions.iter().map(|f| f.verdict));

    // Surface — once each — every assumption any proof in the module depends on.
    let mut ids: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for func in &functions {
        for o in &func.outcomes {
            if let ObligationResult::Proven(tree) = &o.result {
                ids.extend(tree.assumptions.iter().cloned());
            }
        }
    }
    let assumptions = ids.into_iter().map(assumption_record).collect();

    ModuleReport {
        module: module.name.clone(),
        verdict,
        functions,
        assumptions,
    }
}

/// Verify one function in isolation with a *local* obligation-id counter (the
/// caller renumbers globally). Self-contained: its own solver context, read-only
/// summaries/contracts/config — so it is safe to run on any worker thread.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_one_function(
    module: &Module,
    summaries: Option<&HashMap<FuncId, Summary>>,
    ctx: Option<WholeProgramContext<'_>>,
    synthesized: &HashMap<(FuncId, u32), PtrContract>,
    field_synth: &HashMap<(FuncId, u32), Vec<FieldContract>>,
    scalar_synth: &HashMap<(FuncId, u32), (i128, i128)>,
    config: &Config,
    f: &Function,
) -> FunctionReport {
    let mut contracts = module.contracts_for(f);
    for (i, slot) in contracts.iter_mut().enumerate() {
        if slot.is_none() {
            *slot = synthesized.get(&(f.id, i as u32)).copied();
        }
        // Opt-in `assume_valid_params`: a still-uncontracted raw pointer parameter of
        // known pointee size becomes a prove-only, valid, correctly-sized region under
        // the `param-valid` assumption (the framework passes a valid pointer at entry).
        if slot.is_none() && config.assume_valid_params {
            if let Some(&(size, align)) = module.raw_ptr_hints.get(&(f.id, i as u32)) {
                // The C "context behind the struct" idiom (`crypto_skcipher_ctx(tfm)` is
                // `tfm + 1`): the code navigates *past* the declared type, so the object is an
                // allocation of the struct plus a trailing context. Debug info only ever names
                // the struct, so the pointee size alone stops at its end and every access into
                // the tail stays UNKNOWN. Under `--assume-struct-tail` the region covers the
                // reach the code itself takes (`PtrHint::tail`, keyed by the parameter's
                // register). Off by default — the tail's real size is known only at the
                // allocation site, which per-file kernel IR does not contain.
                let size = match module.reg_ptr_hints.get(&(f.id, f.params[i].0)) {
                    Some(h) if config.assume_struct_tail => size.max(h.tail),
                    _ => size,
                };
                // A valid instance is naturally aligned; when debug info omits the
                // alignment, derive it from the size (a type's size is a multiple of
                // its alignment) — the largest power of two dividing it, capped at 16
                // (`max_align_t`) — so an aligned field access proves.
                let derived = 1u32 << size.trailing_zeros().min(4);
                *slot = Some(PtrContract {
                    assumption: Some("param-valid"),
                    refutable: false,
                    size: SizeSpec::Bytes(size),
                    align: align.max(derived).max(1),
                    readable: true,
                    writable: true,
                    sentinel: None,
                });
            }
        }
        // An internal function's (or closure's) contract is a caller-established
        // precondition: the guard lives at the call sites, so a witness picked
        // freely from the parameter space may never occur in the real program.
        // Prove-only — refuting it reported false FAILs on bytes' closures.
        if module.internal.contains(&f.id) {
            if let Some(c) = slot {
                c.refutable = false;
            }
        }
    }
    // Per-parameter member-provenance field contracts (empty vec = none).
    let mut field_contracts: Vec<Vec<FieldContract>> = (0..f.params.len())
        .map(|i| field_synth.get(&(f.id, i as u32)).cloned().unwrap_or_default())
        .collect();
    // Per-parameter scalar value-range preconditions (None = unconstrained).
    let mut scalar_pre: Vec<Option<(i128, i128)>> = (0..f.params.len())
        .map(|i| scalar_synth.get(&(f.id, i as u32)).copied())
        .collect();

    // Whole-program precondition overlay (2b): for a **linkage-external** function, lay
    // its whole-tree preconditions (from the streaming facts, keyed by name) over the
    // per-file (open-world) ones — the cross-file caller→callee validation flow that
    // linking provided, without linking. Gated on external linkage so a file-local
    // `static` never picks up an unrelated same-named external's contract. Sound only
    // because these facts were extracted closed-world (the driver's responsibility); the
    // maps are empty otherwise, making this a no-op. They reproduce exactly what a linked
    // closed-world synthesis would assign (the facts are bit-identical), including each
    // contract's baked-in refutability.
    if let Some(ctx) = ctx {
        if !module.internal.contains(&f.id) {
            for i in 0..f.params.len() as u32 {
                let key = (f.name.clone(), i);
                if let Some(&range) = ctx.name_scalars.get(&key) {
                    scalar_pre[i as usize] = Some(range);
                }
                // A declared / `assume_valid_params` contract still wins (as synthesized
                // never overrides declared); only fill an otherwise-uncontracted pointer.
                if contracts[i as usize].is_none() {
                    if let Some(&c) = ctx.name_ptr_contracts.get(&key) {
                        contracts[i as usize] = Some(c);
                    }
                }
                if let Some(fc) = ctx.name_field_contracts.get(&key) {
                    if !fc.is_empty() {
                        field_contracts[i as usize] = fc.clone();
                    }
                }
            }
        }
    }

    // An entry policy (if given) decides attacker-reachability by name — the sound
    // kernel model, where LLVM external linkage does NOT mean userspace-reachable.
    let exported = match &config.entry_patterns {
        Some(pats) => matches_entry(&f.name, pats),
        None => !module.internal.contains(&f.id),
    };
    let empty_summaries = HashMap::new();
    let name_summaries = ctx.map(|c| c.name_summaries).unwrap_or(&empty_summaries);
    let mut local_id = 0u32;
    verify_function_with(
        f,
        summaries,
        name_summaries,
        &contracts,
        &field_contracts,
        &scalar_pre,
        &module.globals,
        &module.prov_grants,
        &module.global_fn_ptrs,
        // This function's register→pointee-size hints (from the typed geps that index each
        // register), used to size a loop-carried pointer under `--assume-valid-loop-ptrs`.
        &module
            .reg_ptr_hints
            .iter()
            .filter(|((fid, _), _)| *fid == f.id)
            .map(|((_, r), s)| (*r, *s))
            .collect(),
        // The MMIO dispatch bound applies wherever the handler is defined — including a handler
        // registered in another file (`register_read_memory`) and *including when it is an
        // auto-entry* (exported): it is a real dispatch invariant, not a caller convention, so it
        // is seeded unconditionally (unlike `scalar_pre`, which is caller-established and gated on
        // non-exported linkage). Resolve it from this file's own handlers, else the whole-program
        // context's name-keyed union.
        module
            .mmio_handlers
            .get(&f.name)
            .copied()
            .or_else(|| ctx.and_then(|c| c.name_mmio.get(&f.name).copied())),
        config,
        exported,
        &mut local_id,
    )
}

/// Verify every function, distributing them over `threads` workers. Work is pulled
/// from a shared atomic index (not fixed chunks), so a few slow functions do not
/// stall a whole worker — scalable to the machine's cores. Results are returned in
/// function order (sorted by index), so the caller's renumbering is deterministic.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_functions(
    module: &Module,
    summaries: Option<&HashMap<FuncId, Summary>>,
    ctx: Option<WholeProgramContext<'_>>,
    synthesized: &HashMap<(FuncId, u32), PtrContract>,
    field_synth: &HashMap<(FuncId, u32), Vec<FieldContract>>,
    scalar_synth: &HashMap<(FuncId, u32), (i128, i128)>,
    config: &Config,
    threads: usize,
) -> Vec<FunctionReport> {
    let fns = &module.functions;
    let n = fns.len();
    if threads <= 1 || n <= 1 {
        return fns
            .iter()
            .map(|f| verify_one_function(module, summaries, ctx, synthesized, field_synth, scalar_synth, config, f))
            .collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let out = std::sync::Mutex::new(Vec::<(usize, FunctionReport)>::with_capacity(n));
    std::thread::scope(|s| {
        for _ in 0..threads.min(n) {
            s.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if i >= n {
                    break;
                }
                let r = verify_one_function(
                    module, summaries, ctx, synthesized, field_synth, scalar_synth,
                    config, &fns[i],
                );
                // Recover from a poisoned lock (a worker panicked) rather than
                // cascading the panic — the collected data is still valid.
                out.lock().unwrap_or_else(std::sync::PoisonError::into_inner).push((i, r));
            });
        }
    });
    let mut v = out.into_inner().unwrap_or_else(std::sync::PoisonError::into_inner);
    v.sort_by_key(|&(i, _)| i);
    v.into_iter().map(|(_, r)| r).collect()
}
