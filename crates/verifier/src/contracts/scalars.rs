use super::*;

/// The interval of a call-site argument (the value flowing into a parameter),
/// as a finite `[lo, hi]` — `None` if it is not a bounded integer there.
pub(crate) fn arg_interval(arg: &Operand, iv: &IntervalAnalysis, block: BlockId) -> Option<(i128, i128)> {
    match arg {
        Operand::Const(Const::Int(bv)) => Some((bv.signed(), bv.signed())),
        Operand::Reg(r) => {
            let interval = iv.entry_interval(block, *r);
            let (Bound::Fin(lo), Bound::Fin(hi)) = (interval.lower()?, interval.upper()?) else {
                return None;
            };
            (lo <= hi).then_some((lo, hi))
        }
        _ => None,
    }
}

/// Interprocedural **scalar value-range preconditions**. For each integer parameter of a
/// function whose call sites are provably complete (internal linkage, or any function under
/// closed-world), take the **union** of the interval the argument holds at every call site:
/// the callee may then assume `param ∈ [lo, hi]`, since the union covers every value any
/// visible caller can pass. This is the interprocedural analogue of the pointer-contract
/// synthesis (same completeness/soundness basis), for scalars — e.g. a `switch (optname)
/// case A..B:` guard at the call site bounds the callee's `optname`, so an array index
/// `t[optname - A]` inside the callee is proven in-bounds instead of flagged at `optname =
/// UINT_MAX` no caller can produce. Prove-only (an out-of-range witness is the caller's
/// fault). Single pass — scalar ranges do not feed one another.
pub(crate) fn synthesize_scalars(
    module: &Module,
    closed_world: bool,
) -> HashMap<(FuncId, u32), (i128, i128)> {
    let escaped = address_taken_names(module);
    let mut candidates: HashSet<(FuncId, u32)> = HashSet::new();
    let mut candidate_callees: HashSet<FuncId> = HashSet::new();
    for f in &module.functions {
        let complete = closed_world || module.internal.contains(&f.id);
        if !complete || escaped.contains(&f.name) {
            continue;
        }
        for (i, (_, ty)) in f.params.iter().enumerate() {
            if matches!(ty, Type::Int { .. }) {
                candidates.insert((f.id, i as u32));
                candidate_callees.insert(f.id);
            }
        }
    }
    if candidates.is_empty() {
        return HashMap::new();
    }

    // Fold every call site's argument interval by UNION. `None` = a site whose argument we
    // could not bound — the parameter is then left unconstrained (permanently ineligible).
    let mut folded: HashMap<(FuncId, u32), Option<(i128, i128)>> = HashMap::new();
    for caller in &module.functions {
        let calls_candidate = caller.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
            matches!(inst, Inst::Call { callee: Callee::Direct(g), .. } if candidate_callees.contains(g))
        });
        if !calls_candidate {
            continue;
        }
        let iv = analyze_intervals(caller);
        for block in &caller.blocks {
            for inst in &block.insts {
                let Inst::Call { callee: Callee::Direct(g), args, .. } = inst else {
                    continue;
                };
                if !candidate_callees.contains(g) {
                    continue;
                }
                let Some(callee) = module.function(*g) else { continue };
                if args.len() != callee.params.len() {
                    for i in 0..callee.params.len() as u32 {
                        if candidates.contains(&(*g, i)) {
                            folded.insert((*g, i), None);
                        }
                    }
                    continue;
                }
                // The caller's own MMIO dispatch bound, if it is a handler: its `size` parameter
                // is `[1, 8]` even though its body has no guard that the interval analysis could
                // see. Propagating that to a helper it calls (`register_read_memory(regs, addr,
                // size)`) is what removes the residual shift/div false positives in dispatch
                // helpers — the bound flows from the handler to the helper's `size` parameter.
                let caller_mmio_size_reg = module
                    .mmio_handlers
                    .get(&caller.name)
                    .and_then(|h| caller.params.get(h.size_param as usize))
                    .map(|(r, _)| *r);
                for (i, arg) in args.iter().enumerate() {
                    let key = (*g, i as u32);
                    if !candidates.contains(&key) {
                        continue;
                    }
                    let site = match arg {
                        Operand::Reg(r) if Some(*r) == caller_mmio_size_reg => Some((1, 8)),
                        _ => arg_interval(arg, &iv, block.id),
                    };
                    let entry = folded.entry(key).or_insert(site);
                    *entry = match (*entry, site) {
                        (Some((la, ha)), Some((lb, hb))) => Some((la.min(lb), ha.max(hb))),
                        _ => None,
                    };
                }
            }
        }
    }

    folded
        .into_iter()
        .filter_map(|(k, v)| {
            let (lo, hi) = v?;
            // A full-width range constrains nothing; drop it to avoid a useless assumption.
            (lo > i64::MIN as i128 || hi < i64::MAX as i128).then_some((k, (lo, hi)))
        })
        .collect()
}

/// Body-free, incrementally-built facts for whole-program scalar preconditions —
/// the `SummaryFacts` analogue for [`synthesize_scalars`]. Each module is folded in
/// with `push_module` (which runs its body-local interval analysis and records every
/// call site's per-argument interval) and may then be dropped; `finalize` resolves
/// callees by name, unions each candidate parameter's intervals across all call
/// sites, and drops full-width ranges. The escaped set is the **global union** of
/// every module's address-taken names — a function whose address leaks in ANY module
/// is excluded everywhere. That globality is the one soundness-critical point: a
/// per-file escaped check would let a cross-module address-taken function receive an
/// unsound precondition, i.e. a false PASS. Ids match `merge_modules`.
#[allow(dead_code)] // wired into the verifier by Phase 2; until then only tests use it
#[derive(Default)]
pub(crate) struct ScalarFacts {
    pub(crate) next: u32,
    pub(crate) name_to_id: HashMap<String, FuncId>,
    pub(crate) escaped: HashSet<String>,
    pub(crate) internal: Vec<bool>,
    pub(crate) name: Vec<String>,
    pub(crate) int_params: Vec<Vec<u32>>,
    pub(crate) param_count: Vec<usize>,
    pub(crate) sites: Vec<Vec<ScalarCall>>,
}

/// A call site's callee, unresolved until `finalize` (indirect calls are dropped).
#[allow(dead_code)]
pub(crate) enum ScalarCallee {
    Id(FuncId),
    Name(String),
}

/// One call site: its callee and the interval each argument held there.
#[allow(dead_code)]
pub(crate) struct ScalarCall {
    pub(crate) callee: ScalarCallee,
    pub(crate) arg_intervals: Vec<Option<(i128, i128)>>,
}

#[allow(dead_code)]
impl ScalarFacts {
    /// Fold one module in (droppable afterwards): record each function's linkage,
    /// integer parameters and arity, extend the global escaped set with its
    /// address-taken names, and extract every call site's per-argument interval.
    pub(crate) fn push_module(&mut self, m: &Module) {
        let base = self.next;
        let local: HashMap<FuncId, FuncId> = m
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.id, FuncId(base + i as u32)))
            .collect();
        self.escaped.extend(address_taken_names(m));
        for f in &m.functions {
            if !m.internal.contains(&f.id) {
                self.name_to_id.entry(f.name.clone()).or_insert(local[&f.id]);
            }
            self.internal.push(m.internal.contains(&f.id));
            self.name.push(f.name.clone());
            self.int_params.push(
                f.params
                    .iter()
                    .enumerate()
                    .filter(|(_, (_, ty))| matches!(ty, Type::Int { .. }))
                    .map(|(i, _)| i as u32)
                    .collect(),
            );
            self.param_count.push(f.params.len());
            let iv = analyze_intervals(f);
            // If this caller is an MMIO dispatch handler, its `size` parameter is `[1, 8]` (the
            // dispatch guarantee) though its body carries no guard the interval analysis sees.
            // Passing that reg to a helper propagates the bound cross-function — the whole-program
            // analogue of the same override in `synthesize_scalars`.
            let mmio_size_reg = m
                .mmio_handlers
                .get(&f.name)
                .and_then(|h| f.params.get(h.size_param as usize))
                .map(|(r, _)| *r);
            let mut sites = Vec::new();
            for block in &f.blocks {
                for inst in &block.insts {
                    let Inst::Call { callee, args, .. } = inst else { continue };
                    let callee = match callee {
                        Callee::Direct(old) => match local.get(old) {
                            Some(&g) => ScalarCallee::Id(g),
                            None => continue,
                        },
                        Callee::Symbol(nm) => ScalarCallee::Name(nm.clone()),
                        Callee::Indirect(_) => continue,
                    };
                    let arg_intervals = args
                        .iter()
                        .map(|a| match a {
                            Operand::Reg(r) if Some(*r) == mmio_size_reg => Some((1, 8)),
                            _ => arg_interval(a, &iv, block.id),
                        })
                        .collect();
                    sites.push(ScalarCall { callee, arg_intervals });
                }
            }
            self.sites.push(sites);
        }
        self.next += m.functions.len() as u32;
    }

    /// Absorb another fact set built in parallel, shifting its ids up by `self.next`.
    pub(crate) fn merge(&mut self, other: ScalarFacts) {
        let off = self.next;
        for (name, id) in other.name_to_id {
            self.name_to_id.entry(name).or_insert(FuncId(id.0 + off));
        }
        self.escaped.extend(other.escaped);
        self.internal.extend(other.internal);
        self.name.extend(other.name);
        self.int_params.extend(other.int_params);
        self.param_count.extend(other.param_count);
        self.sites.extend(other.sites.into_iter().map(|mut sites| {
            for site in &mut sites {
                if let ScalarCallee::Id(g) = &mut site.callee {
                    *g = FuncId(g.0 + off);
                }
            }
            sites
        }));
        self.next += other.next;
    }

    /// Resolve callees by name, union each candidate parameter's call-site intervals,
    /// and drop full-width ranges — the same map as `synthesize_scalars`.
    pub(crate) fn finalize(self, closed_world: bool) -> HashMap<(FuncId, u32), (i128, i128)> {
        let n = self.name.len();
        let mut candidates: HashSet<(FuncId, u32)> = HashSet::new();
        let mut candidate_callees: HashSet<FuncId> = HashSet::new();
        for gid in 0..n {
            let complete = closed_world || self.internal[gid];
            if !complete || self.escaped.contains(&self.name[gid]) {
                continue;
            }
            for &i in &self.int_params[gid] {
                candidates.insert((FuncId(gid as u32), i));
                candidate_callees.insert(FuncId(gid as u32));
            }
        }
        if candidates.is_empty() {
            return HashMap::new();
        }
        let resolve = |c: &ScalarCallee| match c {
            ScalarCallee::Id(g) => Some(*g),
            ScalarCallee::Name(nm) => self.name_to_id.get(nm).copied(),
        };
        let mut folded: HashMap<(FuncId, u32), Option<(i128, i128)>> = HashMap::new();
        for gid in 0..n {
            for site in &self.sites[gid] {
                let Some(g) = resolve(&site.callee) else { continue };
                if !candidate_callees.contains(&g) {
                    continue;
                }
                let params = self.param_count[g.0 as usize];
                if site.arg_intervals.len() != params {
                    for i in 0..params as u32 {
                        if candidates.contains(&(g, i)) {
                            folded.insert((g, i), None);
                        }
                    }
                    continue;
                }
                for (i, site_iv) in site.arg_intervals.iter().enumerate() {
                    let key = (g, i as u32);
                    if !candidates.contains(&key) {
                        continue;
                    }
                    let entry = folded.entry(key).or_insert(*site_iv);
                    *entry = match (*entry, *site_iv) {
                        (Some((la, ha)), Some((lb, hb))) => Some((la.min(lb), ha.max(hb))),
                        _ => None,
                    };
                }
            }
        }
        folded
            .into_iter()
            .filter_map(|(k, v)| {
                let (lo, hi) = v?;
                (lo > i64::MIN as i128 || hi < i64::MAX as i128).then_some((k, (lo, hi)))
            })
            .collect()
    }
}

/// Whole-program scalar preconditions **without linking**: the same map as
/// `synthesize_scalars(&merge_modules(mods, …), closed_world)`, streamed through
/// [`ScalarFacts`] (each module scanned once, its body then droppable). Kept as a
/// convenience wrapper and the in-memory equivalence oracle for the streaming path.
#[allow(dead_code)]
pub(crate) fn synthesize_scalars_program(
    mods: &[&Module],
    closed_world: bool,
) -> HashMap<(FuncId, u32), (i128, i128)> {
    let mut facts = ScalarFacts::default();
    for m in mods {
        facts.push_module(m);
    }
    facts.finalize(closed_world)
}
