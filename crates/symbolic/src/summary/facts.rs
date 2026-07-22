use super::*;

/// Body-free facts for whole-program summaries, built **incrementally**: fold each
/// module in with [`SummaryFacts::push_module`] — after which it may be dropped —
/// then [`SummaryFacts::finalize`] resolves cross-module edges by name and runs the
/// write/free and provenance fixpoints. This is what lets a whole-program summary
/// pass run in memory bounded by the facts, not the IR: lower a `.ll`, push it,
/// drop it. Cross-module `Symbol` calls are resolved only at `finalize`, so a
/// forward reference to a not-yet-pushed module resolves correctly.
///
/// Ids are assigned in push order (module-then-function), identical to
/// [`csolver_ir::merge_modules`]/[`csolver_ir::merge_id_plan`], so the finalized
/// map equals `summarize_module(&merge_modules(mods, …))` key-for-key.
#[derive(Default)]
pub struct SummaryFacts {
    /// Functions folded in so far; their ids are `0..next` in push order.
    next: u32,
    /// External (non-internal) definition name → id, first definition winning.
    name_to_id: HashMap<String, FuncId>,
    /// Per function (by id): the body-local base summary.
    base: Vec<Summary>,
    /// Per function: pointer-parameter map (for the provenance fixpoint).
    param_of: Vec<HashMap<RegId, usize>>,
    /// Per function: its *observable* calls, callee unresolved until `finalize`.
    calls: Vec<Vec<(CalleeRef, Vec<Operand>)>>,
    /// Per function: the index (into `calls`) of the observable call whose result the
    /// function returns on every path, if any — for propagating a callee's `DanglingStack`
    /// return through a wrapper. `None` when the return is not a bare call result.
    ret_call: Vec<Option<usize>>,
}

/// A call's callee before cross-module name resolution.
pub(crate) enum CalleeRef {
    /// An in-module (`Direct`) edge, already a global id.
    Id(FuncId),
    /// A `Symbol` call — resolved to a definition (or opaque) at `finalize`.
    Name(String),
    /// An indirect call — always opaque.
    Indirect,
}

impl SummaryFacts {
    /// A fresh, empty fact set.
    pub fn new() -> SummaryFacts {
        SummaryFacts::default()
    }

    /// The external (non-internal) definition name → global `FuncId` map (first
    /// definition winning), as used to resolve cross-module `Symbol` call edges.
    /// Lets a whole-program driver pair a finalized summary back to its callee name.
    pub fn name_to_id(&self) -> &HashMap<String, FuncId> {
        &self.name_to_id
    }

    /// Fold one module's functions in. The module is only read here; the caller may
    /// drop it immediately afterwards.
    pub fn push_module(&mut self, m: &Module) {
        let base = self.next;
        let local: HashMap<FuncId, FuncId> = m
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.id, FuncId(base + i as u32)))
            .collect();
        for f in &m.functions {
            let gid = local[&f.id];
            if !m.internal.contains(&f.id) {
                self.name_to_id.entry(f.name.clone()).or_insert(gid);
            }
            self.base.push(summarize_fn(f));
            self.param_of.push(ptr_param_of(f));
            self.ret_call.push(returned_call_index(f));
            let mut calls = Vec::new();
            for b in &f.blocks {
                if matches!(b.term, csolver_ir::Terminator::Unreachable) {
                    continue; // a diverging block's calls cannot affect a caller
                }
                for inst in &b.insts {
                    let Inst::Call { callee, args, .. } = inst else { continue };
                    let cr = match callee {
                        Callee::Direct(old) => {
                            local.get(old).map_or(CalleeRef::Indirect, |&g| CalleeRef::Id(g))
                        }
                        Callee::Symbol(nm) => CalleeRef::Name(nm.clone()),
                        Callee::Indirect(_) => CalleeRef::Indirect,
                    };
                    calls.push((cr, args.clone()));
                }
            }
            self.calls.push(calls);
        }
        self.next += m.functions.len() as u32;
    }

    /// Absorb another fact set as if its modules had been pushed after `self`'s:
    /// `other`'s ids are shifted up by `self.next`. This lets shards be built in
    /// parallel and merged in file order, giving ids identical to a single
    /// sequential push (so `finalize` still equals the linked result).
    pub fn merge(&mut self, other: SummaryFacts) {
        let off = self.next;
        for (name, id) in other.name_to_id {
            self.name_to_id.entry(name).or_insert(FuncId(id.0 + off));
        }
        self.base.extend(other.base);
        self.param_of.extend(other.param_of);
        self.ret_call.extend(other.ret_call);
        self.calls.extend(other.calls.into_iter().map(|mut calls| {
            for (cr, _) in &mut calls {
                if let CalleeRef::Id(g) = cr {
                    *g = FuncId(g.0 + off);
                }
            }
            calls
        }));
        self.next += other.next;
    }

    /// Resolve cross-module edges by name and run the fixpoints, yielding the same
    /// map as `summarize_module(&merge_modules(mods, …))`.
    pub fn finalize(self) -> HashMap<FuncId, Summary> {
        let n = self.base.len();
        let mut summ = self.base;
        let mut edges: Vec<Vec<FuncId>> = vec![Vec::new(); n];
        let mut opaque: Vec<bool> = vec![false; n];
        let mut prov_calls: Vec<Vec<(FuncId, Vec<Operand>)>> = vec![Vec::new(); n];
        // The resolved callee of each function's returned call (if its return is a bare call
        // result), for the dangling-return wrapper fixpoint.
        let mut ret_callee: Vec<Option<FuncId>> = vec![None; n];
        for (gid, calls) in self.calls.into_iter().enumerate() {
            for (ci, (cr, args)) in calls.into_iter().enumerate() {
                let resolved = match cr {
                    CalleeRef::Id(g) => Some(g),
                    CalleeRef::Name(nm) if nm == "<inline asm nomem>" => None,
                    CalleeRef::Name(nm) => match self.name_to_id.get(&nm) {
                        Some(&g) => Some(g),
                        None => {
                            opaque[gid] = true; // unresolved external ⇒ opaque
                            None
                        }
                    },
                    CalleeRef::Indirect => {
                        opaque[gid] = true;
                        None
                    }
                };
                if let Some(g) = resolved {
                    edges[gid].push(g);
                    prov_calls[gid].push((g, args));
                }
                if self.ret_call[gid] == Some(ci) {
                    ret_callee[gid] = resolved;
                }
            }
        }
        // 1. an opaque (external/indirect) call may do anything.
        for gid in 0..n {
            if opaque[gid] {
                summ[gid].writes = true;
                summ[gid].frees = true;
            }
        }
        // 2. propagate write/free through direct calls to a fixpoint.
        loop {
            let mut changed = false;
            for gid in 0..n {
                let (mut writes, mut frees) = (summ[gid].writes, summ[gid].frees);
                for &g in &edges[gid] {
                    writes |= summ[g.0 as usize].writes;
                    frees |= summ[g.0 as usize].frees;
                }
                if writes != summ[gid].writes || frees != summ[gid].frees {
                    summ[gid].writes = writes;
                    summ[gid].frees = frees;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // 3. propagate provenance transfers through direct calls to a fixpoint.
        loop {
            let mut changed = false;
            for gid in 0..n {
                let pof = &self.param_of[gid];
                let arg = |op: &Operand| match op {
                    Operand::Reg(r) => pof.get(r).copied(),
                    _ => None,
                };
                let mut add = ProvTransfer::default();
                for (g, args) in &prov_calls[gid] {
                    let sg = &summ[g.0 as usize];
                    for &(d, s) in &sg.prov.transfers {
                        if let (Some(pd), Some(ps)) =
                            (args.get(d).and_then(&arg), args.get(s).and_then(&arg))
                        {
                            add.transfers.push((pd, ps));
                        }
                    }
                    for &(a, label) in &sg.prov.labels {
                        if let Some(pa) = args.get(a).and_then(&arg) {
                            add.labels.push((pa, label));
                        }
                    }
                }
                let before = (summ[gid].prov.transfers.len(), summ[gid].prov.labels.len());
                summ[gid].prov.transfers.extend(add.transfers);
                summ[gid].prov.labels.extend(add.labels);
                dedup(&mut summ[gid].prov);
                if (summ[gid].prov.transfers.len(), summ[gid].prov.labels.len()) != before {
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // 4. propagate a dangling-stack return through wrappers to a fixpoint: a function that
        //    returns a callee's result inherits `DanglingStack` when that callee does. Only the
        //    dangling case composes trivially (a dangling pointer is dangling regardless of the
        //    wrapper's arguments); `PtrFromArg` would need argument remapping and stays Unknown
        //    (sound — the caller havocs). Monotone (`Unknown → DanglingStack` only), so it ends.
        loop {
            let mut changed = false;
            for gid in 0..n {
                if summ[gid].ret != RetSummary::Unknown {
                    continue;
                }
                let inherited = ret_callee[gid]
                    .map(|g| summ[g.0 as usize].ret.clone())
                    .filter(RetSummary::composes_through_wrapper);
                if let Some(ret) = inherited {
                    summ[gid].ret = ret;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        summ.into_iter()
            .enumerate()
            .map(|(i, s)| (FuncId(i as u32), s))
            .collect()
    }
}

/// Whole-program summaries **without linking**: the same result as
/// `summarize_module(&merge_modules(mods, …))`, streamed through [`SummaryFacts`]
/// (each module is scanned once; the bodies need not be held past the scan). Kept
/// as a convenience over the incremental [`SummaryFacts`] API and as the in-memory
/// equivalence oracle for it.
pub fn summarize_program(mods: &[&Module]) -> HashMap<FuncId, Summary> {
    let mut facts = SummaryFacts::new();
    for m in mods {
        facts.push_module(m);
    }
    facts.finalize()
}
