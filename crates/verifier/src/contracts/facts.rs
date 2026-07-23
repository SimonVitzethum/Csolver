use super::*;

/// Body-local pointer-contract def facts for one caller — enough to recompute
/// `local_defs` each fixpoint round *without* the body. `alloc_defs` and
/// `offset_edges` are fixed; only the parameter contributions (`param_regs` looked
/// up in the growing `prior`) change across rounds.
pub(crate) struct CallerDefFacts {
    /// Alloc-derived region roots (fixed): `(dst, guarantee)`.
    pub(crate) alloc_defs: Vec<(RegId, SiteGuarantee)>,
    /// DWARF/typed-use pointer-hint roots (fixed): `(reg, guarantee)` — the A2 lever, seeded only
    /// under `--assume-valid-params` and overridden by an exact `alloc`/param def for the same
    /// register (lowest precedence). Extracted here so `reconstruct_defs` matches `local_defs`.
    pub(crate) hint_defs: Vec<(RegId, SiteGuarantee)>,
    /// Each parameter's register and index — its def comes from its contract.
    pub(crate) param_regs: Vec<(RegId, u32)>,
    /// Constant `PtrOffset` edges `(dst, base, byte_offset)` (fixed structure).
    pub(crate) offset_edges: Vec<(RegId, RegId, u64)>,
}

/// A call's callee before name resolution (indirect calls dropped at extraction).
pub(crate) enum ContractCallee {
    Id(FuncId),
    Name(String),
}

/// Recompute `local_defs` for a caller from its [`CallerDefFacts`] and the current
/// declared/`prior` contracts — bit-identical to `local_defs` on the body: parameter
/// defs first (from a contract with a byte size), then alloc roots, then the
/// constant-offset fixpoint.
pub(crate) fn reconstruct_defs(
    facts: &CallerDefFacts,
    caller_gid: FuncId,
    declared: &HashMap<(FuncId, u32), PtrContract>,
    prior: &HashMap<(FuncId, u32), PtrContract>,
    avp: bool,
) -> HashMap<RegId, SiteGuarantee> {
    let mut defs: HashMap<RegId, SiteGuarantee> = HashMap::new();
    // A2: DWARF/typed-use hint roots first (lowest precedence — exact params/allocs below win),
    // only under `--assume-valid-params`. Mirrors `local_defs`' hint seeding for streaming==linked.
    if avp {
        for &(reg, sg) in &facts.hint_defs {
            defs.insert(reg, sg);
        }
    }
    for &(reg, i) in &facts.param_regs {
        let key = (caller_gid, i);
        if let Some(c) = declared.get(&key).or_else(|| prior.get(&key)) {
            if let SizeSpec::Bytes(n) = c.size {
                defs.insert(
                    reg,
                    SiteGuarantee { size: n, align: c.align, readable: c.readable, writable: c.writable },
                );
            }
        }
    }
    for &(reg, sg) in &facts.alloc_defs {
        defs.insert(reg, sg);
    }
    loop {
        let mut grew = false;
        for &(dst, base, off) in &facts.offset_edges {
            if defs.contains_key(&dst) {
                continue;
            }
            let Some(base_sg) = defs.get(&base).copied() else { continue };
            let Some(size) = base_sg.size.checked_sub(off) else { continue };
            let align = if off == 0 {
                base_sg.align
            } else {
                1u32 << off.trailing_zeros().min(base_sg.align.trailing_zeros())
            };
            defs.insert(
                dst,
                SiteGuarantee { size, align, readable: base_sg.readable, writable: base_sg.writable },
            );
            grew = true;
        }
        if !grew {
            break;
        }
    }
    defs
}

/// Body-free, incrementally-built facts for whole-program **pointer-contract**
/// synthesis — the streaming form of [`synthesize_program`]. Each module is folded
/// in with `push_module` (extracting per caller its [`CallerDefFacts`] and call
/// sites, plus per function its ptr params, linkage, declared contracts and the
/// global escaped names) and may then be dropped; `finalize` runs the same
/// round-based fixpoint as `synthesize`, recomputing each caller's `local_defs`
/// from its facts and the growing `prior`. This is what makes the (fixpoint)
/// pointer-contract pass run in memory bounded by the facts, not the IR.
#[allow(dead_code)] // wired into the verifier by Phase 2; until then only tests use it
#[derive(Default)]
pub(crate) struct ContractFacts {
    pub(crate) next: u32,
    pub(crate) name_to_id: HashMap<String, FuncId>,
    pub(crate) escaped: HashSet<String>,
    pub(crate) layout: Option<csolver_ir::DataLayout>,
    pub(crate) name: Vec<String>,
    pub(crate) internal: Vec<bool>,
    pub(crate) ptr_params: Vec<Vec<u32>>,
    pub(crate) param_count: Vec<usize>,
    pub(crate) declared: HashMap<(FuncId, u32), PtrContract>,
    pub(crate) caller_defs: Vec<CallerDefFacts>,
    pub(crate) calls: Vec<Vec<(ContractCallee, Vec<Operand>)>>,
}

#[allow(dead_code)]
impl ContractFacts {
    /// Fold one module in (droppable afterwards): extract its functions' linkage,
    /// pointer parameters, declared contracts and address-taken names, and per
    /// caller its alloc/param/offset def facts and (unresolved) call sites.
    pub(crate) fn push_module(&mut self, m: &Module) {
        if self.layout.is_none() {
            self.layout = Some(m.layout);
        }
        let layout = self.layout.unwrap_or(csolver_ir::DataLayout::LP64);
        let base = self.next;
        let local: HashMap<FuncId, FuncId> = m
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.id, FuncId(base + i as u32)))
            .collect();
        self.escaped.extend(address_taken_names(m));
        for (&(fid, idx), c) in &m.param_contracts {
            if let Some(&gid) = local.get(&fid) {
                self.declared.insert((gid, idx), *c);
            }
        }
        for f in &m.functions {
            let gid = local[&f.id];
            if !m.internal.contains(&f.id) {
                self.name_to_id.entry(f.name.clone()).or_insert(gid);
            }
            self.name.push(f.name.clone());
            self.internal.push(m.internal.contains(&f.id));
            self.ptr_params.push(
                f.params
                    .iter()
                    .enumerate()
                    .filter(|(_, (_, t))| t.is_ptr())
                    .map(|(i, _)| i as u32)
                    .collect(),
            );
            self.param_count.push(f.params.len());
            let param_regs = f.params.iter().enumerate().map(|(i, (r, _))| (*r, i as u32)).collect();
            // DWARF/typed-use hint roots for this caller (A2): the same registers `local_defs`
            // seeds — instruction-defined regs then params — keyed by the function's *local* id
            // (as `module.reg_ptr_hints` is before merge). Guarantee computed here so the streaming
            // fixpoint needs no IR; consulted only under `--assume-valid-params` in reconstruct.
            let mut hint_defs = Vec::new();
            {
                let mut seen: HashSet<RegId> = HashSet::new();
                let add = |reg: RegId, hint_defs: &mut Vec<(RegId, SiteGuarantee)>, seen: &mut HashSet<RegId>| {
                    if let Some(h) = m.reg_ptr_hints.get(&(f.id, reg)).filter(|h| h.size > 0) {
                        if seen.insert(reg) {
                            hint_defs.push((reg, hint_guarantee(h)));
                        }
                    }
                };
                for inst in f.blocks.iter().flat_map(|b| &b.insts) {
                    if let Some(reg) = inst.defined_reg() {
                        add(reg, &mut hint_defs, &mut seen);
                    }
                }
                for (reg, _) in &f.params {
                    add(*reg, &mut hint_defs, &mut seen);
                }
            }
            let mut alloc_defs = Vec::new();
            let mut offset_edges = Vec::new();
            for inst in f.blocks.iter().flat_map(|b| &b.insts) {
                match inst {
                    Inst::Alloc { dst, elem, count: Operand::Const(Const::Int(bv)), align, .. } => {
                        if let (Some(es), Ok(cnt)) = (elem.size_bytes(&layout), u64::try_from(bv.unsigned())) {
                            if let Some(size) = es.checked_mul(cnt) {
                                alloc_defs.push((
                                    *dst,
                                    SiteGuarantee { size, align: (*align).max(1), readable: true, writable: true },
                                ));
                            }
                        }
                    }
                    Inst::PtrOffset { dst, base: Operand::Reg(b), index: Operand::Const(Const::Int(bv)), elem } => {
                        if let (Some(es), Ok(idx)) = (elem.size_bytes(&layout), u64::try_from(bv.unsigned())) {
                            if let Some(off) = idx.checked_mul(es) {
                                offset_edges.push((*dst, *b, off));
                            }
                        }
                    }
                    _ => {}
                }
            }
            self.caller_defs.push(CallerDefFacts { alloc_defs, hint_defs, param_regs, offset_edges });
            let mut calls = Vec::new();
            for inst in f.blocks.iter().flat_map(|b| &b.insts) {
                let Inst::Call { callee, args, .. } = inst else { continue };
                let cr = match callee {
                    Callee::Direct(old) => match local.get(old) {
                        Some(&g) => ContractCallee::Id(g),
                        None => continue,
                    },
                    Callee::Symbol(nm) => ContractCallee::Name(nm.clone()),
                    Callee::Indirect(_) => continue,
                };
                calls.push((cr, args.clone()));
            }
            self.calls.push(calls);
        }
        self.next += m.functions.len() as u32;
    }

    /// Absorb another fact set built in parallel, shifting its ids up by `self.next`
    /// so a file-order merge reproduces a single sequential push.
    pub(crate) fn merge(&mut self, other: ContractFacts) {
        let off = self.next;
        if self.layout.is_none() {
            self.layout = other.layout;
        }
        for (name, id) in other.name_to_id {
            self.name_to_id.entry(name).or_insert(FuncId(id.0 + off));
        }
        self.escaped.extend(other.escaped);
        self.name.extend(other.name);
        self.internal.extend(other.internal);
        self.ptr_params.extend(other.ptr_params);
        self.param_count.extend(other.param_count);
        self.caller_defs.extend(other.caller_defs);
        for ((fid, idx), c) in other.declared {
            self.declared.insert((FuncId(fid.0 + off), idx), c);
        }
        self.calls.extend(other.calls.into_iter().map(|mut calls| {
            for (cr, _) in &mut calls {
                if let ContractCallee::Id(g) = cr {
                    *g = FuncId(g.0 + off);
                }
            }
            calls
        }));
        self.next += other.next;
    }

    /// Run the pointer-contract fixpoint over the facts — the same result as
    /// `synthesize(&merge_modules(mods, …), closed_world)`.
    pub(crate) fn finalize(self, closed_world: bool, avp: bool) -> HashMap<(FuncId, u32), PtrContract> {
        let mut acc: HashMap<(FuncId, u32), PtrContract> = HashMap::new();
        loop {
            let round = self.round(&acc, closed_world, avp);
            let mut grew = false;
            for (k, v) in round {
                grew |= acc.insert(k, v).is_none();
            }
            if !grew {
                return acc;
            }
        }
    }

    pub(crate) fn round(
        &self,
        prior: &HashMap<(FuncId, u32), PtrContract>,
        closed_world: bool,
        avp: bool,
    ) -> HashMap<(FuncId, u32), PtrContract> {
        let n = self.name.len();
        let mut candidates: HashSet<(FuncId, u32)> = HashSet::new();
        for gid in 0..n {
            let complete = closed_world || self.internal[gid];
            if !complete || self.escaped.contains(&self.name[gid]) {
                continue;
            }
            for &i in &self.ptr_params[gid] {
                let key = (FuncId(gid as u32), i);
                if !self.declared.contains_key(&key) && !prior.contains_key(&key) {
                    candidates.insert(key);
                }
            }
        }
        if candidates.is_empty() {
            return HashMap::new();
        }
        let resolve = |c: &ContractCallee| match c {
            ContractCallee::Id(g) => Some(*g),
            ContractCallee::Name(nm) => self.name_to_id.get(nm).copied(),
        };
        let mut folded: HashMap<(FuncId, u32), Option<SiteGuarantee>> = HashMap::new();
        for gid in 0..n {
            let defs = reconstruct_defs(&self.caller_defs[gid], FuncId(gid as u32), &self.declared, prior, avp);
            for (cr, args) in &self.calls[gid] {
                let Some(g) = resolve(cr) else { continue };
                let params = self.param_count[g.0 as usize];
                if args.len() != params {
                    for i in 0..params as u32 {
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
                    let site = match arg {
                        Operand::Reg(r) => defs.get(r).copied(),
                        _ => None,
                    };
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
                let assumption = if self.internal[key.0 .0 as usize] {
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
}
