use super::*;

/// One field-analysis-relevant instruction, extracted per block in order (the
/// member-provenance analysis is straight-line, so order is preserved).
pub(crate) enum FieldEvent {
    /// `dst = base + off` (constant byte offset, register base).
    Offset { dst: RegId, base: RegId, off: u64 },
    /// A store through a register pointer, of a register value (or `None` = unknown).
    StoreReg { ptr: RegId, value: Option<RegId> },
    /// A store through a non-register pointer — clears all field knowledge.
    StoreClear,
    /// A call: `callee` resolved (or `None` for indirect — still clobbers), and args.
    Call { callee: Option<ContractCallee>, args: Vec<Operand> },
    /// A `memcpy`/`memset` through a register destination.
    MemDst { dst: RegId },
    /// An intrinsic / non-register memcpy / free — clears all field knowledge.
    Clear,
}

/// Body-free, incrementally-built facts for whole-program **member-provenance**
/// (field contracts) — the streaming form of [`synthesize_fields`]. `push_module`
/// records per caller its [`CallerDefFacts`] (to reconstruct `local_defs`) and its
/// per-block [`FieldEvent`] sequence, plus per function its ptr-param flags,
/// linkage, declared contracts and the global escaped names; the module may then be
/// dropped. `finalize(params, closed_world)` — with `params` the whole-program
/// pointer contracts — replays the same per-block field-slot analysis over the
/// events, so the (single-pass) member-provenance pass runs in memory bounded by
/// the facts, not the IR.
#[allow(dead_code)] // wired into the verifier by Phase 2; until then only tests use it
#[derive(Default)]
pub(crate) struct FieldFacts {
    pub(crate) next: u32,
    pub(crate) name_to_id: HashMap<String, FuncId>,
    pub(crate) escaped: HashSet<String>,
    pub(crate) layout: Option<csolver_ir::DataLayout>,
    pub(crate) name: Vec<String>,
    pub(crate) internal: Vec<bool>,
    pub(crate) param_is_ptr: Vec<Vec<bool>>,
    pub(crate) param_count: Vec<usize>,
    pub(crate) declared: HashMap<(FuncId, u32), PtrContract>,
    pub(crate) caller_defs: Vec<CallerDefFacts>,
    pub(crate) blocks: Vec<Vec<Vec<FieldEvent>>>,
}

#[allow(dead_code)]
impl FieldFacts {
    /// Fold one module in (droppable afterwards).
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
            self.param_is_ptr.push(f.params.iter().map(|(_, t)| t.is_ptr()).collect());
            self.param_count.push(f.params.len());
            // Def facts (for local_defs reconstruction), same as ContractFacts.
            let param_regs = f.params.iter().enumerate().map(|(i, (r, _))| (*r, i as u32)).collect();
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
            // Field synthesis does not use the A2 pointer-hint grounding (that is scoped to
            // pointer contracts); an empty hint set keeps `reconstruct_defs(avp=false)` unchanged.
            self.caller_defs.push(CallerDefFacts { alloc_defs, hint_defs: Vec::new(), param_regs, offset_edges });
            // Per-block field-event sequence.
            let mut fblocks = Vec::with_capacity(f.blocks.len());
            for block in &f.blocks {
                let mut events = Vec::new();
                for inst in &block.insts {
                    match inst {
                        Inst::PtrOffset { dst, base: Operand::Reg(b), index: Operand::Const(Const::Int(bv)), elem } => {
                            if let (Some(es), Ok(idx)) = (elem.size_bytes(&layout), u64::try_from(bv.unsigned())) {
                                if let Some(off) = idx.checked_mul(es) {
                                    events.push(FieldEvent::Offset { dst: *dst, base: *b, off });
                                }
                            }
                        }
                        Inst::Store { ptr: Operand::Reg(pr), value, .. } => {
                            let value = if let Operand::Reg(vr) = value { Some(*vr) } else { None };
                            events.push(FieldEvent::StoreReg { ptr: *pr, value });
                        }
                        Inst::Store { .. } => events.push(FieldEvent::StoreClear),
                        Inst::Call { callee, args, .. } => {
                            let callee = match callee {
                                Callee::Direct(old) => local.get(old).map(|&g| ContractCallee::Id(g)),
                                Callee::Symbol(nm) => Some(ContractCallee::Name(nm.clone())),
                                Callee::Indirect(_) => None,
                            };
                            events.push(FieldEvent::Call { callee, args: args.clone() });
                        }
                        Inst::MemIntrinsic { dst: Operand::Reg(d), .. } => {
                            events.push(FieldEvent::MemDst { dst: *d });
                        }
                        Inst::Intrinsic { .. } | Inst::MemIntrinsic { .. } | Inst::Dealloc { .. } => {
                            events.push(FieldEvent::Clear);
                        }
                        _ => {}
                    }
                }
                fblocks.push(events);
            }
            self.blocks.push(fblocks);
        }
        self.next += m.functions.len() as u32;
    }

    /// Absorb another fact set built in parallel, shifting its ids up by `self.next`.
    pub(crate) fn merge(&mut self, other: FieldFacts) {
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
        self.param_is_ptr.extend(other.param_is_ptr);
        self.param_count.extend(other.param_count);
        self.caller_defs.extend(other.caller_defs);
        for ((fid, idx), c) in other.declared {
            self.declared.insert((FuncId(fid.0 + off), idx), c);
        }
        self.blocks.extend(other.blocks.into_iter().map(|mut fblocks| {
            for events in &mut fblocks {
                for ev in events {
                    if let FieldEvent::Call { callee: Some(ContractCallee::Id(g)), .. } = ev {
                        *g = FuncId(g.0 + off);
                    }
                }
            }
            fblocks
        }));
        self.next += other.next;
    }

    /// Replay the per-block member-provenance analysis over the facts — the same map
    /// as `synthesize_fields(&merge_modules(mods, …), params, closed_world)`.
    pub(crate) fn finalize(
        self,
        params: &HashMap<(FuncId, u32), PtrContract>,
        closed_world: bool,
    ) -> HashMap<(FuncId, u32), Vec<FieldContract>> {
        let n = self.name.len();
        let eligible = |g: FuncId, i: u32| -> bool {
            let gid = g.0 as usize;
            let complete = closed_world || self.internal[gid];
            complete
                && !self.escaped.contains(&self.name[gid])
                && self.param_is_ptr[gid].get(i as usize).copied().unwrap_or(false)
                && (params.contains_key(&(g, i)) || self.declared.contains_key(&(g, i)))
        };
        let resolve = |c: &ContractCallee| match c {
            ContractCallee::Id(g) => Some(*g),
            ContractCallee::Name(nm) => self.name_to_id.get(nm).copied(),
        };

        let mut folded: HashMap<(FuncId, u32), Option<HashMap<u64, SiteGuarantee>>> = HashMap::new();
        for gid in 0..n {
            let defs = reconstruct_defs(&self.caller_defs[gid], FuncId(gid as u32), &self.declared, params, false);
            for events in &self.blocks[gid] {
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
                for ev in events {
                    match ev {
                        FieldEvent::Offset { dst, base, off } => {
                            match (field_of.get(base).copied(), defs.contains_key(base)) {
                                (Some((root, d0)), _) => {
                                    if let Some(total) = d0.checked_add(*off) {
                                        field_of.insert(*dst, (root, total));
                                    }
                                }
                                (None, true) => {
                                    field_of.insert(*dst, (*base, *off));
                                }
                                _ => {}
                            }
                        }
                        FieldEvent::StoreReg { ptr, value } => {
                            if let Some(vr) = value {
                                if let Some(r) = root_of(&field_of, vr) {
                                    escaped.insert(r);
                                    slot.retain(|(root, _), _| *root != r);
                                }
                            }
                            let target = field_of
                                .get(ptr)
                                .copied()
                                .or_else(|| defs.contains_key(ptr).then_some((*ptr, 0)));
                            match target {
                                Some(slotkey) => match value {
                                    Some(vr) if defs.contains_key(vr) => {
                                        slot.insert(slotkey, defs[vr]);
                                    }
                                    _ => {
                                        slot.remove(&slotkey);
                                    }
                                },
                                None => slot.clear(),
                            }
                        }
                        FieldEvent::StoreClear => slot.clear(),
                        FieldEvent::Call { callee, args } => {
                            if let Some(g) = callee.as_ref().and_then(&resolve) {
                                if args.len() == self.param_count[g.0 as usize] {
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
                        FieldEvent::MemDst { dst } => match root_of(&field_of, dst) {
                            Some(r) => {
                                escaped.insert(r);
                                slot.retain(|(root, _), _| !escaped.contains(root));
                            }
                            None => slot.clear(),
                        },
                        FieldEvent::Clear => slot.clear(),
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
                            assumption: Some(if self.internal[key.0 .0 as usize] {
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
}
