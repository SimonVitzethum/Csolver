//! Call-site contract synthesis for internal functions.
//!
//! A function with **internal linkage** is invisible outside its module, so the
//! module's direct call sites are provably *all* of its call sites (unless its
//! address is taken, which would allow an untracked indirect call). That
//! licenses deriving a contract for an otherwise-uncontracted pointer
//! parameter: the **weakest guarantee every call site provides** — the minimum
//! of the argument sizes and alignments, the intersection of the permissions.
//!
//! This is the interprocedural lever for rustc's debug IR, which omits the
//! `dereferenceable` attributes: the callee's `ptr %self` has no declared
//! contract, but every caller demonstrably passes (say) a live 32-byte alloca.
//!
//! ## Closed-world mode
//!
//! Internal linkage is one way to *prove* the call sites complete. When the
//! caller declares the module to be the whole program (`Config::closed_world`),
//! completeness is instead *assumed* for every function, so an exported function
//! is contracted from its in-module call sites too. Every other condition below
//! still holds (address-not-taken, statically-derivable arguments, ≥1 call
//! site), and the trust basis is surfaced as the distinct `closed-world-contract`
//! assumption rather than `internal-call-contract`.
//!
//! ## Soundness conditions (each enforced here)
//!
//! 1. The callee has internal linkage (`Module::internal`), *or* closed-world
//!    mode asserts the module is the whole program.
//! 2. Its address is never taken — no `Const::Symbol(name)` operand anywhere in
//!    the module (an escaped function pointer would mean unseen call sites).
//! 3. Every call site's argument is *statically* derivable: the direct result
//!    of an `Alloc` with a constant byte size (live for the whole caller frame,
//!    read+write), or the caller's own parameter carrying a declared
//!    `SizeSpec::Bytes` contract (borrowed for the call's duration). Anything
//!    else — including a synthesized contract, which would be circular — makes
//!    the parameter ineligible.
//! 4. A callee with zero call sites gets nothing (dead code stays UNKNOWN).
//!
//! Proofs resting on a synthesized contract surface the dedicated
//! `internal-call-contract` assumption, not `param-contracts` — the trust basis
//! is different (derived from call-site completeness, not declared attributes).

use csolver_absint::{analyze_intervals, Bound, IntervalAnalysis};
use csolver_ir::{
    BlockId, Callee, Condition, Const, FieldContract, FuncId, Inst, Module, Operand, PtrContract,
    RegId, SizeSpec, Terminator, Type,
};
use std::collections::{HashMap, HashSet};

/// Visit every operand inside a safety-check condition.
fn condition_operands(c: &Condition, op: &mut impl FnMut(&Operand)) {
    match c {
        Condition::True => {}
        Condition::Cmp { lhs, rhs, .. } => {
            op(lhs);
            op(rhs);
        }
        Condition::And(cs) | Condition::Or(cs) => {
            for c in cs {
                condition_operands(c, op);
            }
        }
        Condition::Not(c) => condition_operands(c, op),
    }
}

/// The assumption id surfaced by proofs that rest on a synthesized contract for
/// a function proven complete by **internal linkage**.
pub(crate) const INTERNAL_CALL_CONTRACT: &str = "internal-call-contract";

/// The assumption id for a synthesized contract whose call-site completeness
/// rests on the **whole-program (closed-world)** assertion rather than on
/// internal linkage — an *exported* function all of whose callers are taken to
/// be visible because the module is declared to be the whole program.
pub(crate) const CLOSED_WORLD_CONTRACT: &str = "closed-world-contract";

/// What one call site guarantees about the region behind an argument.
#[derive(Clone, Copy)]
struct SiteGuarantee {
    size: u64,
    align: u32,
    readable: bool,
    writable: bool,
}

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
fn synthesize_round(
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
fn synthesize_round_program(
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

/// Body-local pointer-contract def facts for one caller — enough to recompute
/// `local_defs` each fixpoint round *without* the body. `alloc_defs` and
/// `offset_edges` are fixed; only the parameter contributions (`param_regs` looked
/// up in the growing `prior`) change across rounds.
struct CallerDefFacts {
    /// Alloc-derived region roots (fixed): `(dst, guarantee)`.
    alloc_defs: Vec<(RegId, SiteGuarantee)>,
    /// Each parameter's register and index — its def comes from its contract.
    param_regs: Vec<(RegId, u32)>,
    /// Constant `PtrOffset` edges `(dst, base, byte_offset)` (fixed structure).
    offset_edges: Vec<(RegId, RegId, u64)>,
}

/// A call's callee before name resolution (indirect calls dropped at extraction).
enum ContractCallee {
    Id(FuncId),
    Name(String),
}

/// Recompute `local_defs` for a caller from its [`CallerDefFacts`] and the current
/// declared/`prior` contracts — bit-identical to `local_defs` on the body: parameter
/// defs first (from a contract with a byte size), then alloc roots, then the
/// constant-offset fixpoint.
fn reconstruct_defs(
    facts: &CallerDefFacts,
    caller_gid: FuncId,
    declared: &HashMap<(FuncId, u32), PtrContract>,
    prior: &HashMap<(FuncId, u32), PtrContract>,
) -> HashMap<RegId, SiteGuarantee> {
    let mut defs: HashMap<RegId, SiteGuarantee> = HashMap::new();
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
    next: u32,
    name_to_id: HashMap<String, FuncId>,
    escaped: HashSet<String>,
    layout: Option<csolver_ir::DataLayout>,
    name: Vec<String>,
    internal: Vec<bool>,
    ptr_params: Vec<Vec<u32>>,
    param_count: Vec<usize>,
    declared: HashMap<(FuncId, u32), PtrContract>,
    caller_defs: Vec<CallerDefFacts>,
    calls: Vec<Vec<(ContractCallee, Vec<Operand>)>>,
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
            self.caller_defs.push(CallerDefFacts { alloc_defs, param_regs, offset_edges });
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
    pub(crate) fn finalize(self, closed_world: bool) -> HashMap<(FuncId, u32), PtrContract> {
        let mut acc: HashMap<(FuncId, u32), PtrContract> = HashMap::new();
        loop {
            let round = self.round(&acc, closed_world);
            let mut grew = false;
            for (k, v) in round {
                grew |= acc.insert(k, v).is_none();
            }
            if !grew {
                return acc;
            }
        }
    }

    fn round(
        &self,
        prior: &HashMap<(FuncId, u32), PtrContract>,
        closed_world: bool,
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
            let defs = reconstruct_defs(&self.caller_defs[gid], FuncId(gid as u32), &self.declared, prior);
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

/// One field-analysis-relevant instruction, extracted per block in order (the
/// member-provenance analysis is straight-line, so order is preserved).
enum FieldEvent {
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
    next: u32,
    name_to_id: HashMap<String, FuncId>,
    escaped: HashSet<String>,
    layout: Option<csolver_ir::DataLayout>,
    name: Vec<String>,
    internal: Vec<bool>,
    param_is_ptr: Vec<Vec<bool>>,
    param_count: Vec<usize>,
    declared: HashMap<(FuncId, u32), PtrContract>,
    caller_defs: Vec<CallerDefFacts>,
    blocks: Vec<Vec<Vec<FieldEvent>>>,
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
            self.caller_defs.push(CallerDefFacts { alloc_defs, param_regs, offset_edges });
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
            let defs = reconstruct_defs(&self.caller_defs[gid], FuncId(gid as u32), &self.declared, params);
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

/// The interval of a call-site argument (the value flowing into a parameter),
/// as a finite `[lo, hi]` — `None` if it is not a bounded integer there.
fn arg_interval(arg: &Operand, iv: &IntervalAnalysis, block: BlockId) -> Option<(i128, i128)> {
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
                for (i, arg) in args.iter().enumerate() {
                    let key = (*g, i as u32);
                    if !candidates.contains(&key) {
                        continue;
                    }
                    let site = arg_interval(arg, &iv, block.id);
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
    next: u32,
    name_to_id: HashMap<String, FuncId>,
    escaped: HashSet<String>,
    internal: Vec<bool>,
    name: Vec<String>,
    int_params: Vec<Vec<u32>>,
    param_count: Vec<usize>,
    sites: Vec<Vec<ScalarCall>>,
}

/// A call site's callee, unresolved until `finalize` (indirect calls are dropped).
#[allow(dead_code)]
enum ScalarCallee {
    Id(FuncId),
    Name(String),
}

/// One call site: its callee and the interval each argument held there.
#[allow(dead_code)]
struct ScalarCall {
    callee: ScalarCallee,
    arg_intervals: Vec<Option<(i128, i128)>>,
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
                    let arg_intervals =
                        args.iter().map(|a| arg_interval(a, &iv, block.id)).collect();
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
        let defs = local_defs(caller, caller.id, &module.param_contracts, &module.layout, params);
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
            let defs = local_defs(caller, caller_gid, &global_pc, &layout, params);
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

/// Fold one call site's field guarantees into the running intersection: keep only
/// byte offsets present at *every* site so far, each at the weakest guarantee.
fn intersect_site(
    acc: &mut Option<HashMap<u64, SiteGuarantee>>,
    site: HashMap<u64, SiteGuarantee>,
) {
    match acc {
        None => *acc = Some(site),
        Some(cur) => {
            cur.retain(|f, g| {
                if let Some(s) = site.get(f) {
                    *g = SiteGuarantee {
                        size: g.size.min(s.size),
                        align: g.align.min(s.align),
                        readable: g.readable && s.readable,
                        writable: g.writable && s.writable,
                    };
                    true
                } else {
                    false
                }
            });
        }
    }
}

/// What the caller statically guarantees about `arg`, if anything.
fn derive_site(
    arg: &Operand,
    defs: &HashMap<RegId, SiteGuarantee>,
) -> Option<SiteGuarantee> {
    match arg {
        Operand::Reg(r) => defs.get(r).copied(),
        _ => None,
    }
}

/// Per-function map from a register to the static guarantee it carries:
/// `Alloc` results (constant size, full access, live for the frame) and the
/// function's own parameters with a `Bytes` contract — declared, or synthesized
/// in a strictly earlier round (final by the induction in [`synthesize`]).
/// Same-round synthesized contracts are never consulted — that would be
/// circular.
fn local_defs(
    f: &csolver_ir::Function,
    caller_id: FuncId,
    param_contracts: &HashMap<(FuncId, u32), PtrContract>,
    layout: &csolver_ir::DataLayout,
    prior: &HashMap<(FuncId, u32), PtrContract>,
) -> HashMap<RegId, SiteGuarantee> {
    let mut defs = HashMap::new();
    for (i, (reg, _)) in f.params.iter().enumerate() {
        let key = (caller_id, i as u32);
        if let Some(c) = param_contracts.get(&key).or_else(|| prior.get(&key)) {
            if let SizeSpec::Bytes(n) = c.size {
                defs.insert(
                    *reg,
                    SiteGuarantee {
                        size: n,
                        align: c.align,
                        readable: c.readable,
                        writable: c.writable,
                    },
                );
            }
        }
    }
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        if let Inst::Alloc { dst, elem, count: Operand::Const(Const::Int(bv)), align, .. } = inst {
            let Some(elem_size) = elem.size_bytes(layout) else { continue };
            let Ok(count) = u64::try_from(bv.unsigned()) else { continue };
            let Some(size) = elem_size.checked_mul(count) else { continue };
            defs.insert(
                *dst,
                SiteGuarantee { size, align: (*align).max(1), readable: true, writable: true },
            );
        }
    }
    // A constant `PtrOffset` into a known region (`&a[k]` — C passes an array
    // argument as `&a[0]`, a getelementptr into the alloca, never the alloca
    // itself) still points into that region: it guarantees the remaining
    // `size - offset` bytes. A bounded fixpoint chains multi-step geps
    // (`&outer.arr[0]`); a negative or past-end offset is simply not derivable.
    loop {
        let mut grew = false;
        for inst in f.blocks.iter().flat_map(|b| &b.insts) {
            let Inst::PtrOffset {
                dst,
                base: Operand::Reg(b),
                index: Operand::Const(Const::Int(bv)),
                elem,
            } = inst
            else {
                continue;
            };
            if defs.contains_key(dst) {
                continue;
            }
            let Some(base) = defs.get(b).copied() else { continue };
            let Some(elem_size) = elem.size_bytes(layout) else { continue };
            let Ok(idx) = u64::try_from(bv.unsigned()) else { continue };
            let Some(off) = idx.checked_mul(elem_size) else { continue };
            let Some(size) = base.size.checked_sub(off) else { continue };
            // Alignment at `base + off`: unchanged at offset 0, else the exact
            // 2-power common to the base alignment and the offset (a lower bound,
            // so sound).
            let align = if off == 0 {
                base.align
            } else {
                1u32 << off.trailing_zeros().min(base.align.trailing_zeros())
            };
            defs.insert(
                *dst,
                SiteGuarantee { size, align, readable: base.readable, writable: base.writable },
            );
            grew = true;
        }
        if !grew {
            break;
        }
    }
    defs
}

/// Every function name whose address escapes into a value position
/// (`Const::Symbol` in any instruction or terminator operand). Such a function
/// can be called indirectly, so its call sites are *not* all known.
fn address_taken_names(module: &Module) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut op = |o: &Operand| {
        if let Operand::Const(Const::Symbol(s)) | Operand::Const(Const::SymbolOffset(s, _)) = o {
            names.insert(s.clone());
        }
    };
    for f in &module.functions {
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
                    Inst::RefWitness { .. } => {}
                    Inst::Assign { value, .. } => match value {
                        csolver_ir::RValue::Use(o) => op(o),
                        csolver_ir::RValue::Bin { lhs, rhs, .. }
                        | csolver_ir::RValue::Cmp { lhs, rhs, .. } => {
                            op(lhs);
                            op(rhs);
                        }
                        csolver_ir::RValue::Cast { operand, .. } => op(operand),
                        csolver_ir::RValue::Select { cond, then_val, else_val } => {
                            op(cond);
                            op(then_val);
                            op(else_val);
                        }
                    },
                    Inst::Call { args, .. } => args.iter().for_each(&mut op),
                    Inst::Intrinsic { args, .. } => args.iter().for_each(&mut op),
                    Inst::MemIntrinsic { dst, src, len, .. } => {
                        op(dst);
                        if let Some(s) = src {
                            op(s);
                        }
                        op(len);
                    }
                    Inst::Dealloc { ptr, .. } => op(ptr),
                    Inst::ProvLabel { ptr, .. } | Inst::CapRequire { ptr, .. } => op(ptr),
                    Inst::ProvPropagate { dst, src } => { op(dst); op(src); }
                    Inst::CapRequireIfAlias { a, b, .. } => { op(a); op(b); }
                    Inst::CapRequireIfAliasFields { obj, .. } => op(obj),
                    Inst::SafetyCheck { condition, .. } => condition_operands(condition, &mut op),
                    Inst::Asm { .. } => {}
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
    }
    names
}

#[cfg(test)]
mod program_equiv_tests {
    use super::*;
    use csolver_ir::{merge_modules, BasicBlock, Function, RValue};

    fn func(id: u32, name: &str, params: Vec<(RegId, Type)>, insts: Vec<Inst>) -> Function {
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb.insts = insts;
        Function {
            id: FuncId(id),
            name: name.into(),
            params,
            ret_ty: Type::Unit,
            blocks: vec![bb],
            entry: BlockId(0),
        }
    }
    fn call(callee: Callee, arg: i128) -> Inst {
        Inst::Call {
            dst: None,
            callee,
            args: vec![Operand::int(32, arg as u128)],
            ret_ty: Type::Unit,
            ret_ref: None,
        }
    }

    /// `synthesize_scalars_program` must equal `synthesize_scalars(&merge(...))`
    /// key-for-key: cross-module `Symbol` folds into the callee's precondition like
    /// the linked `Direct` call, an in-module `Direct` folds too, and an
    /// address-taken (escaped) callee is excluded everywhere.
    #[test]
    fn scalar_preconditions_match_the_linked_module() {
        let ip = |r: u32| vec![(RegId(r), Type::int(32))];
        // Module A: a caller that calls the cross-module `target` (5 and 10), an
        // in-module `atgt` (7), and an escaped `esc` (3) whose address it also takes.
        let mut a = Module::new("a");
        a.functions.push(func(
            0,
            "caller_a",
            vec![],
            vec![
                call(Callee::Symbol("target".into()), 5),
                call(Callee::Symbol("target".into()), 10),
                call(Callee::Direct(FuncId(1)), 7),
                Inst::Assign {
                    dst: RegId(9),
                    ty: Type::ptr(Type::int(32)),
                    value: RValue::Use(Operand::Const(Const::Symbol("esc".into()))),
                },
                call(Callee::Direct(FuncId(2)), 3),
            ],
        ));
        a.functions.push(func(1, "atgt", ip(0), vec![]));
        a.functions.push(func(2, "esc", ip(0), vec![]));
        // Module B: the cross-module target.
        let mut b = Module::new("b");
        b.functions.push(func(0, "target", ip(0), vec![]));

        for cw in [true, false] {
            let linked = merge_modules(vec![a.clone(), b.clone()], "linked");
            let want = synthesize_scalars(&linked, cw);
            let got = synthesize_scalars_program(&[&a, &b], cw);
            assert_eq!(got, want, "link-free scalar preconditions must equal linked (cw={cw})");
        }

        // Spot-check the intent under closed-world: target=[5,10], atgt=[7,7], esc absent.
        let got = synthesize_scalars_program(&[&a, &b], true);
        assert_eq!(got.get(&(FuncId(3), 0)), Some(&(5, 10)), "target folds 5∪10");
        assert_eq!(got.get(&(FuncId(1), 0)), Some(&(7, 7)), "atgt folds 7");
        assert!(!got.contains_key(&(FuncId(2), 0)), "escaped esc is excluded");
    }

    /// `synthesize_program` (pointer contracts, link-free) must equal
    /// `synthesize(&merge(...))` key-for-key: a cross-module `Symbol` call passing a
    /// const-sized alloca gives the callee's parameter the same contract the linked
    /// `Direct` call would, and an address-taken callee is excluded.
    #[test]
    fn pointer_contracts_match_the_linked_module() {
        let pp = || vec![(RegId(0), Type::ptr(Type::int(32)))];
        let alloc16 = Inst::Alloc {
            dst: RegId(1),
            region: csolver_core::RegionKind::Stack,
            elem: Type::int(32),
            count: Operand::int(64, 4), // 4 × i32 = 16 bytes
            align: 4,
        };
        let pcall = |callee: Callee, arg: Operand| Inst::Call {
            dst: None,
            callee,
            args: vec![arg],
            ret_ty: Type::Unit,
            ret_ref: None,
        };
        // A: caller allocs 16 bytes and passes it cross-module to `sink`.
        let mut a = Module::new("a");
        a.functions.push(func(
            0,
            "caller",
            vec![],
            vec![alloc16, pcall(Callee::Symbol("sink".into()), Operand::Reg(RegId(1)))],
        ));
        // B: the sink (uncontracted ptr param) and an escaped ptr-param function.
        let mut b = Module::new("b");
        b.functions.push(func(0, "sink", pp(), vec![]));

        for cw in [true, false] {
            let want = synthesize(&merge_modules(vec![a.clone(), b.clone()], "l"), cw);
            let got = synthesize_program(&[&a, &b], cw);
            assert_eq!(got, want, "link-free pointer contracts must equal linked (cw={cw})");
        }
        // Under closed-world, sink (FuncId 1 after merge) gets a 16-byte contract.
        let got = synthesize_program(&[&a, &b], true);
        assert_eq!(got.get(&(FuncId(1), 0)).map(|c| c.size), Some(SizeSpec::Bytes(16)));
    }

    /// Randomised guard for pointer contracts over random multi-module programs:
    /// const-sized allocas, cross-module and in-module calls that pass an alloca, a
    /// forwarded parameter (exercising the synthesis fixpoint), or a constant, plus
    /// random address-taking and closed-world flag.
    #[test]
    fn pointer_contracts_match_linked_on_random_programs() {
        let mut state: u64 = 0x00A5_5A5A_1357_9BDF;
        let mut rng = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let pcall = |callee: Callee, arg: Operand| Inst::Call {
            dst: None,
            callee,
            args: vec![arg],
            ret_ty: Type::Unit,
            ret_ref: None,
        };
        for _ in 0..300 {
            let n_mods = 2 + (rng() % 2) as usize;
            let per = 2 + (rng() % 3) as usize;
            let total = n_mods * per;
            let name = |gi: usize| format!("h{gi}");
            let mut modules = Vec::new();
            let mut gi = 0usize;
            for _ in 0..n_mods {
                let mut m = Module::new("m");
                for local in 0..per {
                    let mut insts = Vec::new();
                    let has_alloc = rng() % 2 == 0;
                    if has_alloc {
                        insts.push(Inst::Alloc {
                            dst: RegId(1),
                            region: csolver_core::RegionKind::Stack,
                            elem: Type::int(32),
                            count: Operand::int(64, (1 + rng() % 4) as u128),
                            align: [1u32, 2, 4, 8][(rng() % 4) as usize],
                        });
                    }
                    for _ in 0..(rng() % 3) {
                        let tgt = (rng() as usize) % total;
                        let arg = match rng() % 3 {
                            0 => Operand::Reg(RegId(0)), // forward own param (fixpoint)
                            1 => Operand::Reg(RegId(1)), // the alloca (or an undefined reg)
                            _ => Operand::int(64, 0),    // a non-derivable constant
                        };
                        insts.push(pcall(Callee::Symbol(name(tgt)), arg));
                    }
                    if rng() % 4 == 0 {
                        let e = (rng() as usize) % total;
                        insts.push(Inst::Assign {
                            dst: RegId(9),
                            ty: Type::ptr(Type::int(32)),
                            value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                        });
                    }
                    m.functions.push(func(
                        local as u32,
                        &name(gi),
                        vec![(RegId(0), Type::ptr(Type::int(32)))],
                        insts,
                    ));
                    gi += 1;
                }
                modules.push(m);
            }
            let cw = rng() & 1 == 0;
            let refs: Vec<&Module> = modules.iter().collect();
            let got = synthesize_program(&refs, cw);
            let want = synthesize(&merge_modules(modules.clone(), "linked"), cw);
            assert_eq!(got, want, "link-free != linked pointer contracts (cw={cw})");
        }
    }

    /// Streaming pointer contracts: `ContractFacts` (push each module, then
    /// `finalize`) must equal `synthesize_program` (and hence `synthesize∘merge`)
    /// over random multi-module programs — the fixpoint recomputed from body-free
    /// facts, not the bodies.
    #[test]
    fn contract_facts_match_synthesize_program_on_random() {
        let mut state: u64 = 0x0C0F_FEE0_1234_ABCD;
        let mut rng = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let pcall = |callee: Callee, arg: Operand| Inst::Call {
            dst: None,
            callee,
            args: vec![arg],
            ret_ty: Type::Unit,
            ret_ref: None,
        };
        let mut total_with_contracts = 0;
        for _ in 0..300 {
            let n_mods = 2 + (rng() % 2) as usize;
            let per = 2 + (rng() % 3) as usize;
            let total = n_mods * per;
            let name = |gi: usize| format!("c{gi}");
            let mut modules = Vec::new();
            let mut gi = 0usize;
            for _ in 0..n_mods {
                let mut m = Module::new("m");
                for local in 0..per {
                    let mut insts = Vec::new();
                    if rng() % 2 == 0 {
                        insts.push(Inst::Alloc {
                            dst: RegId(1),
                            region: csolver_core::RegionKind::Stack,
                            elem: Type::int(32),
                            count: Operand::int(64, (1 + rng() % 4) as u128),
                            align: [1u32, 2, 4, 8][(rng() % 4) as usize],
                        });
                    }
                    // A constant PtrOffset off the alloca (a field/subarray pointer).
                    if rng() % 2 == 0 {
                        insts.push(Inst::PtrOffset {
                            dst: RegId(3),
                            base: Operand::Reg(RegId(1)),
                            index: Operand::int(64, (rng() % 3) as u128),
                            elem: Type::int(32),
                        });
                    }
                    for _ in 0..(rng() % 3) {
                        let tgt = (rng() as usize) % total;
                        let arg = match rng() % 4 {
                            0 => Operand::Reg(RegId(0)), // forwarded param (fixpoint)
                            1 => Operand::Reg(RegId(1)), // alloca
                            2 => Operand::Reg(RegId(3)), // offset pointer
                            _ => Operand::int(64, 0),
                        };
                        insts.push(pcall(Callee::Symbol(name(tgt)), arg));
                    }
                    if rng() % 5 == 0 {
                        let e = (rng() as usize) % total;
                        insts.push(Inst::Assign {
                            dst: RegId(9),
                            ty: Type::ptr(Type::int(32)),
                            value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                        });
                    }
                    m.functions.push(func(
                        local as u32,
                        &name(gi),
                        vec![(RegId(0), Type::ptr(Type::int(32)))],
                        insts,
                    ));
                    gi += 1;
                }
                modules.push(m);
            }
            let cw = rng() & 1 == 0;
            let refs: Vec<&Module> = modules.iter().collect();
            let mut facts = ContractFacts::default();
            for m in &refs {
                facts.push_module(m);
            }
            let got = facts.finalize(cw);
            let want = synthesize_program(&refs, cw);
            assert_eq!(got, want, "streamed pointer contracts != synthesize_program (cw={cw})");
            total_with_contracts += usize::from(!got.is_empty());
        }
        assert!(total_with_contracts > 0, "no program produced a contract — test is vacuous");
    }

    /// Streaming property: push each module then **drop it**, then `finalize`, equals
    /// the linked pointer contracts (caller pushed before its callee's module).
    #[test]
    fn contract_facts_stream_and_drop_equals_linked() {
        let caller = {
            let mut m = Module::new("a");
            m.functions.push(func(
                0,
                "caller",
                vec![],
                vec![
                    Inst::Alloc {
                        dst: RegId(1),
                        region: csolver_core::RegionKind::Stack,
                        elem: Type::int(32),
                        count: Operand::int(64, 4),
                        align: 4,
                    },
                    Inst::Call {
                        dst: None,
                        callee: Callee::Symbol("sink".into()),
                        args: vec![Operand::Reg(RegId(1))],
                        ret_ty: Type::Unit,
                        ret_ref: None,
                    },
                ],
            ));
            m
        };
        let callee = {
            let mut m = Module::new("b");
            m.functions.push(func(0, "sink", vec![(RegId(0), Type::ptr(Type::int(32)))], vec![]));
            m
        };
        let want = synthesize(&merge_modules(vec![caller.clone(), callee.clone()], "l"), true);
        let mut facts = ContractFacts::default();
        {
            let m0 = caller;
            facts.push_module(&m0);
        }
        {
            let m1 = callee;
            facts.push_module(&m1);
        }
        assert_eq!(facts.finalize(true), want, "streamed+dropped == linked pointer contracts");
    }

    /// `synthesize_fields_program` (member-provenance, link-free) must equal
    /// `synthesize_fields(&merge(...), params, …)`: a valid pointer stored into a
    /// field of a region that is then passed cross-module to a contracted-parameter
    /// callee gives that parameter's field the same contract as when linked.
    #[test]
    fn field_contracts_match_the_linked_module() {
        // caller: R = alloc 16B; B = alloc 8B; store B into R@0; sink(R).
        let mut a = Module::new("a");
        a.functions.push(func(
            0,
            "caller",
            vec![],
            vec![
                Inst::Alloc {
                    dst: RegId(1),
                    region: csolver_core::RegionKind::Stack,
                    elem: Type::int(64),
                    count: Operand::int(64, 2),
                    align: 8,
                },
                Inst::Alloc {
                    dst: RegId(2),
                    region: csolver_core::RegionKind::Stack,
                    elem: Type::int(64),
                    count: Operand::int(64, 1),
                    align: 8,
                },
                Inst::Store {
                    ty: Type::ptr(Type::int(64)),
                    ptr: Operand::Reg(RegId(1)),
                    value: Operand::Reg(RegId(2)),
                    align: 8,
                },
                Inst::Call {
                    dst: None,
                    callee: Callee::Symbol("sink".into()),
                    args: vec![Operand::Reg(RegId(1))],
                    ret_ty: Type::Unit,
                    ret_ref: None,
                },
            ],
        ));
        let mut b = Module::new("b");
        b.functions.push(func(0, "sink", vec![(RegId(0), Type::ptr(Type::int(64)))], vec![]));

        for cw in [true, false] {
            let merged = merge_modules(vec![a.clone(), b.clone()], "l");
            let params = synthesize(&merged, cw);
            let want = synthesize_fields(&merged, &params, cw);
            let got = synthesize_fields_program(&[&a, &b], &params, cw);
            assert_eq!(got, want, "link-free field contracts must equal linked (cw={cw})");
        }
        // Under closed-world, sink (FuncId 1) gets a field at offset 0.
        let merged = merge_modules(vec![a.clone(), b.clone()], "l");
        let params = synthesize(&merged, true);
        let got = synthesize_fields_program(&[&a, &b], &params, true);
        assert_eq!(got.get(&(FuncId(1), 0)).map(|v| v.len()), Some(1), "sink gets one field");
    }

    /// Randomised guard for member-provenance over random multi-module programs
    /// that build regions, store valid pointers into fields (at offset 0 and via a
    /// constant `PtrOffset`), pass the region cross-module and in-module, and clobber
    /// via extra calls / stores — with `params` taken from `synthesize` so callees
    /// carry the contracts fields attach to.
    #[test]
    fn field_contracts_match_linked_on_random_programs() {
        let mut state: u64 = 0x0F1E_2D3C_4B5A_6978;
        let mut rng = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..300 {
            let n_mods = 2 + (rng() % 2) as usize;
            let per = 2 + (rng() % 3) as usize;
            let total = n_mods * per;
            let name = |gi: usize| format!("k{gi}");
            let mut modules = Vec::new();
            let mut gi = 0usize;
            for _ in 0..n_mods {
                let mut m = Module::new("m");
                for local in 0..per {
                    let mut insts = vec![
                        // R = region (16B, holds two 8B slots), B = a valid 8B buffer.
                        Inst::Alloc {
                            dst: RegId(1),
                            region: csolver_core::RegionKind::Stack,
                            elem: Type::int(64),
                            count: Operand::int(64, 2),
                            align: 8,
                        },
                        Inst::Alloc {
                            dst: RegId(2),
                            region: csolver_core::RegionKind::Stack,
                            elem: Type::int(64),
                            count: Operand::int(64, 1),
                            align: 8,
                        },
                    ];
                    // Maybe a field pointer R + k*8.
                    if rng() % 2 == 0 {
                        insts.push(Inst::PtrOffset {
                            dst: RegId(3),
                            base: Operand::Reg(RegId(1)),
                            index: Operand::int(64, (rng() % 2) as u128),
                            elem: Type::int(64),
                        });
                    }
                    // Maybe store B (a valid ptr) or an unknown value into R@0 or the field.
                    if rng() % 3 != 0 {
                        let target = if rng() % 2 == 0 { RegId(1) } else { RegId(3) };
                        let value = if rng() % 3 == 0 {
                            Operand::int(64, 0) // unknown value clears the slot
                        } else {
                            Operand::Reg(RegId(2))
                        };
                        insts.push(Inst::Store {
                            ty: Type::ptr(Type::int(64)),
                            ptr: Operand::Reg(target),
                            value,
                            align: 8,
                        });
                    }
                    // Pass R to some targets (and maybe escape it via an extra call).
                    for _ in 0..(1 + rng() % 2) {
                        let tgt = (rng() as usize) % total;
                        insts.push(Inst::Call {
                            dst: None,
                            callee: Callee::Symbol(name(tgt)),
                            args: vec![Operand::Reg(RegId(1))],
                            ret_ty: Type::Unit,
                            ret_ref: None,
                        });
                    }
                    if rng() % 5 == 0 {
                        let e = (rng() as usize) % total;
                        insts.push(Inst::Assign {
                            dst: RegId(9),
                            ty: Type::ptr(Type::int(32)),
                            value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                        });
                    }
                    m.functions.push(func(
                        local as u32,
                        &name(gi),
                        vec![(RegId(0), Type::ptr(Type::int(64)))],
                        insts,
                    ));
                    gi += 1;
                }
                modules.push(m);
            }
            let cw = rng() & 1 == 0;
            let refs: Vec<&Module> = modules.iter().collect();
            let merged = merge_modules(modules.clone(), "linked");
            let params = synthesize(&merged, cw);
            let want = synthesize_fields(&merged, &params, cw);
            let got = synthesize_fields_program(&refs, &params, cw);
            assert_eq!(got, want, "link-free != linked field contracts (cw={cw})");
        }
    }

    /// The parallel-merge property: building the whole-program facts in two shards
    /// and merging them in order must give the same four result maps as pushing all
    /// modules sequentially — so shards can be extracted in parallel. Covers all
    /// four builders' `merge` at once via `WholeProgramFacts`.
    #[test]
    fn wholeprog_facts_shard_and_merge_equals_sequential() {
        let mut state: u64 = 0x00DE_AD57_A11E_D000;
        let mut rng = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..200 {
            let n_mods = 3 + (rng() % 3) as usize; // 3..=5 modules (so a split is meaningful)
            let per = 2 + (rng() % 3) as usize;
            let total = n_mods * per;
            let name = |gi: usize| format!("w{gi}");
            let mut modules = Vec::new();
            let mut gi = 0usize;
            for _ in 0..n_mods {
                let mut m = Module::new("m");
                for local in 0..per {
                    let mut insts = vec![
                        Inst::Alloc {
                            dst: RegId(1),
                            region: csolver_core::RegionKind::Stack,
                            elem: Type::int(64),
                            count: Operand::int(64, 2),
                            align: 8,
                        },
                        Inst::Alloc {
                            dst: RegId(2),
                            region: csolver_core::RegionKind::Stack,
                            elem: Type::int(64),
                            count: Operand::int(64, 1),
                            align: 8,
                        },
                    ];
                    if rng() % 2 == 0 {
                        insts.push(Inst::Store {
                            ty: Type::ptr(Type::int(64)),
                            ptr: Operand::Reg(RegId(1)),
                            value: Operand::Reg(RegId(2)),
                            align: 8,
                        });
                    }
                    for _ in 0..(1 + rng() % 2) {
                        let tgt = (rng() as usize) % total;
                        let arg = if rng() % 2 == 0 { Operand::Reg(RegId(1)) } else { Operand::Reg(RegId(0)) };
                        insts.push(Inst::Call {
                            dst: None,
                            callee: Callee::Symbol(name(tgt)),
                            args: vec![arg],
                            ret_ty: Type::Unit,
                            ret_ref: None,
                        });
                    }
                    if rng() % 5 == 0 {
                        let e = (rng() as usize) % total;
                        insts.push(Inst::Assign {
                            dst: RegId(9),
                            ty: Type::ptr(Type::int(32)),
                            value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                        });
                    }
                    m.functions.push(func(
                        local as u32,
                        &name(gi),
                        vec![(RegId(0), Type::ptr(Type::int(64)))],
                        insts,
                    ));
                    gi += 1;
                }
                modules.push(m);
            }
            let cw = rng() & 1 == 0;

            let seq = {
                let mut w = crate::WholeProgramFacts::new();
                for m in &modules {
                    w.push_module(m);
                }
                w.finalize(cw)
            };
            let k = 1 + (rng() as usize % (n_mods - 1)); // split point in 1..n_mods
            let sharded = {
                let mut w1 = crate::WholeProgramFacts::new();
                for m in &modules[..k] {
                    w1.push_module(m);
                }
                let mut w2 = crate::WholeProgramFacts::new();
                for m in &modules[k..] {
                    w2.push_module(m);
                }
                w1.merge(w2);
                w1.finalize(cw)
            };
            assert_eq!(seq.summaries, sharded.summaries, "summaries differ");
            assert_eq!(seq.scalars, sharded.scalars, "scalars differ");
            assert_eq!(seq.ptr_contracts, sharded.ptr_contracts, "pointer contracts differ");
            assert_eq!(seq.field_contracts, sharded.field_contracts, "field contracts differ");
        }
    }

    /// Streaming member-provenance: `FieldFacts` (push each module, then `finalize`
    /// with the pointer contracts) must equal `synthesize_fields_program` (and hence
    /// `synthesize_fields∘merge`) over random field-building programs — the per-block
    /// analysis replayed from body-free facts.
    #[test]
    fn field_facts_match_synthesize_fields_program_on_random() {
        let mut state: u64 = 0x0FAC_E0FF_1234_5678;
        let mut rng = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut total_with_fields = 0;
        for _ in 0..300 {
            let n_mods = 2 + (rng() % 2) as usize;
            let per = 2 + (rng() % 3) as usize;
            let total = n_mods * per;
            let name = |gi: usize| format!("d{gi}");
            let mut modules = Vec::new();
            let mut gi = 0usize;
            for _ in 0..n_mods {
                let mut m = Module::new("m");
                for local in 0..per {
                    let mut insts = vec![
                        Inst::Alloc {
                            dst: RegId(1),
                            region: csolver_core::RegionKind::Stack,
                            elem: Type::int(64),
                            count: Operand::int(64, 2),
                            align: 8,
                        },
                        Inst::Alloc {
                            dst: RegId(2),
                            region: csolver_core::RegionKind::Stack,
                            elem: Type::int(64),
                            count: Operand::int(64, 1),
                            align: 8,
                        },
                    ];
                    if rng() % 2 == 0 {
                        insts.push(Inst::PtrOffset {
                            dst: RegId(3),
                            base: Operand::Reg(RegId(1)),
                            index: Operand::int(64, (rng() % 2) as u128),
                            elem: Type::int(64),
                        });
                    }
                    if rng() % 3 != 0 {
                        let target = if rng() % 2 == 0 { RegId(1) } else { RegId(3) };
                        let value = if rng() % 3 == 0 { Operand::int(64, 0) } else { Operand::Reg(RegId(2)) };
                        insts.push(Inst::Store {
                            ty: Type::ptr(Type::int(64)),
                            ptr: Operand::Reg(target),
                            value,
                            align: 8,
                        });
                    }
                    for _ in 0..(1 + rng() % 2) {
                        let tgt = (rng() as usize) % total;
                        insts.push(Inst::Call {
                            dst: None,
                            callee: Callee::Symbol(name(tgt)),
                            args: vec![Operand::Reg(RegId(1))],
                            ret_ty: Type::Unit,
                            ret_ref: None,
                        });
                    }
                    if rng() % 5 == 0 {
                        let e = (rng() as usize) % total;
                        insts.push(Inst::Assign {
                            dst: RegId(9),
                            ty: Type::ptr(Type::int(32)),
                            value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                        });
                    }
                    m.functions.push(func(
                        local as u32,
                        &name(gi),
                        vec![(RegId(0), Type::ptr(Type::int(64)))],
                        insts,
                    ));
                    gi += 1;
                }
                modules.push(m);
            }
            let cw = rng() & 1 == 0;
            let refs: Vec<&Module> = modules.iter().collect();
            let params = synthesize_program(&refs, cw);
            let want = synthesize_fields_program(&refs, &params, cw);
            let mut facts = FieldFacts::default();
            for m in &refs {
                facts.push_module(m);
            }
            let got = facts.finalize(&params, cw);
            assert_eq!(got, want, "streamed field contracts != synthesize_fields_program (cw={cw})");
            total_with_fields += usize::from(!got.is_empty());
        }
        assert!(total_with_fields > 0, "no program produced a field contract — test is vacuous");
    }

    /// Streaming property for member-provenance: push each module then **drop it**,
    /// then `finalize`, equals the linked field contracts.
    #[test]
    fn field_facts_stream_and_drop_equals_linked() {
        let caller = {
            let mut m = Module::new("a");
            m.functions.push(func(
                0,
                "caller",
                vec![],
                vec![
                    Inst::Alloc {
                        dst: RegId(1),
                        region: csolver_core::RegionKind::Stack,
                        elem: Type::int(64),
                        count: Operand::int(64, 2),
                        align: 8,
                    },
                    Inst::Alloc {
                        dst: RegId(2),
                        region: csolver_core::RegionKind::Stack,
                        elem: Type::int(64),
                        count: Operand::int(64, 1),
                        align: 8,
                    },
                    Inst::Store {
                        ty: Type::ptr(Type::int(64)),
                        ptr: Operand::Reg(RegId(1)),
                        value: Operand::Reg(RegId(2)),
                        align: 8,
                    },
                    Inst::Call {
                        dst: None,
                        callee: Callee::Symbol("sink".into()),
                        args: vec![Operand::Reg(RegId(1))],
                        ret_ty: Type::Unit,
                        ret_ref: None,
                    },
                ],
            ));
            m
        };
        let callee = {
            let mut m = Module::new("b");
            m.functions.push(func(0, "sink", vec![(RegId(0), Type::ptr(Type::int(64)))], vec![]));
            m
        };
        let merged = merge_modules(vec![caller.clone(), callee.clone()], "l");
        let params = synthesize(&merged, true);
        let want = synthesize_fields(&merged, &params, true);
        let mut facts = FieldFacts::default();
        {
            let m0 = caller;
            facts.push_module(&m0);
        }
        {
            let m1 = callee;
            facts.push_module(&m1);
        }
        assert_eq!(facts.finalize(&params, true), want, "streamed+dropped == linked field contracts");
    }

    /// The streaming property: pushing modules one at a time and **dropping each**
    /// right after `push_module` yields the same scalar preconditions as the linked
    /// module — the caller is pushed and dropped before its callee's module is even
    /// seen, so a whole-program pass needs no IR resident.
    #[test]
    fn scalar_facts_stream_and_drop_equals_linked() {
        let ip = |r: u32| vec![(RegId(r), Type::int(32))];
        let caller = {
            let mut m = Module::new("a");
            m.functions.push(func(0, "caller", vec![], vec![call(Callee::Symbol("t".into()), 9)]));
            m
        };
        let callee = {
            let mut m = Module::new("b");
            m.functions.push(func(0, "t", ip(0), vec![]));
            m
        };
        let want = synthesize_scalars(&merge_modules(vec![caller.clone(), callee.clone()], "l"), true);
        let mut facts = ScalarFacts::default();
        {
            let m0 = caller;
            facts.push_module(&m0);
        }
        {
            let m1 = callee;
            facts.push_module(&m1);
        }
        assert_eq!(facts.finalize(true), want, "streamed+dropped == linked");
    }

    /// Randomised guard: over many random multi-module programs (cross-module and
    /// in-module constant-argument calls, random address-taking, random closed-world
    /// flag), the link-free scalar preconditions must always equal the linked ones.
    #[test]
    fn scalar_preconditions_match_linked_on_random_programs() {
        let mut state: u64 = 0x0BEE_F123_4567_89AB;
        let mut rng = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..300 {
            let n_mods = 2 + (rng() % 2) as usize; // 2..=3
            let per = 2 + (rng() % 3) as usize; // 2..=4
            let total = n_mods * per;
            let name = |gi: usize| format!("g{gi}");
            let mut modules = Vec::new();
            let mut gi = 0usize;
            for _ in 0..n_mods {
                let mut m = Module::new("m");
                for local in 0..per {
                    let mut insts = Vec::new();
                    for _ in 0..(rng() % 3) {
                        let tgt = (rng() as usize) % total;
                        let v = (rng() % 20) as i128;
                        insts.push(call(Callee::Symbol(name(tgt)), v));
                    }
                    if rng() % 4 == 0 {
                        let e = (rng() as usize) % total;
                        insts.push(Inst::Assign {
                            dst: RegId(50),
                            ty: Type::ptr(Type::int(32)),
                            value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                        });
                    }
                    m.functions.push(func(
                        local as u32,
                        &name(gi),
                        vec![(RegId(0), Type::int(32))],
                        insts,
                    ));
                    gi += 1;
                }
                modules.push(m);
            }
            let cw = rng() & 1 == 0;
            let refs: Vec<&Module> = modules.iter().collect();
            let got = synthesize_scalars_program(&refs, cw);
            let want = synthesize_scalars(&merge_modules(modules.clone(), "linked"), cw);
            assert_eq!(got, want, "link-free != linked scalar preconditions (cw={cw})");
        }
    }
}
