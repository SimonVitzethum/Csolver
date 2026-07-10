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
        let defs = local_defs(caller, module, prior);
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
        let defs = local_defs(caller, module, params);
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
    module: &Module,
    prior: &HashMap<(FuncId, u32), PtrContract>,
) -> HashMap<RegId, SiteGuarantee> {
    let mut defs = HashMap::new();
    for (i, (reg, _)) in f.params.iter().enumerate() {
        let key = (f.id, i as u32);
        if let Some(c) = module.param_contracts.get(&key).or_else(|| prior.get(&key)) {
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
            let Some(elem_size) = elem.size_bytes(&module.layout) else { continue };
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
            let Some(elem_size) = elem.size_bytes(&module.layout) else { continue };
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
