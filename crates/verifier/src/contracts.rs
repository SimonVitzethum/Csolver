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

use csolver_ir::{
    Callee, Condition, Const, FieldContract, FuncId, Inst, Module, Operand, PtrContract, RegId,
    SizeSpec, Terminator,
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
