use super::*;

/// The API effect contracts, parsed once from the embedded default files (allocators,
/// deallocators, user-copies). Recognized calls are lowered from these instead of a
/// hardcoded table; see [`csolver_contracts`] and `crates/contracts/data/*.contract`.
pub(crate) fn contracts() -> &'static Contracts {
    static CONTRACTS: OnceLock<Contracts> = OnceLock::new();
    CONTRACTS.get_or_init(Contracts::defaults)
}

/// Interns provenance label and capability names (a shared namespace) to stable `u32`
/// ids, and precomputes the id-keyed grant relation, so the emitted `ProvLabel`/
/// `CapRequire` instructions and `Module::prov_grants` speak in ids. Built once from the
/// global contracts (deterministic: names sorted before assigning ids).
pub(crate) struct ProvInterner {
    pub(crate) ids: HashMap<String, u32>,
    pub(crate) grants: HashMap<u32, std::collections::HashSet<u32>>,
}

impl ProvInterner {
    pub(crate) fn id(&self, name: &str) -> Option<u32> {
        self.ids.get(name).copied()
    }
}

/// The entry-seed `ProvLabel`s for a function definition: from any `seed arg_k <label>`
/// effects in this function's own contract (`Effect::Seed`), a `ProvLabel` on the named
/// parameter. Empty for a function with no seed contract (the sound default).
pub(crate) fn entry_seed_insts(name: &str, params: &[(RegId, Type)]) -> Vec<Inst> {
    let Some(contract) = contracts().lookup(name) else { return Vec::new() };
    let mut seeds = Vec::new();
    for effect in &contract.effects {
        if let Effect::Seed { arg, label } = effect {
            if let (Some((reg, _)), Some(id)) = (params.get(*arg), prov_interner().id(label)) {
                seeds.push(Inst::ProvLabel { ptr: Operand::Reg(*reg), label: id });
            }
        }
    }
    seeds
}

pub(crate) fn prov_interner() -> &'static ProvInterner {
    static INTERNER: OnceLock<ProvInterner> = OnceLock::new();
    INTERNER.get_or_init(|| {
        let c = contracts();
        // Collect every label/capability name: the lattice keys (labels) and values
        // (capabilities), plus any name mentioned by a `label`/`require` effect.
        let mut names: Vec<&str> = Vec::new();
        for (label, caps) in c.lattice() {
            names.push(label);
            names.extend(caps.iter().map(String::as_str));
        }
        for contract in c.iter() {
            for effect in &contract.effects {
                match effect {
                    Effect::Label { label, .. } => names.push(label),
                    Effect::Require { cap, .. } => names.push(cap),
                    Effect::TaintSource { label, .. }
                    | Effect::TaintSink { label, .. }
                    | Effect::TaintSanitize { label, .. } => names.push(label),
                    Effect::TypestateSet { protocol, state, .. }
                    | Effect::TypestateRequire { protocol, state, .. }
                    | Effect::TypestateLeak { protocol, state } => {
                        names.push(protocol);
                        names.push(state);
                    }
                    Effect::TypestateYield { protocol, from, to } => {
                        names.push(protocol);
                        names.push(from);
                        names.push(to);
                    }
                    Effect::Refcount { protocol, .. } => names.push(protocol),
                    _ => {}
                }
            }
        }
        names.sort_unstable();
        names.dedup();
        let ids: HashMap<String, u32> =
            names.iter().enumerate().map(|(i, n)| (n.to_string(), i as u32)).collect();
        let grants = c
            .lattice()
            .iter()
            .filter_map(|(label, caps)| {
                let lid = *ids.get(label)?;
                let cset = caps.iter().filter_map(|c| ids.get(c).copied()).collect();
                Some((lid, cset))
            })
            .collect();
        ProvInterner { ids, grants }
    })
}

/// Lower a recognized API call from its `contract` into the modelling MSIR instructions.
/// Returns `true` if the call was handled (and should not fall through to a generic call).
pub(crate) fn emit_contract(
    ctx: &mut Ctx,
    insts: &mut Vec<Inst>,
    contract: &ApiContract,
    dst: Option<&str>,
    args: &[LValue],
    ret: &LType,
) -> Result<bool> {
    let mut handled = false;
    let mut result_bound = false;
    for effect in &contract.effects {
        match effect {
            // A fresh heap region (byte-granular, `elem = i8`) whose result pointer is
            // the call value — only meaningful when that result is actually used.
            Effect::Alloc { size, align, external } => {
                let Some(dst) = dst else { continue };
                let Some(count) = size_operand(ctx, insts, size, args)? else { continue };
                insts.push(Inst::Alloc {
                    dst: ctx.reg(dst)?,
                    // An externally-backed MMIO mapping is a `Global` region (initialized
                    // static-like storage); an ordinary allocator is `Heap` (fresh bytes).
                    region: if *external { RegionKind::Global } else { RegionKind::Heap },
                    elem: Type::int(8),
                    count,
                    align: *align,
                });
                handled = true;
                result_bound = true;
            }
            Effect::Free { ptr } => {
                if let Some(a) = args.get(*ptr) {
                    insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: ctx.operand(a, 64)? });
                    handled = true;
                }
            }
            // A bulk write of `len` bytes to the argument buffer — carries the in-bounds
            // obligation (refutable via `check_mem_intrinsic`). `fill=user` taints the
            // region so a value read back is a genuine adversarial input.
            Effect::Write { ptr, len, fill, from } => {
                if let Some(a) = args.get(*ptr) {
                    let Some(len) = size_operand(ctx, insts, len, args)? else { continue };
                    let kind = match fill {
                        Fill::User => MemKind::UserFill,
                        Fill::Undef => MemKind::Set,
                    };
                    // For a `fill=user` copy, carry the USER source pointer (`from=arg<k>`)
                    // as the intrinsic's `src` so the executor can detect a double-fetch.
                    let src = match from.and_then(|k| args.get(k)) {
                        Some(s) => Some(ctx.operand(s, 64)?),
                        None => None,
                    };
                    insts.push(Inst::MemIntrinsic { kind, dst: ctx.operand(a, 64)?, src, len });
                    handled = true;
                }
            }
            // A bulk read carries the in-bounds obligation (the read must stay within the
            // region). A plain in-kernel read is modelled as a bounded `Set`; a read whose
            // bytes are disclosed to userspace (`copy_to_user`, `sink=user`) is a `UserDrain`
            // that additionally carries the `NoInfoLeak` obligation.
            Effect::Read { ptr, len, sink } => {
                if let Some(a) = args.get(*ptr) {
                    let Some(len) = size_operand(ctx, insts, len, args)? else { continue };
                    let kind = match sink {
                        ReadSink::Internal => MemKind::Set,
                        ReadSink::User => MemKind::UserDrain,
                    };
                    insts.push(Inst::MemIntrinsic { kind, dst: ctx.operand(a, 64)?, src: None, len });
                    handled = true;
                }
            }
            // Provenance labelling / capability requirements (the Copy-Fail write-to-a-
            // read-only-page class): the label/cap names are interned to ids the executor
            // resolves against `Module::prov_grants`. These do NOT mark the call handled —
            // an otherwise-unmodelled call still falls through to a generic (opaque) call,
            // it just also carries the provenance effect.
            Effect::Label { ptr, label } => {
                if let (Some(a), Some(id)) = (args.get(*ptr), prov_interner().id(label)) {
                    insts.push(Inst::ProvLabel { ptr: ctx.operand(a, 64)?, label: id });
                }
            }
            Effect::Require { ptr, cap } => {
                if let (Some(a), Some(id)) = (args.get(*ptr), prov_interner().id(cap)) {
                    insts.push(Inst::CapRequire { ptr: ctx.operand(a, 64)?, cap: id });
                }
            }
            Effect::Propagate { dst, src } => {
                if let (Some(d), Some(s)) = (args.get(*dst), args.get(*src)) {
                    insts.push(Inst::ProvPropagate {
                        dst: ctx.operand(d, 64)?,
                        src: ctx.operand(s, 64)?,
                    });
                }
            }
            Effect::RequireIfAlias { a, b, cap } => {
                if let (Some(pa), Some(pb), Some(id)) =
                    (args.get(*a), args.get(*b), prov_interner().id(cap))
                {
                    insts.push(Inst::CapRequireIfAlias {
                        a: ctx.operand(pa, 64)?,
                        b: ctx.operand(pb, 64)?,
                        cap: id,
                    });
                }
            }
            // A `seed` is applied at the seeded function's OWN entry (see `entry_seeds`), not
            // at call sites — a no-op here.
            Effect::Seed { .. } => {}
            // Read the two field pointers back from the object (via read-your-writes of the
            // prior field stores — the inlined `req->src = …; req->dst = …`) and apply the
            // in-place-alias capability check to them. A dedicated inst so the executor reads
            // the fields *internally* (no `ValidRead`/`InBounds` obligation on the analyzer's
            // own field reads — those would spuriously FAIL on a small/opaque object).
            Effect::RequireIfAliasFields { arg, off_a, off_b, cap } => {
                if let (Some(a), Some(id)) = (args.get(*arg), prov_interner().id(cap)) {
                    insts.push(Inst::CapRequireIfAliasFields {
                        obj: ctx.operand(a, 64)?,
                        off_a: *off_a,
                        off_b: *off_b,
                        cap: id,
                    });
                }
            }
            // Directional taint (injection J / tainted-length F / info-flow D). A `taint-sink`
            // on an argument emits the check inline. A `taint-source`/`taint-sanitize` on an
            // **argument** likewise; when the target is `ret` (the call's result) it is deferred
            // and emitted *after* the result register is bound (below).
            Effect::TaintSink { arg, label } => {
                if let (Some(a), Some(id)) = (args.get(*arg), prov_interner().id(label)) {
                    insts.push(Inst::TaintCheck { val: ctx.operand(a, 64)?, taint: id });
                }
            }
            Effect::TaintSource { arg, label } if *arg != RET_ARG => {
                if let (Some(a), Some(id)) = (args.get(*arg), prov_interner().id(label)) {
                    insts.push(Inst::TaintSource { val: ctx.operand(a, 64)?, taint: id });
                }
            }
            Effect::TaintSanitize { arg, label } if *arg != RET_ARG => {
                if let (Some(a), Some(id)) = (args.get(*arg), prov_interner().id(label)) {
                    insts.push(Inst::TaintClear { val: ctx.operand(a, 64)?, taint: id });
                }
            }
            // `ret`-targeted taint source/sanitiser: handled after result binding.
            Effect::TaintSource { .. } | Effect::TaintSanitize { .. } => {}
            // Typestate transitions/obligations (the protocol tracker). `typestate-set` on a
            // non-`ret` argument, and all `typestate-require`, are emitted inline; a `ret`-
            // targeted set is deferred to after the result binding (below).
            Effect::TypestateSet { arg, protocol, state } if *arg != RET_ARG => {
                if let (Some(a), Some(p), Some(s)) =
                    (args.get(*arg), prov_interner().id(protocol), prov_interner().id(state))
                {
                    insts.push(Inst::TypestateSet { val: ctx.operand(a, 64)?, protocol: p, state: s });
                }
            }
            Effect::TypestateRequire { arg, protocol, state, negate } => {
                if let (Some(a), Some(p), Some(s)) =
                    (args.get(*arg), prov_interner().id(protocol), prov_interner().id(state))
                {
                    insts.push(Inst::TypestateRequire {
                        val: ctx.operand(a, 64)?,
                        protocol: p,
                        state: s,
                        negate: *negate,
                    });
                }
            }
            // `ret`-targeted typestate-set: handled after result binding.
            Effect::TypestateSet { .. } => {}
            // Protocol-wide yield (TOCTOU): not tied to an argument.
            Effect::TypestateYield { protocol, from, to } => {
                if let (Some(p), Some(fr), Some(t)) = (
                    prov_interner().id(protocol),
                    prov_interner().id(from),
                    prov_interner().id(to),
                ) {
                    insts.push(Inst::TypestateYield { protocol: p, from: fr, to: t });
                }
            }
            // Reference-count inc/dec.
            Effect::Refcount { arg, protocol, dec, checked } => {
                if let (Some(a), Some(p)) = (args.get(*arg), prov_interner().id(protocol)) {
                    insts.push(Inst::Refcount {
                        val: ctx.operand(a, 64)?,
                        protocol: p,
                        dec: *dec,
                        checked: *checked,
                    });
                }
            }
            // Leak-state declarations are collected globally and injected before returns
            // (see `inject_leak_and_secret_checks`), not emitted at a call.
            Effect::TypestateLeak { .. } => {}
            // A memory barrier: recorded in the interleaving trace as a fence, plus — for a
            // `smp_store_release`/`smp_load_acquire` (`access = Some(arg)`) — the flag access
            // the fence orders, so the message-passing handoff is modelled. If the argument is
            // missing the barrier still lowers as a bare fence (sound).
            Effect::Barrier { kind, access } => {
                let access = access
                    .and_then(|i| args.get(i))
                    .and_then(|a| ctx.operand(a, 64).ok());
                insts.push(Inst::Barrier { kind: *kind, access });
            }
            // Thread spawn/join (happens-before). The child function name comes from the
            // function-pointer argument (a global symbol); skip if it is not a direct symbol.
            Effect::Spawn { arg } => {
                if let Some(LValue::Global(child)) = args.get(*arg) {
                    insts.push(Inst::Spawn { child: child.clone() });
                }
            }
            Effect::Join => insts.push(Inst::Join),
            Effect::Cas { arg } => {
                if let Some(a) = args.get(*arg) {
                    insts.push(Inst::Cas { val: ctx.operand(a, 64)? });
                }
            }
            // Synchronisation classification (locks, blocking, IRQ/RCU state, per-CPU,
            // container lookups): consumed by the symbolic executor's pre-solve collector
            // (`csolver_symbolic::sync`), which matches the surviving call by name — no
            // instruction to emit, and the call must NOT be marked handled.
            Effect::LockAcquire { .. }
            | Effect::Blocking
            | Effect::IrqDisable
            | Effect::IrqEnable
            | Effect::RcuReadLock
            | Effect::RcuReadUnlock
            | Effect::PercpuPtr
            | Effect::ContainerLookup { .. }
            | Effect::GlobalLookup { .. } => {}
        }
    }
    // A recognized non-allocating call still yields a result the caller may use
    // (e.g. `copy_from_user`'s bytes-not-copied) — bind it to an opaque value.
    if handled && !result_bound {
        if let Some(dst) = dst {
            insts.push(Inst::Assign {
                dst: ctx.reg(dst)?,
                ty: lower_type(ret),
                value: RValue::Use(Operand::Const(Const::Undef)),
            });
        }
    }
    // `ret`-targeted effects need the result register bound *first*. When this contract fully
    // models the call (`handled`), the result is bound above, so emit them now; otherwise the
    // real `Inst::Call` (emitted by the caller after this returns) binds the result, so the
    // caller emits the ret-effects afterwards (see `emit_ret_effects`).
    if handled {
        emit_ret_effects(ctx, insts, contract, dst)?;
    }
    Ok(handled)
}

/// Emit the `ret`-targeted contract effects (taint source/sanitiser, typestate transition) —
/// which mark or clear the **result** value's provenance/taint/state. Called once the result
/// register is bound (by a memory model inside `emit_contract`, or by the real call the caller
/// emits for an annotation-only contract). A `recv`-style tainted return, or `fopen`'s returned
/// `file.open` handle, is the archetype.
pub(crate) fn emit_ret_effects(
    ctx: &mut Ctx,
    insts: &mut Vec<Inst>,
    contract: &ApiContract,
    dst: Option<&str>,
) -> Result<()> {
    let Some(dst) = dst else { return Ok(()) };
    for effect in &contract.effects {
        match effect {
            Effect::TaintSource { arg, label } if *arg == RET_ARG => {
                if let Some(id) = prov_interner().id(label) {
                    insts.push(Inst::TaintSource { val: Operand::Reg(ctx.reg(dst)?), taint: id });
                }
            }
            Effect::TaintSanitize { arg, label } if *arg == RET_ARG => {
                if let Some(id) = prov_interner().id(label) {
                    insts.push(Inst::TaintClear { val: Operand::Reg(ctx.reg(dst)?), taint: id });
                }
            }
            Effect::TypestateSet { arg, protocol, state } if *arg == RET_ARG => {
                if let (Some(p), Some(s)) = (prov_interner().id(protocol), prov_interner().id(state)) {
                    insts.push(Inst::TypestateSet {
                        val: Operand::Reg(ctx.reg(dst)?),
                        protocol: p,
                        state: s,
                    });
                }
            }
            _ => {}
        }
    }
    Ok(())
}
