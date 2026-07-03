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
//! ## Soundness conditions (each enforced here)
//!
//! 1. The callee has internal linkage (`Module::internal`).
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
    Callee, Condition, Const, FuncId, Inst, Module, Operand, PtrContract, RegId, SizeSpec,
    Terminator,
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

/// The assumption id surfaced by proofs that rest on a synthesized contract.
pub(crate) const INTERNAL_CALL_CONTRACT: &str = "internal-call-contract";

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
pub(crate) fn synthesize(module: &Module) -> HashMap<(FuncId, u32), PtrContract> {
    let mut acc: HashMap<(FuncId, u32), PtrContract> = HashMap::new();
    loop {
        let round = synthesize_round(module, &acc);
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
) -> HashMap<(FuncId, u32), PtrContract> {
    let escaped = address_taken_names(module);

    // Eligible (callee, param-index) pairs: internal, address never taken,
    // pointer-typed, no declared contract.
    let mut candidates: HashSet<(FuncId, u32)> = HashSet::new();
    for f in &module.functions {
        if !module.internal.contains(&f.id) || escaped.contains(&f.name) {
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
            Some((
                key,
                PtrContract {
                    size: SizeSpec::Bytes(g.size),
                    align: g.align,
                    readable: g.readable,
                    writable: g.writable,
                    assumption: Some(INTERNAL_CALL_CONTRACT),
                    // A synthesized contract is the *weakest* call-site
                    // guarantee; a witness against it may combine argument
                    // values no single caller produces — prove-only.
                    refutable: false,
                },
            ))
        })
        .collect()
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
