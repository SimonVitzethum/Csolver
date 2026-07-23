use super::*;

/// Fold one call site's field guarantees into the running intersection: keep only
/// byte offsets present at *every* site so far, each at the weakest guarantee.
pub(crate) fn intersect_site(
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
pub(crate) fn derive_site(
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
#[allow(clippy::too_many_arguments)]
pub(crate) fn local_defs(
    f: &csolver_ir::Function,
    caller_id: FuncId,
    param_contracts: &HashMap<(FuncId, u32), PtrContract>,
    layout: &csolver_ir::DataLayout,
    prior: &HashMap<(FuncId, u32), PtrContract>,
    hints: &HashMap<(FuncId, RegId), PtrHint>,
    avp: bool,
) -> HashMap<RegId, SiteGuarantee> {
    let mut defs = HashMap::new();
    // A2 (opt-in `--assume-valid-params`): a register the frontend typed with a DWARF/typed-use
    // pointee hint guarantees a `sizeof(pointee)`-byte valid region. Seeded first (lowest
    // precedence) so an exact `alloc`/declared-contract def below overrides it. Only for the
    // caller's own registers (keyed by `caller_id`), matching the merged module's remapped hints.
    if avp {
        for inst in f.blocks.iter().flat_map(|b| &b.insts) {
            if let Some(reg) = inst.defined_reg() {
                if let Some(h) = hints.get(&(caller_id, reg)).filter(|h| h.size > 0) {
                    defs.insert(reg, hint_guarantee(h));
                }
            }
        }
        for (reg, _) in &f.params {
            if let Some(h) = hints.get(&(caller_id, *reg)).filter(|h| h.size > 0) {
                defs.insert(*reg, hint_guarantee(h));
            }
        }
    }
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
pub fn address_taken_names(module: &Module) -> HashSet<String> {
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
                    Inst::TaintSource { val, .. }
                    | Inst::TaintCheck { val, .. }
                    | Inst::TaintClear { val, .. }
                    | Inst::TypestateSet { val, .. }
                    | Inst::TypestateRequire { val, .. }
                    | Inst::Refcount { val, .. }
                    | Inst::SecretCheck { val, .. } => op(val),
                    Inst::TypestateLeakCheck { escaping, .. } => {
                        if let Some(e) = escaping {
                            op(e);
                        }
                    }
                    Inst::TypestateYield { .. } | Inst::Barrier { .. } | Inst::Spawn { .. } | Inst::Join | Inst::Cas { .. } => {}
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
