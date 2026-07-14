use super::*;

pub(crate) fn summarize_fn(f: &Function) -> Summary {
    // A write/free is *caller-visible* only through memory the caller can also
    // reach: anything but the function's own allocations. A store into a local
    // alloca (rustc's debug IR round-trips every value through one) cannot alias
    // any region the caller tracks — distinct allocations never alias — so it
    // must not force the caller to discard its heap knowledge.
    let local = local_alloc_regs(f);
    let is_local = |op: &Operand| matches!(op, Operand::Reg(r) if local.contains(r));
    let mut writes = false;
    let mut frees = false;
    for i in f.blocks.iter().flat_map(|b| &b.insts) {
        match i {
            Inst::Store { ptr, .. } => writes |= !is_local(ptr),
            // A bulk write is a write (previously missed: a callee memcpy-ing
            // into a parameter looked pure — stale caller heap, false-PASS
            // material). Inline asm is opaque: assume both effects.
            Inst::MemIntrinsic { dst, .. } => writes |= !is_local(dst),
            Inst::Asm { .. } => {
                writes = true;
                frees = true;
            }
            Inst::Dealloc { ptr, .. } => frees |= !is_local(ptr),
            _ => {}
        }
    }

    Summary {
        ret: ret_of_fn(f).0,
        writes,
        frees,
        frees_arg: derive_frees_arg(f),
        prov: prov_transfer_of_fn(f),
        refcount_effect: refcount_effect_of_fn(f),
        escapes_stack: escapes_stack_through(f),
    }
}

/// Pointer-parameter indices through which the function **unconditionally** stores the address
/// of one of its own stack locals (`*out = &x`). Only the **entry block** is scanned — it always
/// executes, so a store found there is unconditional and the caller-side dangling mark can never
/// be a false FAIL (a conditional escape in a later block is soundly missed, not mis-flagged).
pub(crate) fn escapes_stack_through(f: &Function) -> Vec<usize> {
    let Some(entry) = f.blocks.iter().find(|b| b.id == f.entry) else { return Vec::new() };
    let mut env: HashMap<RegId, AbsVal> = HashMap::new();
    for (k, (reg, ty)) in f.params.iter().enumerate() {
        let v = if ty.is_ptr() {
            AbsVal::PtrArg { arg: k, off: Affine::constant(0) }
        } else {
            AbsVal::Scalar(Affine::param(k))
        };
        env.insert(*reg, v);
    }
    let mut escapes = Vec::new();
    for inst in &entry.insts {
        // A store of a local stack address through a parameter pointer is an out-param escape.
        if let Inst::Store { ptr, value, .. } = inst {
            if let (AbsVal::PtrArg { arg, .. }, AbsVal::LocalStack) =
                (eval_operand(ptr, &env), eval_operand(value, &env))
            {
                if !escapes.contains(&arg) {
                    escapes.push(arg);
                }
            }
        }
        match inst {
            Inst::Alloc { dst, .. } => {
                env.insert(*dst, AbsVal::LocalStack);
            }
            Inst::Assign { dst, value, .. } => {
                let v = eval_rvalue(value, &env);
                env.insert(*dst, v);
            }
            Inst::PtrOffset { dst, base, index, elem } => {
                let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1) as i128;
                let v = match (eval_operand(base, &env), eval_operand(index, &env)) {
                    (AbsVal::PtrArg { arg, off }, AbsVal::Scalar(ix)) => {
                        match ix.scale(stride).and_then(|t| off.add(&t)) {
                            Some(o) => AbsVal::PtrArg { arg, off: o },
                            None => AbsVal::Opaque,
                        }
                    }
                    (AbsVal::LocalStack, _) => AbsVal::LocalStack,
                    _ => AbsVal::Opaque,
                };
                env.insert(*dst, v);
            }
            other => {
                if let Some(d) = other.defined_reg() {
                    env.insert(d, AbsVal::Opaque);
                }
            }
        }
    }
    escapes
}

/// The net reference-count change this function makes to each pointer parameter's object, per
/// protocol — a straight-line sum of the `Inst::Refcount` operations whose value is (derived
/// from) a parameter. Composed interprocedurally by the fixpoint in `summarize_module`.
pub(crate) fn refcount_effect_of_fn(f: &Function) -> Vec<(usize, u32, i64)> {
    let params = ptr_param_of(f);
    let mut acc: std::collections::BTreeMap<(usize, u32), i64> = std::collections::BTreeMap::new();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        if let Inst::Refcount { val: Operand::Reg(r), protocol, dec, .. } = inst {
            if let Some(&p) = params.get(r) {
                *acc.entry((p, *protocol)).or_insert(0) += if *dec { -1 } else { 1 };
            }
        }
    }
    acc.into_iter().filter(|(_, d)| *d != 0).map(|((p, proto), d)| (p, proto, d)).collect()
}

/// The parameter a **single-block** function definitely frees: it has exactly one
/// `Dealloc` and that deallocates a bare parameter (a `kfree(p)`-style wrapper). A
/// single block means the free is unconditional (executes on every call), so a call
/// to it definitely frees that argument — the basis for detecting a double-free
/// through two such wrapper calls. Conservative: any other shape (multi-block,
/// several deallocs, inline asm, a non-parameter pointer) yields `None`, so this
/// never over-claims a free (which would risk a false double-free FAIL).
pub(crate) fn derive_frees_arg(f: &Function) -> Option<usize> {
    if f.blocks.len() != 1 {
        return None;
    }
    let params: HashMap<RegId, usize> =
        f.params.iter().enumerate().map(|(i, (r, _))| (*r, i)).collect();
    let mut deallocs = f.blocks[0].insts.iter().filter_map(|i| match i {
        Inst::Dealloc { ptr: Operand::Reg(r), .. } => Some(params.get(r).copied()),
        Inst::Dealloc { .. } | Inst::Asm { .. } => Some(None),
        _ => None,
    });
    match (deallocs.next(), deallocs.next()) {
        (Some(hit), None) => hit,
        _ => None,
    }
}

/// Which pointer parameter (by index) a register **definitely** aliases: the parameter
/// pointers themselves, closed under `PtrOffset` / `Assign(Use|Cast)` (an offset/copy of a
/// parameter pointer stays that parameter's provenance). A register not in the map (a
/// loaded value, a call result, a block parameter) is *not* claimed — sound: we only ever
/// record a provenance transfer between two definite parameter pointers.
pub(crate) fn ptr_param_of(f: &Function) -> HashMap<RegId, usize> {
    let mut map: HashMap<RegId, usize> = HashMap::new();
    for (k, (reg, ty)) in f.params.iter().enumerate() {
        if ty.is_ptr() {
            map.insert(*reg, k);
        }
    }
    loop {
        let mut changed = false;
        let mut relate = |dst: RegId, base: &Operand, map: &mut HashMap<RegId, usize>| {
            if let Operand::Reg(b) = base {
                if let Some(&arg) = map.get(b) {
                    changed |= map.insert(dst, arg).is_none();
                }
            }
        };
        for inst in f.blocks.iter().flat_map(|b| &b.insts) {
            match inst {
                Inst::PtrOffset { dst, base, .. } => relate(*dst, base, &mut map),
                Inst::Assign { dst, value: RValue::Use(op), .. }
                | Inst::Assign { dst, value: RValue::Cast { operand: op, .. }, .. } => {
                    relate(*dst, op, &mut map)
                }
                _ => {}
            }
        }
        if !changed {
            return map;
        }
    }
}

/// Derive a function's provenance-transfer summary from the `ProvLabel`/`ProvPropagate`
/// instructions its body contains (the ones a contract lowered for the recognized calls it
/// makes). Interprocedural composition through direct callees is added by the module
/// fixpoint in [`summarize_module`].
pub(crate) fn prov_transfer_of_fn(f: &Function) -> ProvTransfer {
    let param_of = ptr_param_of(f);
    let arg = |op: &Operand| match op {
        Operand::Reg(r) => param_of.get(r).copied(),
        _ => None,
    };
    let mut prov = ProvTransfer::default();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        match inst {
            Inst::ProvLabel { ptr, label } => {
                if let Some(a) = arg(ptr) {
                    prov.labels.push((a, *label));
                }
            }
            Inst::ProvPropagate { dst, src } => {
                if let (Some(d), Some(s)) = (arg(dst), arg(src)) {
                    prov.transfers.push((d, s));
                }
            }
            _ => {}
        }
    }
    dedup(&mut prov);
    prov
}

pub(crate) fn dedup(prov: &mut ProvTransfer) {
    prov.transfers.sort_unstable();
    prov.transfers.dedup();
    prov.labels.sort_unstable();
    prov.labels.dedup();
}

/// The registers that provably hold pointers into the function's *own*
/// allocations: `Alloc` results, closed under `PtrOffset` / `Assign(Use)` /
/// `Assign(Cast)` to a fixpoint. Conservative in the right direction — a
/// register not in the set (a parameter, a loaded value, a block parameter, a
/// call result) counts as caller-visible.
pub(crate) fn local_alloc_regs(f: &Function) -> std::collections::HashSet<RegId> {
    let mut set = std::collections::HashSet::new();
    loop {
        let mut changed = false;
        for inst in f.blocks.iter().flat_map(|b| &b.insts) {
            let derived = match inst {
                Inst::Alloc { dst, .. } => Some(*dst),
                Inst::PtrOffset { dst, base: Operand::Reg(b), .. } if set.contains(b) => {
                    Some(*dst)
                }
                Inst::Assign { dst, value, .. } => match value {
                    RValue::Use(Operand::Reg(r)) | RValue::Cast { operand: Operand::Reg(r), .. }
                        if set.contains(r) =>
                    {
                        Some(*dst)
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(d) = derived {
                changed |= set.insert(d);
            }
        }
        if !changed {
            return set;
        }
    }
}

/// Characterize the return value across the whole CFG. Instruction results are
/// pure functions of their inputs and are recomputed each pass; the only join
/// points are **block parameters**, whose value is the [`AbsVal::join`] over
/// every incoming branch argument seen so far. Joins are monotone toward
/// `Opaque` (lattice height 2), so the iteration terminates; a defensive pass
/// cap degrades to `Unknown` rather than looping.
///
/// This subsumes the previous single-block analysis and, crucially, covers
/// rustc's guard shape — `entry: cond ? panic-block : ok-block; ok: ret p+off` —
/// where the panic block never returns and thus never joins: the summary comes
/// from the agreeing return sites alone.
/// Whether the function's return value is, on every returning path, exactly the result of
/// one observable call — its index in body-call order (matching `SummaryFacts`' collection,
/// which skips `Unreachable`-terminated blocks). Lets the cross-function fixpoint propagate a
/// callee's `DanglingStack` return through a wrapper.
pub(crate) fn returned_call_index(f: &Function) -> Option<usize> {
    ret_of_fn(f).1
}

pub(crate) fn ret_of_fn(f: &Function) -> (RetSummary, Option<usize>) {
    use csolver_ir::Terminator;

    // dst-register → observable-call index, in the exact order (and Unreachable-skip) that
    // `SummaryFacts::push_module` numbers calls, so an index here names the same call there.
    let mut call_index: HashMap<RegId, usize> = HashMap::new();
    {
        let mut idx = 0usize;
        for b in &f.blocks {
            if matches!(b.term, Terminator::Unreachable) {
                continue;
            }
            for inst in &b.insts {
                if let Inst::Call { dst, .. } = inst {
                    if let Some(d) = dst {
                        call_index.insert(*d, idx);
                    }
                    idx += 1;
                }
            }
        }
    }

    let mut env: HashMap<RegId, AbsVal> = HashMap::new();
    for (k, (reg, ty)) in f.params.iter().enumerate() {
        let v = if ty.is_ptr() {
            AbsVal::PtrArg { arg: k, off: Affine::constant(0) }
        } else {
            AbsVal::Scalar(Affine::param(k))
        };
        env.insert(*reg, v);
    }

    // `param_join[reg]`: the running join of every branch argument bound to the
    // block parameter `reg`. Function parameters are pre-seeded with their call
    // value so that an edge that rebinds one (a back-edge into the entry block)
    // joins *against the seed* rather than replacing it — replacing would claim
    // the loop value holds on the first entry too.
    let mut param_join: HashMap<RegId, AbsVal> = env.clone();
    let by_id: HashMap<_, _> = f.blocks.iter().map(|b| (b.id, b)).collect();

    for _pass in 0..64 {
        let mut changed = false;
        for b in &f.blocks {
            // Bind this block's parameters from the joined incoming values.
            for (reg, _) in &b.params {
                if let Some(v) = param_join.get(reg) {
                    if env.get(reg) != Some(v) {
                        env.insert(*reg, v.clone());
                        changed = true;
                    }
                }
            }
            for inst in &b.insts {
                let (dst, v) = match inst {
                    Inst::Assign { dst, value, .. } => (*dst, eval_rvalue(value, &env)),
                    Inst::PtrOffset { dst, base, index, elem } => {
                        let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1) as i128;
                        let v = match (eval_operand(base, &env), eval_operand(index, &env)) {
                            (AbsVal::PtrArg { arg, off }, AbsVal::Scalar(ix)) => {
                                match ix.scale(stride).and_then(|t| off.add(&t)) {
                                    Some(o) => AbsVal::PtrArg { arg, off: o },
                                    None => AbsVal::Opaque,
                                }
                            }
                            // Offsetting into this frame's own allocation stays a
                            // pointer into that (dangling-on-return) local.
                            (AbsVal::LocalStack, _) => AbsVal::LocalStack,
                            _ => AbsVal::Opaque,
                        };
                        (*dst, v)
                    }
                    // A **stack** allocation of this frame: its address is a local whose
                    // lifetime ends at return, so returning it is a dangling-stack escape. A
                    // **heap** allocation (a `kmalloc`/`malloc` wrapper) outlives the return —
                    // it is a fresh live region for the caller, sized by a constant count.
                    Inst::Alloc { dst, region: RegionKind::Stack, .. } => (*dst, AbsVal::LocalStack),
                    Inst::Alloc { dst, region: RegionKind::Heap, elem, count, .. } => {
                        let size = match count {
                            Operand::Const(Const::Int(bv)) => {
                                let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                                u64::try_from(bv.unsigned()).ok().and_then(|c| c.checked_mul(stride))
                            }
                            _ => None,
                        };
                        (*dst, AbsVal::HeapAlloc { size })
                    }
                    Inst::Alloc { dst, .. } => (*dst, AbsVal::Opaque),
                    // A call result: tracked as `Call(index)` so a wrapper that returns it
                    // can inherit the callee's dangling-stack return in the cross-fn fixpoint.
                    Inst::Call { dst: Some(d), .. } => {
                        let v = call_index.get(d).map_or(AbsVal::Opaque, |&i| AbsVal::Call(i));
                        (*d, v)
                    }
                    other => match other.defined_reg() {
                        Some(dst) => (dst, AbsVal::Opaque),
                        None => continue,
                    },
                };
                if env.get(&dst) != Some(&v) {
                    env.insert(dst, v);
                    changed = true;
                }
            }
            // Propagate branch arguments into the successors' parameter joins.
            let mut feed = |target: BlockId, args: &[Operand]| {
                let Some(tb) = by_id.get(&target) else { return };
                for ((reg, _), arg) in tb.params.iter().zip(args) {
                    let v = eval_operand(arg, &env);
                    let joined = match param_join.get(reg) {
                        Some(prev) => prev.join(&v),
                        None => v,
                    };
                    if param_join.get(reg) != Some(&joined) {
                        param_join.insert(*reg, joined);
                        changed = true;
                    }
                }
            };
            match &b.term {
                Terminator::Br { target, args } => feed(*target, args),
                Terminator::CondBr { then_blk, then_args, else_blk, else_args, .. } => {
                    feed(*then_blk, then_args);
                    feed(*else_blk, else_args);
                }
                // Switch targets carry no arguments; Return/Unreachable have no
                // successors.
                Terminator::Switch { .. } | Terminator::Return(_) | Terminator::Unreachable => {}
            }
        }
        if !changed {
            // Fixpoint reached: join the value of every returning site.
            let mut ret: Option<AbsVal> = None;
            for b in &f.blocks {
                if let Terminator::Return(Some(op)) = &b.term {
                    let v = eval_operand(op, &env);
                    ret = Some(match ret {
                        Some(prev) => prev.join(&v),
                        None => v,
                    });
                }
            }
            return match ret {
                Some(AbsVal::PtrArg { arg, off }) => (RetSummary::PtrFromArg { arg, offset: off }, None),
                Some(AbsVal::Scalar(a)) => (RetSummary::Scalar(a), None),
                Some(AbsVal::LocalStack) => (RetSummary::DanglingStack, None),
                Some(AbsVal::HeapAlloc { size }) => (RetSummary::Alloc { size }, None),
                // The return is a bare call result — no local RetSummary, but the callee index
                // is handed to the cross-function fixpoint for dangling-return propagation.
                Some(AbsVal::Call(i)) => (RetSummary::Unknown, Some(i)),
                _ => (RetSummary::Unknown, None),
            };
        }
    }
    // Pass cap hit (pathological CFG): degrade, never loop or guess.
    (RetSummary::Unknown, None)
}

pub(crate) fn eval_rvalue(rv: &RValue, env: &HashMap<RegId, AbsVal>) -> AbsVal {
    match rv {
        RValue::Use(op) => eval_operand(op, env),
        RValue::Bin { op, lhs, rhs, .. } => {
            match (eval_operand(lhs, env), eval_operand(rhs, env)) {
                (AbsVal::Scalar(a), AbsVal::Scalar(b)) => {
                    let r = match op {
                        BinOp::Add => a.add(&b),
                        BinOp::Sub => a.sub(&b),
                        BinOp::Mul => match (a.as_const(), b.as_const()) {
                            (Some(c), _) => b.scale(c),
                            (_, Some(c)) => a.scale(c),
                            _ => None,
                        },
                        _ => None,
                    };
                    r.map(AbsVal::Scalar).unwrap_or(AbsVal::Opaque)
                }
                _ => AbsVal::Opaque,
            }
        }
        _ => AbsVal::Opaque,
    }
}

pub(crate) fn eval_operand(op: &Operand, env: &HashMap<RegId, AbsVal>) -> AbsVal {
    match op {
        Operand::Reg(r) => match env.get(r) {
            Some(v) => v.clone(),
            None => AbsVal::Opaque,
        },
        Operand::Const(Const::Int(bv)) => AbsVal::Scalar(Affine::constant(bv.unsigned() as i128)),
        _ => AbsVal::Opaque,
    }
}
