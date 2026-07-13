use super::*;

/// Evaluate a contract [`SizeExpr`] to a byte-length operand, or `None` if it references
/// an argument the call does not have (then the effect is skipped — a sound fallthrough).
/// Resolve a call's textual callee to an MSIR [`Callee`]. A defined function name
/// becomes `Direct`; the parser's indirect-call marker `<indirect via %n>` becomes a
/// real `Indirect(Operand::Reg(..))` on the dispatched register — so an indirect call
/// through a function pointer can be **devirtualized** (a load from a constant
/// ops-struct/vtable global resolves it to the callee summary) instead of staying an
/// opaque symbol. Any other name is an external `Symbol` (opaque, contract-modelled).
pub(crate) fn resolve_callee(ctx: &Ctx, callee: &str) -> Callee {
    if let Some(local) = callee.strip_prefix("<indirect via %").and_then(|s| s.strip_suffix('>')) {
        if let Ok(r) = ctx.reg(local) {
            return Callee::Indirect(Operand::Reg(r));
        }
    }
    match ctx.func_ids.get(callee) {
        Some(id) => Callee::Direct(*id),
        None => Callee::Symbol(callee.to_string()),
    }
}

/// Emit a precise access obligation for each inline-asm memory operand encoded in the callee
/// name (`|w<i>` = written, `|r<i>` = read). A byte Load/Store through the pointer argument
/// checks it is non-null, live, in-bounds and (for a write) writable — catching a UAF / OOB /
/// null-deref committed *through* the asm's declared memory operand.
/// Bind an inline-asm output register to its **register-dataflow semantic** (from the `|sem…`
/// suffix the parser attached — see `asm_reg_semantic`): `|semZ` → the output is `0`; `|semC<j>`
/// → the output is a copy of argument `j`. Emits an `Inst::Assign` and returns `true` when a
/// semantic was applied (so the caller suppresses the havoc binding), `false` otherwise. Both
/// idioms are always-correct, so this only ever *adds* precision to a previously opaque value.
pub(crate) fn emit_asm_semantic(
    ctx: &mut Ctx,
    insts: &mut Vec<Inst>,
    callee: &str,
    args: &[LValue],
    dst: &str,
    ret: &LType,
) -> Result<bool> {
    let ty = lower_type(ret);
    let width = type_width(ret);
    // Resolve an argument index to a width-coerced operand.
    let arg_op = |ctx: &mut Ctx, j: usize| -> Result<Option<Operand>> {
        Ok(match args.get(j) {
            Some(a) => Some(ctx.operand(a, width)?),
            None => None,
        })
    };
    for spec in callee.split('|') {
        let value = if spec == "semZ" {
            RValue::Use(Operand::int(width, 0))
        } else if let Some(j) = spec.strip_prefix("semC").and_then(|n| n.parse::<usize>().ok()) {
            match arg_op(ctx, j)? {
                Some(a) => RValue::Use(a),
                None => continue,
            }
        } else if let Some(rest) = spec.strip_prefix("semB") {
            // `semB<op>:<jd>:<js>` → args[jd] OP args[js].
            let mut it = rest.splitn(3, ':');
            let op = it.next().and_then(|s| s.chars().next());
            let jd = it.next().and_then(|s| s.parse::<usize>().ok());
            let js = it.next().and_then(|s| s.parse::<usize>().ok());
            match (op.and_then(asm_binop), jd, js) {
                (Some(binop), Some(jd), Some(js)) => match (arg_op(ctx, jd)?, arg_op(ctx, js)?) {
                    (Some(lhs), Some(rhs)) => RValue::Bin { op: binop, lhs, rhs , flags: Default::default() },
                    _ => continue,
                },
                _ => continue,
            }
        } else if let Some(rest) = spec.strip_prefix("semN") {
            // `semNn:<j>` = neg (0 - x); `semNt:<j>` = not (x ^ all-ones).
            let mut it = rest.splitn(2, ':');
            let kind = it.next().and_then(|s| s.chars().next());
            let j = it.next().and_then(|s| s.parse::<usize>().ok());
            match (kind, j.and_then(|j| arg_op(ctx, j).transpose())) {
                (Some('n'), Some(x)) => RValue::Bin { op: BinOp::Sub, lhs: Operand::int(width, 0), rhs: x? , flags: Default::default() },
                (Some('t'), Some(x)) => RValue::Bin { op: BinOp::Xor, lhs: x?, rhs: Operand::int(width, u128::MAX) , flags: Default::default() },
                _ => continue,
            }
        } else {
            continue;
        };
        let d = ctx.reg(dst)?;
        insts.push(Inst::Assign { dst: d, ty, value });
        return Ok(true);
    }
    Ok(false)
}

/// The `BinOp` for an inline-asm semantic binop code letter (see `asm_binop_code` in the parser).
pub(crate) fn asm_binop(code: char) -> Option<BinOp> {
    Some(match code {
        'a' => BinOp::Add,
        's' => BinOp::Sub,
        'n' => BinOp::And,
        'o' => BinOp::Or,
        'x' => BinOp::Xor,
        'l' => BinOp::Shl,
        'r' => BinOp::LShr,
        'h' => BinOp::AShr,
        'm' => BinOp::Mul,
        _ => return None,
    })
}

pub(crate) fn emit_inline_asm_mem_ops(
    ctx: &mut Ctx,
    insts: &mut Vec<Inst>,
    callee: &str,
    args: &[LValue],
) -> Result<()> {
    for spec in callee.split('|').skip(1) {
        let (write, idx_str) = match spec.split_at(1) {
            ("w", n) => (true, n),
            ("r", n) => (false, n),
            _ => continue,
        };
        let Ok(i) = idx_str.parse::<usize>() else { continue };
        let Some(a) = args.get(i) else { continue };
        // Only a pointer operand can be accessed (a register/global/null); an integer immediate
        // is not a memory operand and is skipped.
        if !matches!(a, LValue::Local(_) | LValue::Global(_) | LValue::GlobalOff { .. } | LValue::Null) {
            continue;
        }
        let ptr = ctx.operand(a, 64)?;
        if write {
            insts.push(Inst::Store {
                ty: Type::int(8),
                ptr,
                value: Operand::Const(Const::Undef),
                align: 1,
                volatile: true,
            });
        } else {
            insts.push(Inst::Load { dst: ctx.fresh(), ty: Type::int(8), ptr, align: 1, volatile: true });
        }
    }
    Ok(())
}

pub(crate) fn size_operand(
    ctx: &mut Ctx,
    insts: &mut Vec<Inst>,
    size: &SizeExpr,
    args: &[LValue],
) -> Result<Option<Operand>> {
    Ok(match size {
        SizeExpr::Arg(i) => match args.get(*i) {
            Some(a) => Some(ctx.operand(a, 64)?),
            None => None,
        },
        SizeExpr::Const(n) => Some(Operand::int(64, *n as u128)),
        SizeExpr::Product(a, b) => match (args.get(*a), args.get(*b)) {
            (Some(x), Some(y)) => {
                let lhs = ctx.operand(x, 64)?;
                let rhs = ctx.operand(y, 64)?;
                let tmp = ctx.fresh();
                insts.push(Inst::Assign {
                    dst: tmp,
                    ty: Type::int(64),
                    value: RValue::Bin { op: BinOp::Mul, lhs, rhs , flags: Default::default() },
                });
                Some(Operand::Reg(tmp))
            }
            _ => None,
        },
    })
}

pub(crate) fn type_width(ty: &LType) -> u32 {
    match ty {
        LType::Int(bits) => *bits,
        _ => 64,
    }
}

pub(crate) fn align_or(given: u32, ty: &LType) -> u32 {
    if given > 0 {
        given
    } else {
        lower_type(ty).align_bytes(&LAYOUT).unwrap_or(1) as u32
    }
}

pub(crate) fn lower_bin(op: LBin) -> BinOp {
    match op {
        LBin::Add => BinOp::Add,
        LBin::Sub => BinOp::Sub,
        LBin::Mul => BinOp::Mul,
        LBin::UDiv => BinOp::UDiv,
        LBin::SDiv => BinOp::SDiv,
        LBin::URem => BinOp::URem,
        LBin::SRem => BinOp::SRem,
        LBin::And => BinOp::And,
        LBin::Or => BinOp::Or,
        LBin::Xor => BinOp::Xor,
        LBin::Shl => BinOp::Shl,
        LBin::LShr => BinOp::LShr,
        LBin::AShr => BinOp::AShr,
    }
}

pub(crate) fn lower_pred(p: LPred) -> CmpOp {
    match p {
        LPred::Eq => CmpOp::Eq,
        LPred::Ne => CmpOp::Ne,
        LPred::Ult => CmpOp::Ult,
        LPred::Ule => CmpOp::Ule,
        LPred::Ugt => CmpOp::Ugt,
        LPred::Uge => CmpOp::Uge,
        LPred::Slt => CmpOp::Slt,
        LPred::Sle => CmpOp::Sle,
        LPred::Sgt => CmpOp::Sgt,
        LPred::Sge => CmpOp::Sge,
    }
}

pub(crate) fn lower_cast(c: LCast) -> CastOp {
    match c {
        LCast::Trunc => CastOp::Trunc,
        LCast::ZExt => CastOp::ZExt,
        LCast::SExt => CastOp::SExt,
        LCast::PtrToInt => CastOp::PtrToInt,
        LCast::IntToPtr => CastOp::IntToPtr,
        LCast::Bitcast => CastOp::Bitcast,
    }
}
