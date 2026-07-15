use super::*;

/// Infer the pointee `(size, align)` of a raw pointer parameter from its **use**,
/// when debug info is absent (kernel IR is built without it). A single-element gep
/// `gep %struct.T, ptr %param, 0, …` reveals that `%param` points at a `%struct.T`;
/// take the largest such aggregate (a union is accessed through its biggest member).
/// Only sees a use directly on the parameter (sound at `-O1`+, where the parameter is
/// not spilled to an alloca — kernel IR is `-O2`). Returns `None` if never so used.
pub(crate) fn infer_raw_ptr_pointee(f: &LFunc, param_name: &str) -> Option<(u64, u32)> {
    let mut best: Option<(u64, u32)> = None;
    for b in &f.blocks {
        for inst in &b.insts {
            // A struct/array field navigation whose leading index is 0 (one element)
            // and whose base is exactly this parameter.
            let LInst::GepChain { agg_ty, base, indices, .. } = inst else { continue };
            if !matches!(base, LValue::Local(n) if n == param_name) {
                continue;
            }
            if !matches!(indices.first(), Some(LValue::Int(0))) {
                continue;
            }
            let ty = lower_type(agg_ty);
            if let (Some(size), Some(align)) = (ty.size_bytes(&LAYOUT), ty.align_bytes(&LAYOUT)) {
                if size > 0 && best.is_none_or(|(bs, _)| size > bs) {
                    best = Some((size, align as u32));
                }
            }
        }
    }
    best
}

/// Lower a multi-level `getelementptr` into a `PtrOffset` chain by walking the
/// aggregate type through the index list. The leading index strides by
/// `sizeof(agg)`; a struct field or a *constant* array index folds into a running
/// byte offset; a *variable* array index emits its own scaled `PtrOffset`. The
/// running offset (possibly zero) is folded into `dst` at the end. A step that does
/// not fit the current type (a field index into a scalar, a variable struct field)
/// is refused, never mis-offset.
pub(crate) fn lower_gep_chain(
    ctx: &mut Ctx,
    dst: &str,
    agg: Type,
    base: &LValue,
    indices: &[LValue],
) -> Result<Vec<Inst>> {
    let const_idx = |v: &LValue| match v {
        LValue::Int(k) if *k >= 0 => u64::try_from(*k).ok(),
        _ => None,
    };
    let mut insts = Vec::new();
    // Leading index: pointer arithmetic over the whole aggregate.
    let mut cur = ctx.fresh();
    insts.push(Inst::PtrOffset {
        dst: cur,
        base: ctx.operand(base, 64)?,
        index: ctx.operand(&indices[0], 64)?,
        elem: agg.clone(),
    });
    let mut ty = agg;
    let mut acc: u64 = 0; // accumulated constant byte offset not yet emitted
    for idx in &indices[1..] {
        match ty {
            Type::Struct { ref fields, .. } => {
                let k = const_idx(idx)
                    .ok_or_else(|| Error::unsupported("variable struct-field gep index"))?;
                acc = acc
                    .checked_add(struct_field_offset(&ty, k as u32).ok_or_else(|| {
                        Error::unsupported("struct-field gep with an unsizable offset")
                    })?)
                    .ok_or_else(|| Error::unsupported("gep offset overflow"))?;
                ty = fields
                    .get(k as usize)
                    .cloned()
                    .ok_or_else(|| Error::unsupported("struct-field gep index out of range"))?;
            }
            Type::Array { elem, .. } => {
                match const_idx(idx) {
                    Some(k) => {
                        let sz = elem
                            .size_bytes(&LAYOUT)
                            .ok_or_else(|| Error::unsupported("array gep with an unsizable elem"))?;
                        acc = acc
                            .checked_add(k.saturating_mul(sz))
                            .ok_or_else(|| Error::unsupported("gep offset overflow"))?;
                    }
                    None => {
                        // Flush the pending constant offset, then a scaled step.
                        if acc > 0 {
                            let n = ctx.fresh();
                            insts.push(Inst::PtrOffset {
                                dst: n,
                                base: Operand::Reg(cur),
                                index: Operand::int(64, acc as u128),
                                elem: Type::int(8),
                            });
                            cur = n;
                            acc = 0;
                        }
                        let n = ctx.fresh();
                        insts.push(Inst::PtrOffset {
                            dst: n,
                            base: Operand::Reg(cur),
                            index: ctx.operand(idx, 64)?,
                            elem: (*elem).clone(),
                        });
                        cur = n;
                    }
                }
                ty = *elem;
            }
            _ => return Err(Error::unsupported("gep navigation into a non-aggregate")),
        }
    }
    // Fold the remaining constant offset (possibly zero) into the destination.
    insts.push(Inst::PtrOffset {
        dst: ctx.reg(dst)?,
        base: Operand::Reg(cur),
        index: Operand::int(64, acc as u128),
        elem: Type::int(8),
    });
    Ok(insts)
}

/// The padded byte offset of `field` inside struct type `s` (LP64 layout) —
/// the same alignment rule the IR's own `Type::Struct` sizing uses.
pub(crate) fn struct_field_offset(s: &Type, field: u32) -> Option<u64> {
    let Type::Struct { fields, packed } = s else { return None };
    let mut offset: u64 = 0;
    for (i, f) in fields.iter().enumerate() {
        let align = if *packed { 1 } else { f.align_bytes(&LAYOUT)?.max(1) };
        offset = offset.checked_add(align - 1)? / align * align;
        if i as u32 == field {
            return Some(offset);
        }
        offset = offset.checked_add(f.size_bytes(&LAYOUT)?)?;
    }
    None
}

pub(crate) fn inst_dst(inst: &LInst) -> Option<&str> {
    match inst {
        LInst::Alloca { dst, .. }
        | LInst::Load { dst, .. }
        | LInst::Gep { dst, .. }
        | LInst::Bin { dst, .. }
        | LInst::Icmp { dst, .. }
        | LInst::ExtractValue { dst, .. }
        | LInst::Opaque { dst, .. }
        | LInst::GepField { dst, .. }
        | LInst::GepChain { dst, .. }
        | LInst::AtomicRmw { dst, .. }
        | LInst::Select { dst, .. }
        | LInst::Cast { dst, .. } => Some(dst),
        LInst::Call { dst, .. } => dst.as_deref(),
        LInst::Store { .. } | LInst::Fence { .. } => None,
    }
}

pub(crate) fn lower_type(ty: &LType) -> Type {
    match ty {
        LType::Void => Type::Unit,
        // Compiler-annotation operands: zero-sized, never memory.
        LType::Metadata => Type::Unit,
        LType::Int(bits) => Type::int(*bits),
        LType::Ptr => Type::ptr(Type::Unit),
        // A vector is modelled by its byte footprint, like an array of the same
        // element count — enough for the access-size memory-safety reasoning.
        LType::Array(elem, n) | LType::Vector(elem, n) => Type::Array {
            elem: Box::new(lower_type(elem)),
            len: *n,
        },
        // A struct lowers structurally, so the IR layout machinery computes the
        // exact padded size/alignment — a `gep %"T", ptr, i64 N` strides by
        // `sizeof(T)`, and an under-sized placeholder would misplace every
        // subsequent access.
        LType::Struct(fields) => {
            Type::Struct { fields: fields.iter().map(lower_type).collect(), packed: false }
        }
        LType::PackedStruct(fields) => {
            Type::Struct { fields: fields.iter().map(lower_type).collect(), packed: true }
        }
        // Unreachable: the parser resolves every named reference or fails the
        // function. A total function is cheaper to keep correct than a panic; a
        // zero-size type can never *prove* an access in-bounds.
        LType::Named(_) => Type::Opaque { bytes: 0, align: 1 },
    }
}

/// The `(op, a, b)` of every checked-arithmetic tuple in `f`, keyed by the
/// intrinsic call's result register — so a later `extractvalue`, field 0, recovers
/// the arithmetic (field 1, the overflow flag, stays opaque).
pub(crate) fn checked_arith_map(f: &LFunc) -> HashMap<String, (BinOp, LValue, LValue)> {
    let mut m = HashMap::new();
    for b in &f.blocks {
        for inst in &b.insts {
            if let LInst::Call { dst: Some(dst), callee, args, .. } = inst {
                if let (Some(op), [a, b]) = (overflow_intrinsic_op(callee), args.as_slice()) {
                    m.insert(dst.clone(), (op, a.clone(), b.clone()));
                }
            }
        }
    }
    m
}

/// Map `llvm.{s,u}{add,sub,mul}.with.overflow.iN` to its arithmetic op (signed vs
/// unsigned is the same bitvector operation for memory-safety reasoning).
/// An integer min/max intrinsic (`llvm.umin`/`umax`/`smin`/`smax`) → the comparison whose
/// `select(a <cmp> b, a, b)` computes it, and the operand bit width from the `.iN` suffix.
/// `min = select(a < b, a, b)`, `max = select(a > b, a, b)`, unsigned or signed per the prefix.
pub(crate) fn minmax_intrinsic(callee: &str) -> Option<CmpOp> {
    let kind = callee.strip_prefix("llvm.")?;
    let name = kind.split('.').next()?;
    Some(match name {
        "umin" => CmpOp::Ult,
        "umax" => CmpOp::Ugt,
        "smin" => CmpOp::Slt,
        "smax" => CmpOp::Sgt,
        _ => return None,
    })
}

/// The operand bit width of an `.iN`-suffixed intrinsic (`llvm.umin.i32` → 32), defaulting to
/// 64 when the suffix is absent or unparseable (harmless for register operands).
pub(crate) fn intrinsic_width(callee: &str) -> u32 {
    callee
        .rsplit('.')
        .next()
        .and_then(|s| s.strip_prefix('i'))
        .and_then(|n| n.parse::<u32>().ok())
        .filter(|w| (1..=128).contains(w))
        .unwrap_or(64)
}

pub(crate) fn overflow_intrinsic_op(callee: &str) -> Option<BinOp> {
    let kind = callee.strip_prefix("llvm.")?;
    if !kind.contains(".with.overflow.") {
        return None;
    }
    Some(match kind.split('.').next()? {
        "sadd" | "uadd" => BinOp::Add,
        "ssub" | "usub" => BinOp::Sub,
        "smul" | "umul" => BinOp::Mul,
        _ => return None,
    })
}

/// Memory-effect-free intrinsics that are modelled as no-ops (they must not
/// invalidate the symbolic heap or region lifetimes the way an opaque call
/// does).
/// Recognize the bulk-memory intrinsics.
pub(crate) fn mem_kind(name: &str) -> Option<MemKind> {
    if name.starts_with("llvm.memcpy") {
        Some(MemKind::Copy)
    } else if name.starts_with("llvm.memmove") {
        Some(MemKind::Move)
    } else if name.starts_with("llvm.memset") {
        Some(MemKind::Set)
    } else {
        None
    }
}

pub(crate) fn is_noop_intrinsic(name: &str) -> bool {
    name.starts_with("llvm.lifetime.")
        || name.starts_with("llvm.dbg.")
        || name.starts_with("llvm.invariant.")
        || name.starts_with("llvm.expect")
        || name == "llvm.assume"
}
