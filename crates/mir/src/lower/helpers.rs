use super::*;

pub(crate) fn assign(dst: RegId, value: RValue) -> Inst {
    Inst::Assign { dst, ty: Type::int(64), value }
}

/// Map a MIR binary op to an MSIR rvalue (`None` ⇒ unmodelled, opaque result).
/// Comparisons are unsigned — the index/length bounds checks that motivate the
/// MIR frontend are over `usize`.
pub(crate) fn bin_rvalue(kind: BinKind, lhs: IrOp, rhs: IrOp) -> Option<RValue> {
    let cmp = |op| Some(RValue::Cmp { op, lhs: lhs.clone(), rhs: rhs.clone() });
    let bin = |op| Some(RValue::Bin { op, lhs: lhs.clone(), rhs: rhs.clone() , flags: Default::default() });
    match kind {
        BinKind::Lt => cmp(CmpOp::Ult),
        BinKind::Le => cmp(CmpOp::Ule),
        BinKind::Gt => cmp(CmpOp::Ugt),
        BinKind::Ge => cmp(CmpOp::Uge),
        BinKind::Eq => cmp(CmpOp::Eq),
        BinKind::Ne => cmp(CmpOp::Ne),
        BinKind::Add => bin(BinOp::Add),
        BinKind::Sub => bin(BinOp::Sub),
        BinKind::Mul => bin(BinOp::Mul),
        BinKind::BitAnd => bin(BinOp::And),
        BinKind::BitOr => bin(BinOp::Or),
        BinKind::BitXor => bin(BinOp::Xor),
        // `Offset` is pointer arithmetic (a `PtrOffset` inst, handled in `stmt.rs`), not
        // a value `RValue`; a `CheckedBin`/other context has no pointee type so it stays opaque.
        BinKind::Offset | BinKind::Other => None,
    }
}

/// Whether a place denotes a memory access — its projection chain reaches a
/// deref or index. A field of a plain local (`_11.0`, a tuple value) is *not*
/// memory; a field reached through a pointer (`(*_1).0`) *is* (and, lacking
/// struct layout, is rejected rather than silently dropped).
pub(crate) fn is_memory_place(p: &Place) -> bool {
    match p {
        Place::Local(_) => false,
        Place::Deref(_) => true,
        // An index/field is a memory access only if its base ultimately derefs a
        // pointer: `(*_p)[i]` and `(*_p).f[i]` are memory, but indexing a by-value
        // local array (`_l[i]`, `_l.0[i]`) is a bounds-checked stack value, not a
        // heap access — modelled opaquely, with no memory obligation.
        Place::ConstIndex(base, _) | Place::Index(base, _) | Place::Field(base, _, _) => {
            is_memory_place(base)
        }
    }
}

/// The local a place is rooted at, peeling every projection.
pub(crate) fn place_base_local(p: &Place) -> Option<u32> {
    match p {
        Place::Local(n) => Some(*n),
        Place::Deref(inner)
        | Place::Field(inner, _, _)
        | Place::Index(inner, _)
        | Place::ConstIndex(inner, _) => place_base_local(inner),
    }
}

/// The locals a block mentions (params plus any `_N` in index/assign positions),
/// used only to size the temporary-register counter.
pub(crate) fn block_locals(b: &MBlock) -> Vec<u32> {
    let mut out = Vec::new();
    let visit_place = |p: &Place, out: &mut Vec<u32>| {
        let mut cur = p;
        loop {
            match cur {
                Place::Local(n) => {
                    out.push(*n);
                    break;
                }
                Place::Deref(inner) | Place::Field(inner, _, _) | Place::ConstIndex(inner, _) => {
                    cur = inner
                }
                Place::Index(inner, idx) => {
                    out.push(*idx);
                    cur = inner;
                }
            }
        }
    };
    for s in &b.stmts {
        if let MStmt::Assign(p, _) = s {
            visit_place(p, &mut out);
        }
    }
    out
}

/// Convert a MIR type to an MSIR type.
/// Walk a (possibly nested) field place down to a `(*_p)` base, returning the
/// pointer local and the field path, outer-to-inner (`[0, 1]` for `((*p).0).1`).
/// `None` if the base is not a deref of a local — a field of a by-value local, or
/// through an index, has no single pointer to offset from.
pub(crate) fn deref_field_path(place: &Place) -> Option<(u32, Vec<u32>)> {
    let mut fields = Vec::new();
    let mut cur = place;
    loop {
        match cur {
            Place::Field(base, f, _) => {
                fields.push(*f);
                cur = base;
            }
            Place::Deref(inner) => {
                return match inner.as_ref() {
                    Place::Local(p) => {
                        fields.reverse();
                        Some((*p, fields))
                    }
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// The element type of an array `Type`, for chaining a nested index.
pub(crate) fn array_elem(ty: &Type) -> Option<Type> {
    match ty {
        Type::Array { elem, .. } => Some((**elem).clone()),
        _ => None,
    }
}

pub(crate) fn mtype_to_ir(mty: &MType) -> Type {
    match mty {
        MType::Int { width, .. } => Type::int(*width),
        MType::Bool => Type::Bool,
        MType::Unit | MType::Other | MType::InteriorMut => Type::Unit,
        MType::Ref(inner, _) | MType::Ptr(inner, _) => Type::ptr(mtype_to_ir(inner)),
        MType::Array(elem, n) => Type::Array { elem: Box::new(mtype_to_ir(elem)), len: *n },
        // A bare slice is never a value type here; only its element is used.
        MType::Slice(elem) => mtype_to_ir(elem),
    }
}

/// The byte size of a reference's pointee, when statically known.
pub(crate) fn pointee_size(pointee: &MType) -> Option<u64> {
    mtype_to_ir(pointee).size_bytes(&LAYOUT).filter(|&s| s > 0)
}

pub(crate) fn pointee_align(pointee: &MType) -> u32 {
    mtype_to_ir(pointee).align_bytes(&LAYOUT).unwrap_or(1) as u32
}
