use super::*;

impl Ctx {
    pub(crate) fn lower_term(&mut self, t: &MTerm, out: &mut Vec<Inst>) -> Result<Terminator> {
        Ok(match t {
            MTerm::Return => Terminator::Return(None),
            MTerm::Goto(n) => Terminator::Br { target: BlockId(*n as u32), args: vec![] },
            MTerm::Unreachable => Terminator::Unreachable,
            MTerm::Assert { cond, expected, target } => {
                self.panic_used = true;
                let c = self.operand_value(cond, out);
                let cont = BlockId(*target as u32);
                let panic = BlockId(self.panic_id);
                let (then_blk, else_blk) = if *expected { (cont, panic) } else { (panic, cont) };
                Terminator::CondBr {
                    cond: c,
                    then_blk,
                    then_args: vec![],
                    else_blk,
                    else_args: vec![],
                }
            }
            MTerm::Call { dst, callee, args, target, unwind } => {
                // A call is an MSIR *instruction* followed by an edge to the
                // return block (or divergence if the call cannot return). The
                // verifier applies a known function's summary or havocs an
                // unknown/external one — both sound.
                let ir_dst = match dst {
                    Place::Local(d) => Some(RegId(*d)),
                    _ => None,
                };
                let ir_callee = match callee {
                    CalleeSpec::Named(n) if !n.is_empty() => match self.func_ids.get(n) {
                        Some(fid) => Callee::Direct(*fid),
                        None => Callee::Symbol(n.clone()),
                    },
                    CalleeSpec::Named(_) => Callee::Symbol(String::new()),
                    CalleeSpec::Indirect(local) => Callee::Indirect(IrOp::Reg(RegId(*local))),
                };
                let ir_args = args.iter().map(|a| self.operand_value(a, out)).collect();
                // The result type is the destination local's declared type — so a
                // call returning a reference (`Index::index` → `&T`, an internal fn
                // returning `&_`) yields a *pointer*, not a scalar the engine would
                // have to treat as an opaque address. A non-`Local` dst keeps the
                // scalar default (its value is unused for memory reasoning).
                let ret_ty = match dst {
                    Place::Local(d) => {
                        self.local_types.get(d).map(mtype_to_ir).unwrap_or_else(|| Type::int(64))
                    }
                    _ => Type::int(64),
                };
                // A call returning `&T`/`&mut T` yields a *valid reference* by
                // Rust's type invariant (the callee — even external — cannot
                // return a dangling reference in safe code). Absent a precise
                // summary, the engine materialises it as a valid-reference
                // region instead of an opaque pointer. Raw pointers are excluded
                // (not guaranteed valid).
                let ret_ref = match dst {
                    Place::Local(d) => match self.local_types.get(d) {
                        Some(MType::Ref(inner, mutable)) => Some(RefResult {
                            size: pointee_size(inner),
                            writable: *mutable,
                        }),
                        _ => None,
                    },
                    _ => None,
                };
                // `core::intrinsics::copy_nonoverlapping` / `copy` / `write_bytes` (the
                // primitives behind `ptr::copy*`, `slice::copy_from_slice`, `write_bytes`):
                // model as a bounds-/liveness-checked `MemIntrinsic` instead of an opaque
                // call that would silently drop the effect. `copy_nonoverlapping` is `Copy`,
                // so it additionally gets the source/destination **overlap** obligation — the
                // concrete Rust aliasing UB (`copy_nonoverlapping` with overlapping ranges).
                if let CalleeSpec::Named(n) = callee {
                    if let Some(mi) = self.mem_intrinsic_for(n, args, out) {
                        out.push(mi);
                        return Ok(self.call_edges(*target, *unwind));
                    }
                }
                out.push(Inst::Call {
                    dst: ir_dst,
                    callee: ir_callee,
                    args: ir_args,
                    ret_ty,
                    ret_ref,
                });
                self.call_edges(*target, *unwind)
            }
            MTerm::SwitchInt(op, cases, otherwise) => {
                let value = self.operand_value(op, out);
                // A two-way `[0: f, otherwise: t]` is a boolean branch.
                if let [(0, false_bb)] = cases[..] {
                    Terminator::CondBr {
                        cond: value,
                        then_blk: BlockId(*otherwise as u32),
                        then_args: vec![],
                        else_blk: BlockId(false_bb as u32),
                        else_args: vec![],
                    }
                } else {
                    let cases = cases
                        .iter()
                        .map(|(v, bb)| {
                            (csolver_core::BitVector::new(64, *v as u128), BlockId(*bb as u32))
                        })
                        .collect();
                    Terminator::Switch { value, cases, default: BlockId(*otherwise as u32) }
                }
            }
            MTerm::Drop { target, unwind } => {
                // A drop runs the value's destructor, which may free what the value
                // owns (a `Vec`/`Box` buffer, or a raw pointer a custom `Drop`
                // frees). Model it as a freeing call: an unknown `Symbol` callee,
                // which the verifier treats as possibly-freeing — it invalidates
                // every owned region's liveness and the heap, so a later use of a
                // freed owned region is not a false PASS. Borrowed (contracted)
                // regions survive, since a destructor cannot free a borrow. Then
                // branch to the return block.
                out.push(Inst::Call {
                    dst: None,
                    callee: Callee::Symbol("drop".into()),
                    args: vec![],
                    ret_ty: Type::Unit,
                    ret_ref: None,
                });
                self.call_edges(*target, *unwind)
            }
            MTerm::Unsupported => {
                return Err(Error::unsupported("MIR terminator outside the modelled subset"))
            }
        })
    }

    /// Materialise an operand as an MSIR scalar operand (loading a memory place
    /// into a fresh register if needed).
    /// If `p` is a *by-value* field projection whose innermost ascribed type is
    /// a reference (`&T`/`&mut T` — e.g. `(_6 as Some).0` of type `&u8`,
    /// extracted from an aggregate the analysis cannot see into), materialise it
    /// as a valid reference: Rust guarantees the value is a live, correctly-sized
    /// reference regardless of where the aggregate came from. Returns the
    /// pointer register, or `None` (the caller falls back to `undef`) for a
    /// non-reference field or a raw-pointer field (`*const T` is not guaranteed
    /// valid). A slice/unsized pointee has unknown size → an opaque region.
    pub(crate) fn ref_witness_for(&mut self, p: &Place, out: &mut Vec<Inst>) -> Option<IrOp> {
        if is_memory_place(p) {
            return None; // a field *through a pointer* is a real load, not this.
        }
        let Place::Field(_, _, Some(MType::Ref(inner, mutable))) = p else {
            return None;
        };
        let (size, align) = match pointee_size(inner) {
            Some(n) => (Some(n), pointee_align(inner)),
            None => (None, 1),
        };
        let dst = self.fresh();
        out.push(Inst::RefWitness { dst, size, align, writable: *mutable, assumed: false, src: None });
        Some(IrOp::Reg(dst))
    }

    pub(crate) fn operand_value(&mut self, op: &Operand, out: &mut Vec<Inst>) -> IrOp {
        match op {
            Operand::Const(MConst::Int(n)) => IrOp::int(64, *n as u128),
            Operand::Const(MConst::Bool(b)) => IrOp::int(1, *b as u128),
            Operand::Copy(p) | Operand::Move(p) => match p {
                Place::Local(n) => IrOp::Reg(RegId(*n)),
                // Field `.0` of a checked-arithmetic tuple (a by-value local) is
                // its result value. A field *through a pointer* (`(*_1).0`) is a
                // memory place and is loaded by the arm below instead.
                Place::Field(inner, 0, _) if matches!(inner.as_ref(), Place::Local(_)) => {
                    match inner.as_ref() {
                        Place::Local(k) => self.checked_arith.get(k).cloned().unwrap_or_else(|| {
                            // `.0` of a by-value fat pointer (`&[T]`) is its data
                            // pointer — which CSolver already models as the region
                            // pointer held in `_k`. Read it back (keeping the
                            // contracted region's provenance) instead of dropping it
                            // to undef.
                            if self.is_fat_ref(*k) {
                                IrOp::Reg(RegId(*k))
                            } else {
                                self.ref_witness_for(p, out)
                                    .unwrap_or(IrOp::Const(Const::Undef))
                            }
                        }),
                        _ => IrOp::Const(Const::Undef),
                    }
                }
                _ if is_memory_place(p) => {
                    if let Some((ptr, elem)) = self.place_access(p, out) {
                        let dst = self.fresh();
                        out.push(Inst::Load {
                            dst,
                            ty: elem.clone(),
                            ptr: IrOp::Reg(ptr),
                            align: elem.align_bytes(&LAYOUT).unwrap_or(1) as u32, volatile: false
                        });
                        IrOp::Reg(dst)
                    } else {
                        IrOp::Const(Const::Undef)
                    }
                }
                _ => self.ref_witness_for(p, out).unwrap_or(IrOp::Const(Const::Undef)),
            },
        }
    }

    /// Emit the pointer to a memory `place` and return `(pointer reg, elem type)`.
    /// Resolve the base pointer and element type for an index projection
    /// `base[..]` — shared by the runtime-`Index` and constant-`ConstIndex`
    /// arms. `base` is either `*_p` (the array/slice behind a pointer) or an
    /// outer index/field yielding a pointer-to-array.
    pub(crate) fn index_base(&mut self, base: &Place, out: &mut Vec<Inst>) -> Option<(IrOp, Type)> {
        match base {
            Place::Deref(inner) => match inner.as_ref() {
                Place::Local(p) => {
                    Some((IrOp::Reg(RegId(*p)), self.index_elem(*p).unwrap_or_else(|| Type::int(8))))
                }
                _ => {
                    self.lowering_failed = true;
                    None
                }
            },
            Place::Index(_, _) | Place::ConstIndex(_, _) | Place::Field(_, _, _) => {
                let (inner_ptr, inner_ty) = self.place_access(base, out)?;
                match array_elem(&inner_ty) {
                    Some(elem) => Some((IrOp::Reg(inner_ptr), elem)),
                    None => {
                        self.lowering_failed = true;
                        None
                    }
                }
            }
            _ => {
                self.lowering_failed = true;
                None
            }
        }
    }

    pub(crate) fn place_access(&mut self, place: &Place, out: &mut Vec<Inst>) -> Option<(RegId, Type)> {
        match place {
            // `base[i]`: a pointer to element 0 of the array/slice `base` denotes,
            // offset by `i` (stride = element size). `base` is either `*_p` (the
            // slice/array behind a pointer) or an *outer* index, so nested indices
            // `(*_p)[i][j]` chain — the inner index yields a pointer to an inner
            // array, which this level indexes again. The strides come from the
            // array element types, which are unambiguous (no struct-layout needed).
            Place::Index(base, idx) => {
                let (base_ptr, elem) = self.index_base(base, out)?;
                let dst = self.fresh();
                out.push(Inst::PtrOffset {
                    dst,
                    base: base_ptr,
                    index: IrOp::Reg(RegId(*idx)),
                    elem: elem.clone(),
                });
                Some((dst, elem))
            }
            // `base[N of M]` — a constant element index (same base resolution as
            // `Index`, but the offset is the compile-time constant `N`).
            Place::ConstIndex(base, n) => {
                let (base_ptr, elem) = self.index_base(base, out)?;
                let dst = self.fresh();
                out.push(Inst::PtrOffset {
                    dst,
                    base: base_ptr,
                    index: IrOp::int(64, *n as u128),
                    elem: elem.clone(),
                });
                Some((dst, elem))
            }
            // `*_p`: the pointer is `_p`; the access is at offset 0.
            Place::Deref(inner) => match inner.as_ref() {
                Place::Local(p) => {
                    let elem = self.deref_elem(*p).unwrap_or_else(|| Type::int(8));
                    Some((RegId(*p), elem))
                }
                _ => {
                    self.lowering_failed = true;
                    None
                }
            },
            // `(*_p).f`: a field of the struct behind pointer `_p`. The field's
            // type (from the MIR ascription) gives its size and alignment; the
            // engine proves the access in bounds by construction, so no struct
            // byte-layout is needed (it is absent from MIR anyway).
            // `(*p).f` and nested `((*p).f0).f1` both denote a field that lies
            // within the referent of `p` by construction. Walk the whole field
            // path down to a `Deref(Local p)` base and emit one FieldPtr keyed on a
            // unique id for that path, so a nested field gets its own disjoint
            // synthetic offset — in bounds and aligned by construction, and never
            // aliasing a sibling or top-level field. The innermost field's type
            // ascription gives its size and alignment.
            Place::Field(_, _, fty) => {
                if let Some((p, path)) = deref_field_path(place) {
                    let elem = fty.as_ref().map(mtype_to_ir).unwrap_or_else(|| Type::int(8));
                    let size = elem.size_bytes(&LAYOUT).unwrap_or(1).max(1);
                    let align = elem.align_bytes(&LAYOUT).unwrap_or(1).max(1);
                    let id = self.field_path_id(&path);
                    let dst = self.fresh();
                    out.push(Inst::FieldPtr {
                        dst,
                        base: IrOp::Reg(RegId(p)),
                        field: id,
                        size,
                        align,
                    });
                    Some((dst, elem))
                } else {
                    self.lowering_failed = true;
                    None
                }
            }
            _ => {
                self.lowering_failed = true;
                None
            }
        }
    }

    /// Carry a slice's synthetic length to `dst` when the rvalue copies or
    /// borrows a slice pointer (`dst = move _p`, `dst = &(*_p)`, a pointer cast).
    pub(crate) fn propagate_slice_len(&mut self, dst: u32, rv: &Rvalue) {
        let src = match rv {
            Rvalue::Use(Operand::Copy(Place::Local(p)) | Operand::Move(Place::Local(p)))
            | Rvalue::Cast(Operand::Copy(Place::Local(p)) | Operand::Move(Place::Local(p))) => Some(*p),
            Rvalue::Ref(Place::Deref(inner), _) => match inner.as_ref() {
                Place::Local(p) => Some(*p),
                _ => None,
            },
            _ => None,
        };
        if let Some(len) = src.and_then(|p| self.slice_len.get(&p).copied()) {
            self.slice_len.insert(dst, len);
        }
    }

    /// The element type for indexing through local `p` (an `&[T; N]`/`&[T]`).
    pub(crate) fn index_elem(&self, p: u32) -> Option<Type> {
        match self.local_types.get(&p)? {
            MType::Ref(inner, _) | MType::Ptr(inner, _) => match inner.as_ref() {
                MType::Array(e, _) | MType::Slice(e) => Some(mtype_to_ir(e)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether local `p` is a fat-pointer reference (`&[T]`/`&mut [T]`) — so its
    /// `.0` projection is a data pointer into a contracted region, not opaque.
    pub(crate) fn is_fat_ref(&self, p: u32) -> bool {
        matches!(
            self.local_types.get(&p),
            Some(MType::Ref(inner, _) | MType::Ptr(inner, _)) if matches!(inner.as_ref(), MType::Slice(_))
        )
    }

    /// The pointee type for dereferencing local `p` (an `&T`/`*T`).
    pub(crate) fn deref_elem(&self, p: u32) -> Option<Type> {
        match self.local_types.get(&p)? {
            MType::Ref(inner, _) | MType::Ptr(inner, _) => Some(mtype_to_ir(inner)),
            _ => None,
        }
    }

    /// The local id an operand copies/moves from (`None` for a constant).
    pub(crate) fn operand_local(op: &Operand) -> Option<u32> {
        match op {
            Operand::Copy(Place::Local(n)) | Operand::Move(Place::Local(n)) => Some(*n),
            _ => None,
        }
    }

    /// Recognise a `core::intrinsics` bulk-memory primitive and build its modelling
    /// [`Inst::MemIntrinsic`]. `copy_nonoverlapping(src, dst, count)` → `Copy` (which
    /// additionally carries the source/destination overlap obligation — the concrete
    /// Rust aliasing UB), `copy(src, dst, count)` → `Move` (overlap allowed),
    /// `write_bytes(dst, val, count)` → `Set`. The byte length is `count *
    /// size_of::<T>()`, `T` recovered from the pointer argument's pointee type; if the
    /// element size is unknown, returns `None` (the caller emits the generic call).
    fn mem_intrinsic_for(&mut self, name: &str, args: &[Operand], out: &mut Vec<Inst>) -> Option<Inst> {
        // (kind, dst arg index, src arg index or None, count arg index, pointer arg for elem size)
        let (kind, dst_i, src_i, count_i, ptr_i) = match name {
            "copy_nonoverlapping" => (MemKind::Copy, 1usize, Some(0usize), 2usize, 0usize),
            "copy" => (MemKind::Move, 1, Some(0), 2, 0),
            "write_bytes" => (MemKind::Set, 0, None, 2, 0),
            _ => return None,
        };
        if args.len() <= dst_i.max(count_i).max(ptr_i) {
            return None;
        }
        // Element size from the pointer argument's pointee (`*const T`/`*mut T`).
        let elem = Self::operand_local(&args[ptr_i]).and_then(|p| self.deref_elem(p))?;
        let size = elem.size_bytes(&LAYOUT).filter(|&s| s > 0)?;
        // len = count * size_of::<T>() (bytes); no multiply when the element is a byte.
        let count = self.operand_value(&args[count_i], out);
        let len = if size == 1 {
            count
        } else {
            let tmp = self.fresh();
            out.push(Inst::Assign {
                dst: tmp,
                ty: Type::int(64),
                value: RValue::Bin { op: BinOp::Mul, lhs: count, rhs: IrOp::int(64, size as u128), flags: Default::default() },
            });
            IrOp::Reg(tmp)
        };
        let dst = self.operand_value(&args[dst_i], out);
        let src = src_i.map(|i| self.operand_value(&args[i], out));
        Some(Inst::MemIntrinsic { kind, dst, src, len })
    }

    /// The constant length `N` of the array `place` refers to (`&[T; N]`).
    pub(crate) fn array_len(&self, place: &Place) -> Option<u64> {
        let local = match place {
            Place::Deref(inner) => match inner.as_ref() {
                Place::Local(p) => *p,
                _ => return None,
            },
            Place::Local(p) => *p,
            _ => return None,
        };
        match self.local_types.get(&local)? {
            MType::Ref(inner, _) | MType::Ptr(inner, _) => match inner.as_ref() {
                MType::Array(_, n) => Some(*n),
                _ => None,
            },
            MType::Array(_, n) => Some(*n),
            _ => None,
        }
    }
}
