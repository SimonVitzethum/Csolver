use super::*;

impl Ctx {
    pub(crate) fn fresh(&mut self) -> RegId {
        let r = RegId(self.next_temp);
        self.next_temp += 1;
        r
    }

    /// The stack-region pointer for an **address-taken** local `_n` of statically-known size:
    /// allocated once (an `Alloc` of `sizeof(type)` bytes) and cached, so every `&_n` yields the
    /// same region and `StorageDead(_n)` can end its lifetime. `None` for a local of unknown size,
    /// which stays opaque (as before) — no change to existing verdicts there.
    pub(crate) fn local_region(&mut self, n: u32, out: &mut Vec<Inst>) -> Option<RegId> {
        if let Some(&reg) = self.local_regions.get(&n) {
            return Some(reg);
        }
        let ir = mtype_to_ir(self.local_types.get(&n)?);
        let size = ir.size_bytes(&LAYOUT).filter(|&s| s > 0)?;
        let align = ir.align_bytes(&LAYOUT).unwrap_or(1).max(1) as u32;
        let reg = self.fresh();
        out.push(Inst::Alloc {
            dst: reg,
            region: RegionKind::Stack,
            elem: Type::int(8),
            count: IrOp::int(64, size as u128),
            align,
        });
        // We do not route the local's *value* through this region (its scalar value stays in the
        // SSA register), so seed the region as **initialised** with a symbolic value — otherwise a
        // read through `&_x` would be a false uninitialised-read. This is a sound over-approximation
        // (the pointee value is unknown), and it keeps the region's purpose: bounds + lifetime
        // (use-after-scope), not value tracking. A whole-object initialiser store covers any size.
        out.push(Inst::Store {
            ty: ir.clone(),
            ptr: IrOp::Reg(reg),
            value: IrOp::Const(Const::Undef),
            align,
            volatile: false,
        });
        self.local_regions.insert(n, reg);
        Some(reg)
    }

    /// A stable FieldPtr `field` id for a field path. A single-level path keeps its
    /// plain field index (so top-level field handling and round-trips are
    /// unchanged); a nested path gets a fresh id in the reserved high namespace, so
    /// each distinct path has its own disjoint synthetic offset.
    pub(crate) fn field_path_id(&mut self, path: &[u32]) -> u32 {
        if let [f] = path {
            return *f;
        }
        if let Some(&id) = self.field_path_ids.get(path) {
            return id;
        }
        let id = NESTED_FIELD_BASE + self.field_path_ids.len() as u32;
        self.field_path_ids.insert(path.to_vec(), id);
        id
    }

    pub(crate) fn lower_block(&mut self, b: &MBlock) -> Result<BasicBlock> {
        let mut insts = Vec::new();
        // Every instruction a statement emits inherits that statement's source
        // location (one MIR statement → possibly several MSIR insts, e.g. a
        // PtrOffset + a Load), so an obligation points back at the right line.
        let mut inst_spans: Vec<Option<String>> = Vec::new();
        for (s, span) in b.stmts.iter().zip(b.stmt_spans.iter()) {
            self.lower_stmt(s, &mut insts)?;
            inst_spans.resize(insts.len(), span.clone());
        }
        let term = self.lower_term(&b.term, &mut insts)?;
        inst_spans.resize(insts.len(), b.term_span.clone());
        let mut block = BasicBlock::new(BlockId(b.id as u32), term);
        block.insts = insts;
        block.inst_spans = inst_spans;
        Ok(block)
    }

    pub(crate) fn lower_stmt(&mut self, s: &MStmt, out: &mut Vec<Inst>) -> Result<()> {
        // A local's stack storage ending/beginning (use-after-scope). Only address-taken locals
        // have a modelled stack region (see `local_region`); for those, mark it freed on
        // `StorageDead` and re-live on `StorageLive` — a pointer dereferenced after the scope ends
        // is then a dangling deref (`NoUseAfterFree`), while a re-entered loop scope re-lives the
        // region (no false FAIL). A local with no region is a plain no-op.
        match s {
            MStmt::StorageDead(n) | MStmt::StorageLive(n) => {
                if let Some(&reg) = self.local_regions.get(n) {
                    let name = if matches!(s, MStmt::StorageDead(_)) {
                        "llvm.lifetime.end"
                    } else {
                        "llvm.lifetime.start"
                    };
                    out.push(Inst::Intrinsic { dst: None, name: name.into(), args: vec![IrOp::Reg(reg)] });
                }
                return Ok(());
            }
            MStmt::Nop => return Ok(()),
            MStmt::Assign(..) => {}
        }
        let MStmt::Assign(place, rv) = s else {
            return Ok(()); // unreachable (handled above)
        };
        match place {
            // Register destination: `_d = rvalue`.
            Place::Local(d) => {
                self.lower_rvalue_into(RegId(*d), rv, out)?;
                // A slice's length flows through pointer copies/borrows, so a
                // later `PtrMetadata`/`Len` of the copy still resolves to it
                // (rustc takes `_4 = &raw const (*_1); _5 = PtrMetadata(_4)`).
                self.propagate_slice_len(*d, rv);
                Ok(())
            }
            // Memory destination: `(*_p)[..] = …` / `*_p = …` / `(*_p).f = …`.
            // A *by-value* field write (`_3.0 = …`) is an opaque aggregate update
            // with no memory effect, so it is skipped soundly.
            Place::Deref(_) | Place::Index(_, _) | Place::ConstIndex(_, _) | Place::Field(_, _, _) => {
                if !is_memory_place(place) {
                    return Ok(());
                }
                let Rvalue::Use(op) = rv else {
                    // A non-`Use` store (e.g. a binop result written straight to
                    // memory) is rare in MIR; not modelled — skip soundly (the
                    // location keeps an unknown value).
                    return Ok(());
                };
                if let Some((ptr, elem)) = self.place_access(place, out) {
                    let value = self.operand_value(op, out);
                    out.push(Inst::Store {
                        ty: elem.clone(),
                        ptr: IrOp::Reg(ptr),
                        value,
                        align: elem.align_bytes(&LAYOUT).unwrap_or(1) as u32, volatile: false
                    });
                }
                Ok(())
            }
        }
    }

    /// Lower an rvalue, writing its value into register `dst`.
    pub(crate) fn lower_rvalue_into(&mut self, dst: RegId, rv: &Rvalue, out: &mut Vec<Inst>) -> Result<()> {
        match rv {
            Rvalue::Use(op) => {
                // A memory operand (`copy (*_1)[_2]`) is a load.
                if let Operand::Copy(p) | Operand::Move(p) = op {
                    if is_memory_place(p) {
                        if let Some((ptr, elem)) = self.place_access(p, out) {
                            out.push(Inst::Load {
                                dst,
                                ty: elem.clone(),
                                ptr: IrOp::Reg(ptr),
                                align: elem.align_bytes(&LAYOUT).unwrap_or(1) as u32, volatile: false
                            });
                        } else {
                            out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                        }
                        return Ok(());
                    }
                }
                let v = self.operand_value(op, out);
                out.push(assign(dst, RValue::Use(v)));
                Ok(())
            }
            // `ptr.offset(count)` / `ptr.add(count)` (MIR `Offset`): the result is
            // `base + count * size_of::<T>()`, keeping the base pointer's provenance.
            // Lower to a `PtrOffset` (stride = the pointee type) when the pointee is
            // known, so a later access through the result is bounds-checked against the
            // same region — instead of the opaque `Undef` a generic `Bin` would give.
            // Unknown pointee → fall back to opaque (sound: no wrong stride).
            Rvalue::Bin(BinKind::Offset, a, b) => {
                let base = self.operand_value(a, out);
                let index = self.operand_value(b, out);
                match Self::operand_local(a).and_then(|l| self.deref_elem(l)) {
                    Some(elem) => out.push(Inst::PtrOffset { dst, base, index, elem }),
                    None => out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef)))),
                }
                Ok(())
            }
            Rvalue::Bin(kind, a, b) => {
                let av = self.operand_value(a, out);
                let bv = self.operand_value(b, out);
                let value = match bin_rvalue(*kind, av, bv) {
                    Some(rv) => rv,
                    None => RValue::Use(IrOp::Const(Const::Undef)),
                };
                out.push(assign(dst, value));
                Ok(())
            }
            // Checked arithmetic produces a `(result, overflow)` tuple. Compute
            // the result into a fresh register and remember it as the tuple's
            // `.0`, so a later `move (_k.0)` recovers the actual value (e.g. the
            // `n - 1` of a checked subtraction) — the `.1` overflow flag stays
            // opaque (it only feeds the overflow `assert`).
            Rvalue::CheckedBin(kind, a, b) => {
                let av = self.operand_value(a, out);
                let bv = self.operand_value(b, out);
                if let Some(rv) = bin_rvalue(*kind, av, bv) {
                    let tmp = self.fresh();
                    out.push(assign(tmp, rv));
                    self.checked_arith.insert(dst.0, IrOp::Reg(tmp));
                }
                Ok(())
            }
            Rvalue::Len(place) => {
                // `Len(&[T; N])` is the constant `N`; `Len(&[T])` is the slice's
                // synthetic length parameter.
                let value = if let Some(n) = self.array_len(place) {
                    IrOp::int(64, n as u128)
                } else if let Some(len) = place_base_local(place).and_then(|l| self.slice_len.get(&l))
                {
                    IrOp::Reg(*len)
                } else {
                    IrOp::Const(Const::Undef)
                };
                out.push(assign(dst, RValue::Use(value)));
                Ok(())
            }
            Rvalue::Ref(place, kind) => {
                // `&(*_p)[i]` is the element address; `&(*_p)` is the pointer
                // itself; other refs (a stack local's address) are opaque.
                match place {
                    // `&(*_p)[i]` is the element address; `&((*_p).f)` /
                    // `&(((*_p) as V).f)` is a struct/enum-variant field address —
                    // both lower to the access pointer.
                    Place::Index(_, _) | Place::ConstIndex(_, _) => {
                        if let Some((ptr, _)) = self.place_access(place, out) {
                            out.push(assign(dst, RValue::Use(IrOp::Reg(ptr))));
                        } else {
                            out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                        }
                    }
                    Place::Field(_, _, _) if is_memory_place(place) => {
                        if let Some((ptr, _)) = self.place_access(place, out) {
                            out.push(assign(dst, RValue::Use(IrOp::Reg(ptr))));
                        } else {
                            out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                        }
                    }
                    Place::Deref(inner) => {
                        if let Place::Local(p) = inner.as_ref() {
                            out.push(assign(dst, RValue::Use(IrOp::Reg(RegId(*p)))));
                        } else {
                            out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                        }
                    }
                    // `&_x` / `&mut _x` — the address of a stack local. For a local of
                    // statically-known size, model it as a stack region (so accesses through it
                    // are bounds-checked, and `StorageDead(_x)` ends its scope — use-after-scope);
                    // an unknown-size local stays opaque, as before.
                    Place::Local(n) => match self.local_region(*n, out) {
                        Some(reg) => out.push(assign(dst, RValue::Use(IrOp::Reg(reg)))),
                        None => out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef)))),
                    },
                    _ => out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef)))),
                }
                // A `&mut *_p` / `&(*_p)` reborrow through a pointer local emits a **retag**
                // marker AFTER the value is set: `dst` is a new borrow derived from `_p`, so the
                // opt-in borrow-stack can invalidate a sibling `&mut` (a mutable reborrow) or
                // detect a read through a shared borrow a later `&mut` write invalidated. A no-op
                // unless `--aliasing-model` is on (the executor ignores the marker otherwise).
                let retag_name = match kind {
                    RefKind::Mut => Some("csolver.retag.mut"),
                    RefKind::Shared => Some("csolver.retag.shared"),
                    RefKind::Opaque => None,
                };
                if let Some(name) = retag_name {
                    if let Place::Deref(inner) = place {
                        if let Place::Local(p) = inner.as_ref() {
                            // Suppress the retag when `_p` points to an interior-mutable type
                            // (`&UnsafeCell`/`&Cell`/`&Mutex`/…): interior mutability writes
                            // through a shared reference, so tracking such a borrow could false-FAIL.
                            let interior = matches!(
                                self.local_types.get(p),
                                Some(MType::Ref(inner, _) | MType::Ptr(inner, _)) if matches!(inner.as_ref(), MType::InteriorMut)
                            );
                            if !interior {
                                out.push(Inst::Intrinsic {
                                    dst: None,
                                    name: name.into(),
                                    args: vec![IrOp::Reg(dst), IrOp::Reg(RegId(*p))],
                                });
                            }
                        }
                    }
                }
                Ok(())
            }
            // A cast keeps the value (width changes are abstracted); an unmodelled
            // rvalue yields a fresh unknown.
            Rvalue::Cast(op) => {
                let v = self.operand_value(op, out);
                out.push(assign(dst, RValue::Use(v)));
                Ok(())
            }
            Rvalue::Discriminant(place) => {
                // The discriminant value is opaque (so a following `switchInt`
                // soundly explores every arm), but reading it through a pointer is
                // a real memory access: emit a one-byte read at the base of the
                // enum so an invalid enum reference is caught (in bounds by
                // construction, like a field). A by-value enum needs no access.
                if is_memory_place(place) {
                    if let Some(p) = place_base_local(place) {
                        let ptr = self.fresh();
                        out.push(Inst::FieldPtr {
                            dst: ptr,
                            base: IrOp::Reg(RegId(p)),
                            field: 0,
                            size: 1,
                            align: 1,
                        });
                        let val = self.fresh();
                        out.push(Inst::Load {
                            dst: val,
                            ty: Type::int(8),
                            ptr: IrOp::Reg(ptr),
                            align: 1, volatile: false
                        });
                    }
                }
                out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                Ok(())
            }
            Rvalue::Other => {
                out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                Ok(())
            }
        }
    }

    /// The terminator after a call/drop, given its normal-return and
    /// unwind-cleanup targets. Both present → a two-way branch on a *fresh
    /// unconstrained* condition, so both the normal successor and the cleanup
    /// block are explored (the cleanup runs on the panic path; its memory ops —
    /// drops and writes — must be checked, not silently left undecided). The
    /// cleanup edge sees the post-call state (the call's conservative havoc), a
    /// sound over-approximation of the partially-unwound state. Mirrors the LLVM
    /// `invoke` lowering.
    pub(crate) fn call_edges(&mut self, target: Option<usize>, unwind: Option<usize>) -> Terminator {
        match (target, unwind) {
            (Some(t), Some(u)) => Terminator::CondBr {
                cond: IrOp::Reg(self.fresh()),
                then_blk: BlockId(t as u32),
                then_args: vec![],
                else_blk: BlockId(u as u32),
                else_args: vec![],
            },
            (Some(t), None) => Terminator::Br { target: BlockId(t as u32), args: vec![] },
            (None, Some(u)) => Terminator::Br { target: BlockId(u as u32), args: vec![] },
            (None, None) => Terminator::Unreachable,
        }
    }
}
