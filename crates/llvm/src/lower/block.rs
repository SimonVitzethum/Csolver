use super::*;

pub(crate) fn lower_block(ctx: &mut Ctx, b: &LBlock, id: BlockId) -> Result<BasicBlock> {
    let block_params: Vec<(RegId, Type)> = b
        .phis
        .iter()
        .map(|phi| Ok((ctx.reg(&phi.dst)?, lower_type(&phi.ty))))
        .collect::<Result<_>>()?;

    let mut insts = Vec::new();
    for inst in &b.insts {
        // An atomic RMW is, at this abstraction, a load (the returned old
        // value — kept only for `atomicrmw`; cmpxchg's tuple stays opaque) plus
        // a store of an unknown value. Both accesses carry their full memory
        // obligations; an opaque placeholder would silently drop them (an
        // unchecked OOB atomicrmw would be a false PASS one level up).
        if let LInst::AtomicRmw { dst, ty, ptr, tuple } = inst {
            let msir_ty = lower_type(ty);
            let align = msir_ty.align_bytes(&LAYOUT).unwrap_or(1) as u32;
            let old_dst = if *tuple { ctx.fresh() } else { ctx.reg(dst)? };
            insts.push(Inst::Load {
                dst: old_dst,
                ty: msir_ty.clone(),
                ptr: ctx.operand(ptr, 64)?,
                align,
                volatile: true, // an atomic RMW is race-free
            });
            insts.push(Inst::Store {
                ty: msir_ty,
                ptr: ctx.operand(ptr, 64)?,
                value: Operand::Const(Const::Undef),
                align,
                volatile: true,
            });
            if *tuple {
                insts.push(Inst::Assign {
                    dst: ctx.reg(dst)?,
                    ty: Type::int(64),
                    value: RValue::Use(Operand::Const(Const::Undef)),
                });
            }
            continue;
        }
        // A struct-field gep expands to a two-step chain: element stride, then
        // the exact padded field offset (needs a fresh intermediate register,
        // hence handled here rather than in the single-instruction lowering).
        if let LInst::GepField { dst, struct_ty, base, index, field } = inst {
            let s_ty = lower_type(struct_ty);
            let off = struct_field_offset(&s_ty, *field).ok_or_else(|| {
                Error::unsupported("struct-field gep with an unsizable field offset")
            })?;
            let tmp = ctx.fresh();
            insts.push(Inst::PtrOffset {
                dst: tmp,
                base: ctx.operand(base, 64)?,
                index: ctx.operand(index, 64)?,
                elem: s_ty,
            });
            insts.push(Inst::PtrOffset {
                dst: ctx.reg(dst)?,
                base: Operand::Reg(tmp),
                index: Operand::int(64, off as u128),
                elem: Type::int(8),
            });
            continue;
        }
        // A multi-level gep: walk the aggregate type through the index list,
        // emitting a PtrOffset chain — the leading index strides by `sizeof(agg)`,
        // a struct field or a constant array index folds into a byte offset, and a
        // *variable* array index emits its own scaled PtrOffset.
        if let LInst::GepChain { dst, agg_ty, base, indices, .. } = inst {
            let out = lower_gep_chain(ctx, dst, lower_type(agg_ty), base, indices)?;
            insts.extend(out);
            continue;
        }
        // An **atomic load-acquire / store-release** (inlined `smp_load_acquire` /
        // `smp_store_release`, or any `load atomic acquire` / `store atomic release` /
        // `seq_cst`): the ordering the acquire/release guarantees is emitted as the
        // matching weak-memory barrier, so the message-passing idiom is seen as ordered
        // and the weak-memory pass does not falsely flag a missing barrier. A **release**
        // orders prior stores before the store (a write barrier *before* it); an
        // **acquire** orders later loads after the load (a read barrier *after* it);
        // `seq_cst`/`acq_rel` is a full barrier. (`Inst::Barrier` kind: 0 full, 1 write,
        // 2 read — see `crates/contracts`.) The load/store itself is emitted as usual, so
        // its memory-safety obligations are unchanged; only the fence is added.
        match inst {
            LInst::Store { ordering: ord @ (LOrdering::Release | LOrdering::AcqRel | LOrdering::SeqCst), .. } => {
                // The real store follows and records the flag access, so the fence itself
                // carries no access (`None`) — otherwise the location would be double-counted.
                insts.push(Inst::Barrier { kind: if *ord == LOrdering::SeqCst { 0 } else { 1 }, access: None });
                insts.push(lower_inst(ctx, inst)?);
                continue;
            }
            LInst::Load { ordering: ord @ (LOrdering::Acquire | LOrdering::AcqRel | LOrdering::SeqCst), .. } => {
                insts.push(lower_inst(ctx, inst)?);
                insts.push(Inst::Barrier { kind: if *ord == LOrdering::SeqCst { 0 } else { 2 }, access: None });
                continue;
            }
            // A standalone `fence <ordering>`: the matching weak-memory barrier (full for
            // seq_cst/acq_rel, write for release, read for acquire), no access of its own. A
            // fence has no memory-safety obligation, so this un-drops the whole function (it was
            // previously an unsupported construct that failed lowering).
            LInst::Fence { ordering } => {
                let kind = match ordering {
                    LOrdering::SeqCst | LOrdering::AcqRel => 0,
                    LOrdering::Release => 1,
                    LOrdering::Acquire => 2,
                    LOrdering::None => {
                        continue;
                    }
                };
                insts.push(Inst::Barrier { kind, access: None });
                continue;
            }
            _ => {}
        }
                // A `load ptr` that reads a *reference field* of a DWARF-typed struct
        // (see `dwarf_field_loads`): keep the load (it checks the field access),
        // then materialise its result as a valid reference — the loaded pointer
        // is a `&T`/`&mut T` by the field's declared type, so accesses through it
        // prove. Without this the loaded field pointer has lost provenance.
        if let LInst::Load { dst, ptr, align_meta, .. } = inst {
            if let Some(&(size, align, writable, assumed)) = ctx.field_ref_loads.get(dst) {
                // The field address the pointer was loaded from — so the executor can give
                // two loads of the *same* field the same materialised region.
                let src = ctx.operand(ptr, 64).ok();
                insts.push(lower_inst(ctx, inst)?);
                insts.push(Inst::RefWitness {
                    dst: ctx.reg(dst)?,
                    size: Some(size),
                    // The DWARF pointee type gives a natural alignment; an `!align`
                    // metadatum on the load is a stronger, explicit guarantee — take
                    // the larger so an aligned access through the field proves.
                    align: align.max(align_meta.unwrap_or(0)),
                    writable,
                    // A raw-pointer field is only valid under `assume_valid_params`.
                    assumed,
                    src,
                });
                continue;
            }
        }
        // A recognized library/kernel API (allocator, deallocator, user-copy, …) is
        // lowered from its **external effect contract** (crates/contracts/data/*.contract)
        // instead of a hardcoded table: an `Alloc`/`Dealloc`/`MemIntrinsic` that models the
        // API's memory effect. This keeps the path *exact* (an `Inst::Call` would taint it,
        // disabling refutation) and lets a new API be covered by writing one contract block.
        // Integer min/max intrinsics (`llvm.umin`/`umax`/`smin`/`smax`): model the *value*
        // as `select(a <cmp> b, a, b)` instead of an opaque fresh scalar, so a shift/index
        // amount computed from `umin(field, size)` stays a real expression over its inputs
        // (and carries their bounds). Two MSIR instructions — the comparison then the select.
        if let LInst::Call { dst: Some(dst), callee, args, .. } = inst {
            if let (Some(cmp), [a, b]) = (minmax_intrinsic(callee), args.as_slice()) {
                let w = intrinsic_width(callee);
                let d = ctx.reg(dst)?;
                let cmp_reg = ctx.fresh();
                let (lhs, rhs) = (ctx.operand(a, w)?, ctx.operand(b, w)?);
                insts.push(Inst::Assign {
                    dst: cmp_reg,
                    ty: Type::int(1),
                    value: RValue::Cmp { op: cmp, lhs: lhs.clone(), rhs: rhs.clone() },
                });
                insts.push(Inst::Assign {
                    dst: d,
                    ty: Type::int(w),
                    value: RValue::Select {
                        cond: Operand::Reg(cmp_reg),
                        then_val: lhs,
                        else_val: rhs,
                    },
                });
                continue;
            }
        }
        if let LInst::Call { dst, callee, args, ret } = inst {
            if let Some(contract) = contracts().lookup(callee) {
                if emit_contract(ctx, &mut insts, contract, dst.as_deref(), args, ret)? {
                    continue;
                }
                // An annotation-only contract (taint/typestate, no memory model): the
                // pre-call effects are already emitted; now emit the *real* call (which binds
                // the result), then the `ret`-targeted effects on the bound result.
                insts.push(lower_inst(ctx, inst)?);
                emit_ret_effects(ctx, &mut insts, contract, dst.as_deref())?;
                continue;
            }
            // Inline asm with structured memory operands (`<inline asm[...]|w0|r1>`): emit a
            // precise access obligation on each pointer operand — so a UAF/OOB/null through the
            // asm's memory operand is caught — then the base call (clean name) for its clobber.
            if callee.starts_with("<inline asm") && callee.contains('|') {
                emit_inline_asm_mem_ops(ctx, &mut insts, callee, args)?;
                // Register-dataflow semantic (`|semC<j>` copy / `|semZ` zero): bind the output
                // register to the provable value instead of havoc-ing it (see `asm_reg_semantic`).
                // Emitted only when there is an output register; the base call still runs (with no
                // `dst`) so any memory clobber is still modelled.
                let sem_bound = if let Some(d) = dst.as_deref() {
                    emit_asm_semantic(ctx, &mut insts, callee, args, d, ret)?
                } else {
                    false
                };
                let base: String = callee.split('|').next().unwrap_or(callee).to_string();
                let call_args = args.iter().map(|a| ctx.operand(a, 64)).collect::<Result<Vec<_>>>()?;
                insts.push(Inst::Call {
                    // The output is bound by the semantic Assign above — don't re-havoc it here.
                    dst: if sem_bound { None } else { dst.as_deref().map(|d| ctx.reg(d)).transpose()? },
                    callee: Callee::Symbol(base),
                    args: call_args,
                    ret_ty: lower_type(ret),
                    ret_ref: None,
                });
                continue;
            }
        }
        insts.push(lower_inst(ctx, inst)?);
    }

    let term = match &b.term {
        // `invoke`: emit the call, then branch to *both* the normal and the
        // unwind-cleanup successor via an unconstrained condition (a fresh,
        // never-defined register), so the cleanup path — which may run `Drop`
        // code — is analysed, not dropped. Modelling only the normal edge would be
        // a false-PASS hole.
        LTerm::Invoke { dst, ret, callee, args, ok, cleanup } => {
            let call_dst = dst.as_deref().map(|d| ctx.reg(d)).transpose()?;
            let callee_ir = resolve_callee(ctx, callee);
            let call_args = args
                .iter()
                .map(|a| ctx.operand(a, 64))
                .collect::<Result<Vec<_>>>()?;
            insts.push(Inst::Call {
                dst: call_dst,
                callee: callee_ir,
                args: call_args,
                ret_ty: lower_type(ret),
                ret_ref: None,
            });
            let then_args = branch_args(ctx, &b.label, ok)?;
            let else_args = branch_args(ctx, &b.label, cleanup)?;
            let then_blk = ctx.block(ok)?;
            let else_blk = ctx.block(cleanup)?;
            let cond = ctx.fresh();
            Terminator::CondBr {
                cond: Operand::Reg(cond),
                then_blk,
                then_args,
                else_blk,
                else_args,
            }
        }
        // `callbr` (inline-asm goto): the asm may clobber memory and control may
        // continue at the fallthrough or any listed label. Emit the asm as an opaque
        // (memory-havoc) call, then a Switch to *every* target on a fresh scrutinee,
        // so all successors are analysed (dropping any would be a false-PASS hole).
        LTerm::CallBr { dst, targets } => {
            let call_dst = dst.as_deref().map(|d| ctx.reg(d)).transpose()?;
            insts.push(Inst::Call {
                dst: call_dst,
                callee: Callee::Symbol("<inline asm>".into()),
                args: Vec::new(),
                ret_ty: Type::int(64),
                ret_ref: None,
            });
            let blk = |name: &str| ctx.block(name);
            let default = blk(&targets[0])?;
            let cases = targets[1..]
                .iter()
                .enumerate()
                .map(|(i, t)| Ok((BitVector::new(64, i as u128), blk(t)?)))
                .collect::<Result<Vec<_>>>()?;
            Terminator::Switch { value: Operand::Reg(ctx.fresh()), cases, default }
        }
        _ => lower_term(ctx, &b.label, &b.term)?,
    };

    Ok(BasicBlock {
        id,
        params: block_params,
        insts,
        inst_spans: Vec::new(),
        term,
    })
}

pub(crate) fn lower_inst(ctx: &Ctx, inst: &LInst) -> Result<Inst> {
    Ok(match inst {
        LInst::Alloca { dst, ty, align } => Inst::Alloc {
            dst: ctx.reg(dst)?,
            region: RegionKind::Stack,
            elem: lower_type(ty),
            count: Operand::int(64, 1),
            align: align_or(*align, ty),
        },
        LInst::Load { dst, ty, ptr, align, atomic, .. } => Inst::Load {
            dst: ctx.reg(dst)?,
            ty: lower_type(ty),
            ptr: ctx.operand(ptr, 64)?,
            align: align_or(*align, ty),
            volatile: *atomic,
        },
        LInst::Fence { .. } => Inst::Barrier { kind: 0, access: None },
        LInst::Store { ty, val, ptr, align, atomic, .. } => Inst::Store {
            ty: lower_type(ty),
            ptr: ctx.operand(ptr, 64)?,
            value: ctx.operand(val, type_width(ty))?,
            align: align_or(*align, ty),
            volatile: *atomic,
        },
        LInst::Gep { dst, elem, base, index } => Inst::PtrOffset {
            dst: ctx.reg(dst)?,
            base: ctx.operand(base, 64)?,
            index: ctx.operand(index, 64)?,
            elem: lower_type(elem),
        },
        LInst::Bin { dst, op, ty, a, b, nsw, nuw } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: lower_type(ty),
            value: RValue::Bin {
                op: lower_bin(*op),
                lhs: ctx.operand(a, type_width(ty))?,
                rhs: ctx.operand(b, type_width(ty))?,
                flags: csolver_ir::WrapFlags { nsw: *nsw, nuw: *nuw },
            },
        },
        LInst::Icmp { dst, pred, ty, a, b } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: Type::Bool,
            value: RValue::Cmp {
                op: lower_pred(*pred),
                lhs: ctx.operand(a, type_width(ty))?,
                rhs: ctx.operand(b, type_width(ty))?,
            },
        },
        LInst::Cast { dst, op, val, to } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: lower_type(to),
            value: RValue::Cast {
                op: lower_cast(*op),
                operand: ctx.operand(val, 64)?,
                to: lower_type(to),
            },
        },
        // Expanded to instruction chains in `lower_block`; unreachable here.
        LInst::GepField { .. } | LInst::GepChain { .. } | LInst::AtomicRmw { .. } => {
            return Err(Error::unsupported("multi-instruction lowering outside lower_block"))
        }
        LInst::Opaque { dst } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: Type::int(64),
            value: RValue::Use(Operand::Const(Const::Undef)),
        },
        LInst::Select { dst, cond, then_val, else_val } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: Type::int(64),
            value: RValue::Select {
                cond: ctx.operand(cond, 1)?,
                then_val: ctx.operand(then_val, 64)?,
                else_val: ctx.operand(else_val, 64)?,
            },
        },
        LInst::ExtractValue { dst, agg, index } => {
            let dst_reg = ctx.reg(dst)?;
            // Field 0 of a checked-arith tuple is the arithmetic result; anything
            // else (the overflow flag, or a non-checked aggregate) stays opaque —
            // sound, and the flag only guards the panic branch.
            let checked = match agg {
                LValue::Local(name) if *index == 0 => ctx.checked_arith.get(name),
                _ => None,
            };
            match checked {
                Some((op, a, b)) => Inst::Assign {
                    dst: dst_reg,
                    ty: Type::int(64),
                    value: RValue::Bin {
                        op: *op,
                        lhs: ctx.operand(a, 64)?,
                        rhs: ctx.operand(b, 64)?,
                    flags: Default::default(),
                    },
                },
                None => Inst::Assign {
                    dst: dst_reg,
                    ty: Type::int(64),
                    value: RValue::Use(Operand::Const(Const::Undef)),
                },
            }
        }
        LInst::Call { dst, ret, callee, args } => {
            let dst = dst.as_deref().map(|d| ctx.reg(d)).transpose()?;
            if let (Some(_), Some(d)) = (overflow_intrinsic_op(callee), dst) {
                // A checked-arithmetic intrinsic is pure arithmetic; its tuple
                // result is recovered field-wise at `extractvalue`, so the tuple
                // register itself is never read — an opaque placeholder.
                Inst::Assign {
                    dst: d,
                    ty: Type::int(64),
                    value: RValue::Use(Operand::Const(Const::Undef)),
                }
            } else if callee.starts_with("llvm.lifetime.") {
                // `llvm.lifetime.start/end(i64 size, ptr p)`: the slot's live range. Keep
                // the pointer argument so the executor can transition the region's
                // lifetime (end → dead, start → live) and catch a use-after-scope. Other
                // no-op intrinsics stay argument-free.
                let ptr = args.last().and_then(|a| ctx.operand(a, 64).ok());
                Inst::Intrinsic { dst, name: callee.clone(), args: ptr.into_iter().collect() }
            } else if is_noop_intrinsic(callee) {
                // Modelled as a no-op (does not touch caller-visible memory).
                Inst::Intrinsic { dst, name: callee.clone(), args: Vec::new() }
            } else if let Some(kind) = mem_kind(callee) {
                // `llvm.memcpy/memmove/memset(dst, src|val, len, isvolatile)`.
                if args.len() >= 3 {
                    let dst_op = ctx.operand(&args[0], 64)?;
                    let len = ctx.operand(&args[2], 64)?;
                    let src = if matches!(kind, MemKind::Copy | MemKind::Move) {
                        Some(ctx.operand(&args[1], 64)?)
                    } else {
                        None
                    };
                    Inst::MemIntrinsic { kind, dst: dst_op, src, len }
                } else {
                    // Malformed — treat as an opaque (conservative) call.
                    Inst::Call {
                        dst: None,
                        callee: Callee::Symbol(callee.clone()),
                        args: Vec::new(),
                        ret_ty: Type::Unit,
                        ret_ref: None,
                    }
                }
            } else {
                let callee = resolve_callee(ctx, callee);
                let args = args
                    .iter()
                    .map(|a| ctx.operand(a, 64))
                    .collect::<Result<_>>()?;
                Inst::Call { dst, callee, args, ret_ty: lower_type(ret), ret_ref: None }
            }
        }
    })
}

pub(crate) fn lower_term(ctx: &Ctx, from: &str, term: &LTerm) -> Result<Terminator> {
    Ok(match term {
        LTerm::Ret(v) => match v {
            Some(v) => Terminator::Return(Some(ctx.operand(v, 64)?)),
            None => Terminator::Return(None),
        },
        LTerm::Br(target) => Terminator::Br {
            target: ctx.block(target)?,
            args: branch_args(ctx, from, target)?,
        },
        LTerm::CondBr(cond, t, f) => Terminator::CondBr {
            cond: ctx.operand(cond, 1)?,
            then_blk: ctx.block(t)?,
            then_args: branch_args(ctx, from, t)?,
            else_blk: ctx.block(f)?,
            else_args: branch_args(ctx, from, f)?,
        },
        LTerm::Switch { value, width, default, cases } => {
            // MSIR `Switch` carries no per-target arguments. A case/default
            // target that has phis referencing this block therefore receives
            // fresh (havoc'd) parameters in the engine — a sound
            // over-approximation, precise for the common discriminant dispatch
            // whose arms have no such phis.
            // Clamp to the 128-bit concrete domain so a >128-bit discriminant (exotic,
            // but legal IR) cannot panic the bit-vector constructor. At most an
            // over-approximation of which arm matches — sound (extra reachable arms).
            let w = (*width).clamp(1, 128);
            let cases = cases
                .iter()
                .map(|(cv, dest)| Ok((BitVector::new(w, *cv as u128), ctx.block(dest)?)))
                .collect::<Result<Vec<_>>>()?;
            Terminator::Switch {
                value: ctx.operand(value, w)?,
                cases,
                default: ctx.block(default)?,
            }
        }
        LTerm::Unreachable => Terminator::Unreachable,
        // Handled in `lower_block` (they need to append the call instruction);
        // defensive and sound if ever reached directly.
        LTerm::Invoke { .. } | LTerm::CallBr { .. } => Terminator::Unreachable,
    })
}

/// The arguments to pass along the edge `from -> to`: each of `to`'s phi
/// incoming values for predecessor `from`, in phi order.
pub(crate) fn branch_args(ctx: &Ctx, from: &str, to: &str) -> Result<Vec<Operand>> {
    let target = ctx
        .func
        .blocks
        .iter()
        .find(|b| b.label == to)
        .ok_or_else(|| Error::parse(format!("unknown block %{to}")))?;
    let mut args = Vec::with_capacity(target.phis.len());
    for phi in &target.phis {
        let (val, _) = phi
            .incomings
            .iter()
            .find(|(_, pred)| pred == from)
            .ok_or_else(|| {
                Error::parse(format!(
                    "phi %{} has no incoming value for predecessor %{from}",
                    phi.dst
                ))
            })?;
        args.push(ctx.operand(val, type_width(&phi.ty))?);
    }
    Ok(args)
}
