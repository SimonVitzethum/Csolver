use super::*;

/// `alloca; store; call @unknown(); load` — with `kind` distinguishing the
/// region. A callee cannot legitimately free a caller's *stack* slot (that
/// free is UB, refuted in the callee by `check_dealloc`'s non-heap check),
/// so the alloca's liveness survives the opaque call and the load's
/// use-after-free obligation is provable. This assume/guarantee pair is what
/// keeps rustc's ubiquitous alloca-heavy debug IR provable across helper
/// calls.
fn call_then_load(kind: RegionKind) -> Function {
    let buf = RegId(0);
    let v = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: kind,
        elem: Type::int(32),
        count: Operand::int(64, 1),
        align: 4,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(buf),
        value: Operand::int(32, 7),
        align: 4, volatile: false
    });
    bb0.insts.push(Inst::Call {
        dst: None,
        callee: Callee::Symbol("unknown".into()),
        args: vec![],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(buf), align: 4 , volatile: false});
    Function {
        id: FuncId(0),
        name: "call_then_load".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn stack_liveness_survives_an_opaque_call() {
    let r = discharge_function(&call_then_load(RegionKind::Stack));
    let d = r
        .mem_decision(BlockId(0), 3, SafetyProperty::NoUseAfterFree)
        .expect("UAF obligation for the load");
    assert!(d.proven, "a stack slot cannot be freed by a callee: {d:?}");
}

/// Positive control for the stack-liveness rule: an *owned heap* region can
/// genuinely be handed off and freed by an opaque callee, so its liveness
/// must NOT be provable after the call. If this starts passing, the havoc is
/// muted and the rule above proves too much.
#[test]
fn heap_liveness_is_still_havocked_by_an_opaque_call() {
    let r = discharge_function(&call_then_load(RegionKind::Heap));
    let d = r
        .mem_decision(BlockId(0), 3, SafetyProperty::NoUseAfterFree)
        .expect("UAF obligation for the load");
    assert!(!d.proven, "owned heap liveness must not survive an opaque call: {d:?}");
}

/// Freeing a stack region is UB no matter its state — and it is the
/// callee-side guarantee the stack-liveness rule composes with, so it must
/// be *refuted*, not merely unproven.
#[test]
fn freeing_a_stack_region_is_refuted() {
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Stack,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    bb0.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
    let f = Function {
        id: FuncId(0),
        name: "free_stack".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let r = discharge_function(&f);
    let d = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("free");
    assert!(!d.proven, "freeing a stack region must never be proven");
    assert!(d.refutation.is_some(), "freeing a stack region is definite UB: {d:?}");
}

/// A counting loop writing across an allocation:
///   bb0: buf = alloc i32*n ; br bb1(0)
///   bb1(i): c = i < n ; condbr c -> bb2(i) / bb3
///   bb2(j): p = buf + j*4 ; store 0 -> p ; nj = j+1 ; br bb1(nj)
///   bb3: return
pub(super) fn loop_store() -> Function {
    let n = RegId(0);
    let buf = RegId(1);
    let i = RegId(2);
    let c = RegId(3);
    let j = RegId(4);
    let p = RegId(5);
    let nj = RegId(6);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br {
            target: BlockId(1),
            args: vec![Operand::int(64, 0)],
        },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 4,
    });

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(2),
            then_args: vec![Operand::Reg(i)],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb1.params = vec![(i, Type::int(64))];
    bb1.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: RValue::Cmp {
            op: CmpOp::Slt,
            lhs: Operand::Reg(i),
            rhs: Operand::Reg(n),
        },
    });

    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br {
            target: BlockId(1),
            args: vec![Operand::Reg(nj)],
        },
    );
    bb2.params = vec![(j, Type::int(64))];
    bb2.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(j),
        elem: Type::int(32),
    });
    bb2.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    });
    bb2.insts.push(Inst::Assign {
        dst: nj,
        ty: Type::int(64),
        value: RValue::Bin {
            op: BinOp::Add,
            lhs: Operand::Reg(j),
            rhs: Operand::int(64, 1),
        flags: Default::default(),
        },
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "loop_store".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

/// Store a pointer into a slot, load it back, dereference it. Without a
/// heap model the loaded pointer is opaque (deref → Unknown); with the
/// alias-aware heap, provenance survives the round-trip and the deref proves.
fn indirect_store() -> Function {
    let buf = RegId(0);
    let slot = RegId(1);
    let p = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 16),
        align: 1,
    });
    bb0.insts.push(Inst::Alloc {
        dst: slot,
        region: RegionKind::Heap,
        elem: Type::ptr(Type::int(8)),
        count: Operand::int(64, 1),
        align: 8,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Reg(slot),
        value: Operand::Reg(buf),
        align: 8, volatile: false
    });
    bb0.insts.push(Inst::Load {
        dst: p,
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Reg(slot),
        align: 8, volatile: false
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(p),
        value: Operand::int(8, 0),
        align: 1, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "indirect_store".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// slot ← buf; call `asm`; p = load slot; store through p. A register-only
/// (`<inline asm nomem>`) call must NOT havoc the heap, so the round-trip survives
/// and the final store proves temporal safety; a memory-clobbering `<inline asm>`
/// does havoc, so it does not.
fn asm_roundtrip(asm_name: &str) -> Function {
    let slot = RegId(0);
    let buf = RegId(1);
    let p = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc { dst: slot, region: RegionKind::Heap, elem: Type::ptr(Type::int(8)), count: Operand::int(64, 1), align: 8 });
    bb0.insts.push(Inst::Alloc { dst: buf, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 8), align: 1 });
    bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(slot), value: Operand::Reg(buf), align: 8 , volatile: false});
    bb0.insts.push(Inst::Call { dst: None, callee: csolver_ir::Callee::Symbol(asm_name.into()), args: vec![], ret_ty: Type::Unit, ret_ref: None });
    bb0.insts.push(Inst::Load { dst: p, ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(slot), align: 8 , volatile: false});
    bb0.insts.push(Inst::Store { ty: Type::int(8), ptr: Operand::Reg(p), value: Operand::int(8, 0), align: 1 , volatile: false});
    Function { id: FuncId(0), name: "asm_rt".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb0], entry: BlockId(0) }
}

#[test]
fn register_only_inline_asm_does_not_havoc_the_heap() {
    let r = discharge_function(&asm_roundtrip("<inline asm nomem>"));
    let d = r.mem_decision(BlockId(0), 5, SafetyProperty::NoUseAfterFree).expect("uaf");
    assert!(d.proven, "register-only asm must preserve the heap: {}", d.residual);
}

#[test]
fn memory_clobbering_inline_asm_havocs_the_heap() {
    let r = discharge_function(&asm_roundtrip("<inline asm>"));
    let d = r.mem_decision(BlockId(0), 5, SafetyProperty::NoUseAfterFree).expect("uaf");
    assert!(!d.proven, "a memory-clobbering asm must havoc (stay conservative)");
}

#[test]
fn pointer_survives_store_load_roundtrip() {
    let f = indirect_store();
    let r = discharge_function(&f);
    // The final deref (store at index 4): provenance survived the load, so
    // non-null and in-bounds are proven (they would be Unknown if the load
    // had returned an opaque value).
    for prop in [
        SafetyProperty::NoNullDeref,
        SafetyProperty::NoUseAfterFree,
        SafetyProperty::InBounds,
        SafetyProperty::ValidWrite,
    ] {
        let d = r.mem_decision(BlockId(0), 4, prop).expect("decided");
        assert!(d.proven, "{prop} should be proven via heap/alias: {}", d.residual);
    }
}

/// Regression (soundness): a `free` inside a loop body must NOT let an
/// access or the free itself be proved — later iterations are UAF/double-free.
#[test]
fn free_inside_loop_is_not_proven() {
    let n = RegId(0);
    let buf = RegId(1);
    let i = RegId(2);
    let c = RegId(3);
    let j = RegId(4);
    let nj = RegId(5);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::int(64, 0)] },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(2),
            then_args: vec![Operand::Reg(i)],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb1.params = vec![(i, Type::int(64))];
    bb1.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Slt, lhs: Operand::Reg(i), rhs: Operand::Reg(n) },
    });
    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(nj)] },
    );
    bb2.params = vec![(j, Type::int(64))];
    bb2.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(buf),
        value: Operand::int(8, 0),
        align: 1, volatile: false
    });
    bb2.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
    bb2.insts.push(Inst::Assign {
        dst: nj,
        ty: Type::int(64),
        value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(j), rhs: Operand::int(64, 1) , flags: Default::default() },
    });
    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
    let f = Function {
        id: FuncId(0),
        name: "loop_free".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    };
    let r = discharge_function(&f);
    let uaf = r.mem_decision(BlockId(2), 0, SafetyProperty::NoUseAfterFree).expect("uaf");
    assert!(!uaf.proven, "store in a freeing loop must not prove temporal safety");
    let df = r.mem_decision(BlockId(2), 1, SafetyProperty::NoDoubleFree).expect("df");
    assert!(!df.proven, "free in a loop must not prove no-double-free");
}

/// Regression (soundness): a call to a freeing function must invalidate
/// region liveness, so a use after it is not proved.
#[test]
fn use_after_freeing_call_is_not_proven() {
    use std::collections::HashMap;
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    bb0.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Direct(FuncId(9)),
        args: vec![Operand::Reg(buf)],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(buf),
        value: Operand::int(8, 0),
        align: 1, volatile: false
    });
    let f = Function {
        id: FuncId(0),
        name: "caller".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let mut summaries = HashMap::new();
    summaries.insert(
        FuncId(9),
        crate::summary::Summary {
            ret: crate::summary::RetSummary::Unknown,
            writes: false,
            frees: true,
            frees_arg: None,
            prov: crate::summary::ProvTransfer::default(),
            refcount_effect: vec![],
            escapes_stack: vec![],
        },
    );
    let r = discharge_with_summaries(&f, &summaries);
    let uaf = r.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
    assert!(!uaf.proven, "use after a freeing call must not prove temporal safety");
}

/// Double-free through a freeing *wrapper* (a callee that definitely frees its
/// parameter): calling it twice on the same pointer is a double-free (flagged in
/// bug-finding mode); calling it once is not.
#[test]
fn double_free_through_a_freeing_wrapper_is_flagged() {
    use std::collections::HashMap;
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    let free_call = |b: &mut BasicBlock| b.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Direct(FuncId(9)),
        args: vec![Operand::Reg(buf)],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    free_call(&mut bb0); // idx 1 — first free
    free_call(&mut bb0); // idx 2 — double free
    let f = Function {
        id: FuncId(0),
        name: "double_free_wrapper".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let mut summaries = HashMap::new();
    summaries.insert(
        FuncId(9),
        Summary { ret: RetSummary::Unknown, writes: false, frees: true, frees_arg: Some(0), prov: ProvTransfer::default(), refcount_effect: vec![], escapes_stack: vec![] },
    );
    let r = discharge_with_fields(
        &f, &summaries, &[], &[], &HashMap::new(), &HashMap::new(), true, true, false,
    );
    let first = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("first free");
    assert!(first.refutation.is_none(), "the first free must not be flagged: {first:?}");
    let second = r.mem_decision(BlockId(0), 2, SafetyProperty::NoDoubleFree).expect("second free");
    assert!(second.refutation.is_some(), "the second free of the same pointer is a double-free: {second:?}");
}

/// Soundness: `frees_arg` is derived only for a single-block `kfree`-style wrapper;
/// a multi-block callee gets `frees_arg = None`, so two calls are NOT a double-free.
#[test]
fn derive_frees_arg_only_for_single_block_wrapper() {
    let p = RegId(0);
    // Single block: `free(p)` → frees_arg = Some(0).
    let mut single = BasicBlock::new(BlockId(0), Terminator::Return(None));
    single.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(p) });
    let wrapper = Function {
        id: FuncId(0), name: "w".into(), params: vec![(p, Type::ptr(Type::int(8)))],
        ret_ty: Type::Unit, blocks: vec![single], entry: BlockId(0),
    };
    assert_eq!(crate::summary::summarize_module(&{
        let mut m = csolver_ir::Module::new("m"); m.functions.push(wrapper); m
    }).get(&FuncId(0)).unwrap().frees_arg, Some(0));
}
