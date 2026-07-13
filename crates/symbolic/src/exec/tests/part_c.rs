use super::*;

/// `init()`: `buf = alloc i32*4; store 7 -> buf; v = load buf` — read after
/// write, so the load reads an initialized value.
fn init() -> Function {
    let buf = RegId(0);
    let v = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 4),
        align: 4,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(buf),
        value: Operand::int(32, 7),
        align: 4, volatile: false
    });
    bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(buf), align: 4 , volatile: false});
    Function {
        id: FuncId(0),
        name: "init".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn initialized_read_is_not_flagged() {
    // The store `Must`-aliases the load, so the value is determined and the
    // definedness check does not fire (no refutation).
    let r = discharge_function(&init());
    let d = r
        .mem_decision(BlockId(0), 2, SafetyProperty::ValidRead)
        .expect("ValidRead obligation for the load");
    assert!(d.proven, "a read after write is proven: {d:?}");
    assert!(d.refutation.is_none(), "no refutation for an initialized read: {d:?}");
}

/// `bare(x)`: `check x < 8` — satisfiable but not valid, so NOT refuted.
fn bare_check() -> Function {
    let x = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(x), rhs: Operand::int(64, 8) },
        note: "x < 8".into(),
    });
    Function {
        id: FuncId(0),
        name: "bare".into(),
        params: vec![(x, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn satisfiable_but_invalid_check_stays_unknown() {
    // `x < 8` holds for some inputs and fails for others — never refuted.
    let r = discharge_function(&bare_check());
    assert_eq!(r.outcome(BlockId(0), 0), Some(SymOutcome::Unknown));
}

/// `unguarded(i)`: `buf = alloc i32*8; store 0 -> buf+i` — OOB for i >= 8.
fn unguarded_store() -> Function {
    let i = RegId(0);
    let buf = RegId(1);
    let p = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 8),
        align: 4,
    });
    bb0.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(i),
        elem: Type::int(32),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "unguarded".into(),
        params: vec![(i, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn concrete_size_oob_memory_access_is_refuted() {
    let r = discharge_function(&unguarded_store());
    let d = r
        .mem_decision(BlockId(0), 2, SafetyProperty::InBounds)
        .expect("in-bounds obligation exists");
    assert!(!d.proven, "an unguarded OOB write is not provable");
    let model = d.refutation.as_ref().expect("refuted with a counterexample");
    assert!(model.get("arg0").is_some(), "witness names the index: {model:?}");
}

/// `store_buf(i, n)`: alloc n i32; if 0<=i { if i<n { store buf[i] } }.
fn store_buf() -> Function {
    let i = RegId(0);
    let n = RegId(1);
    let buf = RegId(2);
    let c0 = RegId(3);
    let c1 = RegId(4);
    let p = RegId(5);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c0),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 4,
    });
    bb0.insts.push(Inst::Assign {
        dst: c0,
        ty: Type::Bool,
        value: RValue::Cmp {
            op: CmpOp::Sle,
            lhs: Operand::int(64, 0),
            rhs: Operand::Reg(i),
        },
    });

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c1),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb1.insts.push(Inst::Assign {
        dst: c1,
        ty: Type::Bool,
        value: RValue::Cmp {
            op: CmpOp::Slt,
            lhs: Operand::Reg(i),
            rhs: Operand::Reg(n),
        },
    });

    let mut bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
    bb2.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(i),
        elem: Type::int(32),
    });
    bb2.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "store_buf".into(),
        params: vec![(i, Type::int(64)), (n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

#[test]
fn guarded_store_proves_all_memory_checks() {
    let f = store_buf();
    let r = discharge_function(&f);
    assert!(!r.truncated);
    // The store is at bb2 index 1; all five obligations must be proven.
    for prop in [
        SafetyProperty::NoNullDeref,
        SafetyProperty::NoUseAfterFree,
        SafetyProperty::InBounds,
        SafetyProperty::Alignment,
        SafetyProperty::ValidWrite,
    ] {
        let d = r.mem_decision(BlockId(2), 1, prop).expect("decided");
        assert!(d.proven, "{prop} should be proven, got residual: {}", d.residual);
    }
    // PtrOffset at bb2 index 0: valid pointer arithmetic.
    let arith = r
        .mem_decision(BlockId(2), 0, SafetyProperty::ValidPointerArith)
        .expect("decided");
    assert!(arith.proven, "pointer arithmetic: {}", arith.residual);
}

#[test]
fn truncated_exploration_reports_no_memory_decision() {
    // Soundness positive control for the truncation rule. When exploration
    // hits its visit budget, the report is `{ truncated: true, ..default }` —
    // every decision map empty — so each memory op falls back to `Open` and the
    // function can never PASS on an unanalysed access. (This is the property the
    // scaling sweep's "truncated" residual bucket rests on; the sweep happens to
    // show 0 truncations today, but the guarantee must hold for the ones it will
    // eventually hit, so it is pinned here rather than assumed.) A 1-visit budget
    // truncates this 4-block function before it reaches the store at bb2.
    let f = store_buf();
    let r = discharge_with(&f, crate::ExecLimits { max_visits: 1, ..Default::default() });
    assert!(r.truncated, "a 1-visit budget must truncate a 4-block function");
    for prop in [
        SafetyProperty::NoNullDeref,
        SafetyProperty::NoUseAfterFree,
        SafetyProperty::InBounds,
        SafetyProperty::Alignment,
        SafetyProperty::ValidWrite,
    ] {
        assert!(
            r.mem_decision(BlockId(2), 1, prop).is_none(),
            "{prop} must be undecided (Open) under truncation, never reported safe"
        );
    }
}

#[test]
fn time_budget_bail_reports_no_memory_decision() {
    // The per-function wall-clock bail (the turnkey-path termination guarantee)
    // must fall to non-PASS exactly like the visit budget: a zero time budget
    // truncates before any memory op is decided, so every obligation is `Open`,
    // never a half-analysed `PASS`. (Soundness pin for the bail path, the same
    // discipline as the wall-clock solve valve.)
    let f = store_buf();
    let r = discharge_with(
        &f,
        crate::ExecLimits {
            max_visits: usize::MAX,
            time_budget: Some(std::time::Duration::ZERO),
            ..Default::default()
        },
    );
    assert!(r.truncated, "a zero time budget must truncate");
    for prop in [
        SafetyProperty::NoNullDeref,
        SafetyProperty::InBounds,
        SafetyProperty::Alignment,
        SafetyProperty::ValidWrite,
    ] {
        assert!(
            r.mem_decision(BlockId(2), 1, prop).is_none(),
            "{prop} must be undecided (Open) under the time bail, never reported safe"
        );
    }
}

/// A **stack** allocation of `count` bytes, then a read of the never-written
/// first word. `count` symbolic (a frame model / VLA) vs. a constant.
fn stack_uninit_read(count: Operand) -> Function {
    let p = RegId(1);
    let v = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc { dst: p, region: RegionKind::Stack, elem: Type::int(8), count, align: 16 });
    bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(p), align: 1, volatile: false });
    Function {
        id: FuncId(0),
        name: "frame".into(),
        params: vec![(RegId(0), Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn symbolic_size_stack_uninit_read_is_not_refuted() {
    // A symbolic-size stack region is `assumed` (an open-above machine frame or a
    // VLA): a read of an untracked byte may be caller-initialized, so it is left
    // UNKNOWN, never a false uninitialized-read FAIL.
    let sym = discharge_function(&stack_uninit_read(Operand::Reg(RegId(0))));
    let d = sym.mem_decision(BlockId(0), 1, SafetyProperty::ValidRead).expect("ValidRead obligation");
    assert!(d.refutation.is_none(), "symbolic-size (assumed) stack read is not refuted: {d:?}");

    // A *constant*-size stack region stays precise: the same unwritten read IS a
    // definite uninitialized-read refutation (the gating is exactly the symbolic size).
    let fixed = discharge_function(&stack_uninit_read(Operand::int(64, 16)));
    let d = fixed.mem_decision(BlockId(0), 1, SafetyProperty::ValidRead).expect("ValidRead obligation");
    assert!(d.refutation.is_some(), "constant-size stack unwritten read is refuted: {d:?}");
}
