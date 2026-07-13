use super::*;

/// Two `spin_lock(&l)` on the same lock without an intervening unlock is an AA
/// self-deadlock; releasing between them (unlock) clears it.
fn double_lock_fn(unlock_between: bool) -> Function {
    let l = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    // A local lock object so the two acquisitions share a base identity.
    bb0.insts.push(Inst::Alloc {
        dst: l,
        region: RegionKind::Stack,
        elem: Type::int(32),
        count: Operand::int(64, 1),
        align: 4,
    });
    let lock = |b: &mut BasicBlock| b.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Symbol("spin_lock".into()),
        args: vec![Operand::Reg(l)],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    lock(&mut bb0);
    if unlock_between {
        bb0.insts.push(Inst::Call {
            dst: None,
            callee: csolver_ir::Callee::Symbol("spin_unlock".into()),
            args: vec![Operand::Reg(l)],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
    }
    lock(&mut bb0);
    Function {
        id: FuncId(0),
        name: "dl".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn double_lock_is_flagged_as_a_deadlock() {
    let f = double_lock_fn(false);
    let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
    let r = discharge_with(&f, limits);
    // alloc=0, lock=1, lock=2 → the second lock is the deadlock.
    let d = r
        .mem_decision(BlockId(0), 2, SafetyProperty::DataRace)
        .expect("DataRace obligation at the second lock");
    assert!(d.refutation.is_some(), "re-acquiring a held lock must be flagged: {d:?}");
}

#[test]
fn pthread_mutex_double_lock_is_a_deadlock() {
    // Userspace: re-acquiring the same `pthread_mutex_t` on a path is an AA self-deadlock,
    // detected exactly as the kernel spinlock case (the lock is arg0).
    let l = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: l,
        region: RegionKind::Stack,
        elem: Type::int(32),
        count: Operand::int(64, 1),
        align: 4,
    });
    let lock = |b: &mut BasicBlock| b.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Symbol("pthread_mutex_lock".into()),
        args: vec![Operand::Reg(l)],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    lock(&mut bb0);
    lock(&mut bb0);
    let f = Function {
        id: FuncId(0),
        name: "dl".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
    let r = discharge_with(&f, limits);
    let d = r
        .mem_decision(BlockId(0), 2, SafetyProperty::DataRace)
        .expect("DataRace obligation at the second pthread_mutex_lock");
    assert!(d.refutation.is_some(), "re-acquiring a held pthread_mutex must be flagged: {d:?}");
}

#[test]
fn lock_unlock_lock_is_not_a_deadlock() {
    let f = double_lock_fn(true);
    let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
    let r = discharge_with(&f, limits);
    // alloc=0, lock=1, unlock=2, lock=3 → the last lock is fine.
    let d = r
        .mem_decision(BlockId(0), 3, SafetyProperty::DataRace)
        .expect("DataRace obligation");
    assert!(d.refutation.is_none() && d.proven, "lock/unlock/lock is balanced: {d:?}");
}

/// Soundness (no false FAIL): a lock released via an *unrecognized* helper that
/// takes the lock as an argument must NOT be reported as a double-lock when
/// re-acquired — the escape-bounded clear drops the base on any call handed it.
#[test]
fn lock_then_unlock_via_unknown_helper_then_lock_is_not_a_deadlock() {
    let l = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: l,
        region: RegionKind::Stack,
        elem: Type::int(32),
        count: Operand::int(64, 1),
        align: 4,
    });
    let call = |b: &mut BasicBlock, name: &str| b.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Symbol(name.into()),
        args: vec![Operand::Reg(l)],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    call(&mut bb0, "spin_lock"); // 1
    call(&mut bb0, "my_custom_unlock"); // 2 — NOT in LOCK_ACQUIRE, takes l → drops it
    call(&mut bb0, "spin_lock"); // 3 — must NOT be a double-lock
    let f = Function {
        id: FuncId(0),
        name: "dl_helper".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
    let r = discharge_with(&f, limits);
    let d = r
        .mem_decision(BlockId(0), 3, SafetyProperty::DataRace)
        .expect("DataRace obligation");
    assert!(
        d.refutation.is_none() && d.proven,
        "an unlock via an unrecognized helper must clear the lock (no false double-lock): {d:?}"
    );
}

#[test]
fn attacker_controlled_alloc_size_overflow_is_flagged() {
    // buf = alloc [n x i32]: size = n * 4, n attacker-controlled → can wrap.
    let n = RegId(0);
    let buf = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 8,
    });
    let f = Function {
        id: FuncId(0),
        name: "alloc_n_i32".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
    let r = discharge_with(&f, limits);
    let d = r
        .mem_decision(BlockId(0), 0, SafetyProperty::NoSizeOverflow)
        .expect("NoSizeOverflow obligation at the alloc");
    assert!(
        d.refutation.is_some(),
        "an unbounded attacker-controlled n*sizeof size must be flagged: {d:?}"
    );
}

#[test]
fn bounded_alloc_size_is_not_flagged_as_overflow() {
    // A guarded count (n < 1024) cannot overflow n*4 → the size proves safe.
    let n = RegId(0);
    let ok = RegId(1);
    let buf = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::CondBr {
        cond: Operand::Reg(ok),
        then_blk: BlockId(1),
        then_args: vec![],
        else_blk: BlockId(2),
        else_args: vec![],
    });
    bb0.insts.push(Inst::Assign {
        dst: ok,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(n), rhs: Operand::int(64, 1024) },
    });
    let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
    bb1.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 8,
    });
    let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
    let f = Function {
        id: FuncId(0),
        name: "alloc_bounded".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2],
        entry: BlockId(0),
    };
    let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
    let r = discharge_with(&f, limits);
    let d = r
        .mem_decision(BlockId(1), 0, SafetyProperty::NoSizeOverflow)
        .expect("NoSizeOverflow obligation");
    assert!(
        d.refutation.is_none() && d.proven,
        "a count guarded < 1024 cannot overflow n*4: {d:?}"
    );
}

#[test]
fn copy_to_user_of_uninitialized_buffer_is_an_info_leak() {
    let f = info_leak_fn(false);
    let r = discharge_function(&f);
    // The drain is the last instruction (index 1: alloc=0, drain=1).
    let d = r
        .mem_decision(BlockId(0), 1, SafetyProperty::NoInfoLeak)
        .expect("NoInfoLeak obligation for the drain");
    assert!(
        d.refutation.is_some(),
        "copy_to_user of a never-written buffer must be refuted as an info leak: {d:?}"
    );
}

#[test]
fn copy_to_user_with_uninitialized_tail_is_an_info_leak() {
    // 32-byte buffer, only the first 8 bytes written, all 32 copied out → the tail
    // [8,32) is disclosed uninitialized. The single-word check missed this; the
    // whole-range scan must catch it.
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 32),
        align: 8,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(64),
        ptr: Operand::Reg(buf),
        value: Operand::int(64, 0),
        align: 8, volatile: false
    });
    bb0.insts.push(Inst::MemIntrinsic {
        kind: MemKind::UserDrain,
        dst: Operand::Reg(buf),
        src: None,
        len: Operand::int(64, 32),
    });
    let f = Function {
        id: FuncId(0),
        name: "drain_tail".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let r = discharge_function(&f);
    let d = r
        .mem_decision(BlockId(0), 2, SafetyProperty::NoInfoLeak)
        .expect("NoInfoLeak obligation for the drain");
    assert!(
        d.refutation.is_some(),
        "copy_to_user of a buffer with an uninitialized tail must be flagged: {d:?}"
    );
}

#[test]
fn copy_to_user_of_initialized_buffer_does_not_leak() {
    let f = info_leak_fn(true);
    let r = discharge_function(&f);
    // alloc=0, memset=1, drain=2.
    if let Some(d) = r.mem_decision(BlockId(0), 2, SafetyProperty::NoInfoLeak) {
        assert!(
            d.refutation.is_none(),
            "a memset-initialized buffer copied out must not be flagged as a leak: {d:?}"
        );
    }
}
