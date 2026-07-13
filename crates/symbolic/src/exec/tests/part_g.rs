use super::*;

/// A use-after-free: alloc, free, then store through the freed pointer.
fn use_after_free() -> Function {
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    bb0.insts.push(Inst::Dealloc {
        region: RegionKind::Heap,
        ptr: Operand::Reg(buf),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(buf),
        value: Operand::int(8, 0),
        align: 1, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "uaf".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn use_after_free_is_not_proven() {
    let f = use_after_free();
    let r = discharge_function(&f);
    // The free itself (index 1) is proven (base of a live region).
    let free = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("free");
    assert!(free.proven);
    // The store after free (index 2) must NOT prove temporal safety.
    let uaf = r
        .mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree)
        .expect("uaf");
    assert!(!uaf.proven, "use-after-free must stay unproven");
    // On this exact path the region is definitely freed, so the UAF is
    // refuted with a (here input-free) witness.
    assert!(uaf.refutation.is_some(), "definite use-after-free is refuted");
}

/// `double_free()`: `buf = alloc; free buf; free buf` — the second free is a
/// definite double free.
fn double_free() -> Function {
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    bb0.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
    bb0.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
    Function {
        id: FuncId(0),
        name: "double_free".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `branch_fixture(K)`: `if i < K { if i >= 1 { check } }`. The inner branch
/// `i >= 1` is unreachable exactly when `K == 1` (`i < 1 ∧ i >= 1`).
fn branch_fixture(c_bound: u128, name: &'static str) -> Function {
    let i = RegId(0);
    let c = RegId(1);
    let d = RegId(2);
    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb0.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(i), rhs: Operand::int(64, c_bound) },
    });
    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(d),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb1.insts.push(Inst::Assign {
        dst: d,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Uge, lhs: Operand::Reg(i), rhs: Operand::int(64, 1) },
    });
    let mut bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
    bb2.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(i), rhs: Operand::int(64, 8) },
        note: "inner check".into(),
    });
    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
    Function {
        id: FuncId(0),
        name: name.into(),
        params: vec![(i, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

#[test]
fn infeasible_branch_is_pruned() {
    // `if i < 1 { if i >= 1 { check } }` — the inner block is unreachable, so
    // its check is never explored (absent from the report).
    let r = discharge_function(&branch_fixture(1, "dead"));
    assert!(r.outcome(BlockId(2), 0).is_none(), "the dead inner check is pruned");
}

#[test]
fn feasible_branch_is_explored() {
    // `if i < 8 { if i >= 1 { check } }` — the inner block is reachable
    // (e.g. i = 5), so its check IS explored.
    let r = discharge_function(&branch_fixture(8, "live"));
    assert!(r.outcome(BlockId(2), 0).is_some(), "the reachable inner check is explored");
}

/// `diamond_phi(sel)`: `p = if sel < 1 { 3 } else { 5 }; check p < 8`. The
/// join block has a PHI (`p`) merged via `ITE`; the check holds on the merged
/// value (both arms are < 8).
fn diamond_phi() -> Function {
    let sel = RegId(0);
    let c = RegId(1);
    let p = RegId(2);
    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        },
    );
    bb0.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(sel), rhs: Operand::int(64, 1) },
    });
    let bb1 = BasicBlock::new(BlockId(1), Terminator::Br { target: BlockId(3), args: vec![Operand::int(64, 3)] });
    let bb2 = BasicBlock::new(BlockId(2), Terminator::Br { target: BlockId(3), args: vec![Operand::int(64, 5)] });
    let mut bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
    bb3.params = vec![(p, Type::int(64))];
    bb3.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(p), rhs: Operand::int(64, 8) },
        note: "merged p < 8".into(),
    });
    Function {
        id: FuncId(0),
        name: "diamond_phi".into(),
        params: vec![(sel, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

#[test]
fn merged_phi_value_is_proven_at_the_join() {
    // The join is analysed once with `p = ite(sel<1, 3, 5)`, and the check
    // `p < 8` is proved bit-precisely on the merged value.
    let r = discharge_function(&diamond_phi());
    assert_eq!(r.outcome(BlockId(3), 0), Some(SymOutcome::Proven));
}

/// `n` independent diamonds in sequence — `2^n` distinct paths, but only
/// `4n + 1` blocks. Each diamond `i` branches on bit `i` of `sel`.
fn wide_diamonds(n: usize) -> Function {
    let sel = RegId(0);
    let final_id = BlockId((4 * n) as u32);
    let mut blocks = Vec::new();
    for i in 0..n {
        let h = BlockId((4 * i) as u32);
        let t = BlockId((4 * i + 1) as u32);
        let e = BlockId((4 * i + 2) as u32);
        let m = BlockId((4 * i + 3) as u32);
        let next = if i + 1 < n { BlockId((4 * (i + 1)) as u32) } else { final_id };
        let tmask = RegId((1 + 2 * i) as u32);
        let creg = RegId((2 + 2 * i) as u32);
        let mut hb = BasicBlock::new(
            h,
            Terminator::CondBr { cond: Operand::Reg(creg), then_blk: t, then_args: vec![], else_blk: e, else_args: vec![] },
        );
        hb.insts.push(Inst::Assign {
            dst: tmask,
            ty: Type::int(64),
            value: RValue::Bin { op: BinOp::And, lhs: Operand::Reg(sel), rhs: Operand::int(64, 1u128 << i) , flags: Default::default() },
        });
        hb.insts.push(Inst::Assign {
            dst: creg,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Ne, lhs: Operand::Reg(tmask), rhs: Operand::int(64, 0) },
        });
        blocks.push(hb);
        blocks.push(BasicBlock::new(t, Terminator::Br { target: m, args: vec![] }));
        blocks.push(BasicBlock::new(e, Terminator::Br { target: m, args: vec![] }));
        blocks.push(BasicBlock::new(m, Terminator::Br { target: next, args: vec![] }));
    }
    let mut fb = BasicBlock::new(final_id, Terminator::Return(None));
    fb.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::int(64, 3), rhs: Operand::int(64, 8) },
        note: "final".into(),
    });
    blocks.push(fb);
    Function {
        id: FuncId(0),
        name: "wide".into(),
        params: vec![(sel, Type::int(64))],
        ret_ty: Type::Unit,
        blocks,
        entry: BlockId(0),
    }
}

#[test]
fn wide_cfg_is_processed_once_per_block_not_per_path() {
    // 8 independent diamonds = 256 distinct paths, but only 33 blocks. With a
    // budget far below the path count, merging still verifies — each block is
    // processed once (the old per-path walk would truncate).
    let f = wide_diamonds(8);
    let r = discharge_with(&f, crate::ExecLimits { max_visits: 40, ..Default::default() });
    assert!(!r.truncated, "merging keeps visits linear in blocks, not exponential in paths");
    assert_eq!(r.outcome(BlockId(32), 0), Some(SymOutcome::Proven), "final check verified");
}

#[test]
fn double_free_is_refuted() {
    let r = discharge_function(&double_free());
    // First free (index 1) is proven safe.
    let first = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("first free");
    assert!(first.proven);
    // Second free (index 2) is a definite double free — refuted.
    let second = r.mem_decision(BlockId(0), 2, SafetyProperty::NoDoubleFree).expect("second free");
    assert!(!second.proven);
    assert!(second.refutation.is_some(), "double free is refuted with a witness");
}
