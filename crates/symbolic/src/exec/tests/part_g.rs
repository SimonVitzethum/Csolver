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

/// A retag-marker instruction: `dst_borrow` becomes a new `&mut` reborrow of `parent`.
fn retag(dst_borrow: RegId, parent: RegId) -> Inst {
    Inst::Intrinsic {
        dst: None,
        name: "csolver.retag.mut".into(),
        args: vec![Operand::Reg(dst_borrow), Operand::Reg(parent)],
    }
}

/// A shared retag marker: `dst_borrow = &(*parent)` (a `&T` reborrow).
fn retag_shared(dst_borrow: RegId, parent: RegId) -> Inst {
    Inst::Intrinsic {
        dst: None,
        name: "csolver.retag.shared".into(),
        args: vec![Operand::Reg(dst_borrow), Operand::Reg(parent)],
    }
}

#[test]
fn read_through_shared_ref_after_mut_write_invalidated_it_is_flagged() {
    // r1 = &mut *r0; s = &*r1; *r1 = 6; read *s  — the write through r1 invalidates the
    // shared borrow s (Stacked Borrows); reading s afterwards is UB.
    let (r0, r1, s, v) = (RegId(0), RegId(1), RegId(2), RegId(3));
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc { dst: r0, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 8), align: 8 });
    bb0.insts.push(Inst::Assign { dst: r1, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb0.insts.push(retag(r1, r0));
    bb0.insts.push(Inst::Assign { dst: s, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r1)) });
    bb0.insts.push(retag_shared(s, r1));
    bb0.insts.push(Inst::Store { ty: Type::int(64), ptr: Operand::Reg(r1), value: Operand::int(64, 6), align: 8, volatile: false });
    bb0.insts.push(Inst::Load { dst: v, ty: Type::int(64), ptr: Operand::Reg(s), align: 8, volatile: false });
    let f = Function { id: FuncId(0), name: "shared_uaf".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb0], entry: BlockId(0) };
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    let load = (BlockId(0), 6usize);
    let d = on.mem_decision(load.0, load.1, SafetyProperty::NoAliasingViolation).expect("aliasing obligation");
    assert!(!d.proven && d.refutation.is_some(), "reading a shared borrow after a &mut write invalidated it is UB");
}

#[test]
fn multiple_shared_borrows_are_not_flagged() {
    // s1 = &*r0; s2 = &*r0; read s1; read s2  — many shared borrows coexist (no violation).
    let (r0, s1, s2, v1, v2) = (RegId(0), RegId(1), RegId(2), RegId(3), RegId(4));
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc { dst: r0, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 8), align: 8 });
    bb0.insts.push(Inst::Assign { dst: s1, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb0.insts.push(retag_shared(s1, r0));
    bb0.insts.push(Inst::Assign { dst: s2, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb0.insts.push(retag_shared(s2, r0));
    bb0.insts.push(Inst::Load { dst: v1, ty: Type::int(64), ptr: Operand::Reg(s1), align: 8, volatile: false });
    bb0.insts.push(Inst::Load { dst: v2, ty: Type::int(64), ptr: Operand::Reg(s2), align: 8, volatile: false });
    let f = Function { id: FuncId(0), name: "multi_shared".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb0], entry: BlockId(0) };
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    for idx in [5usize, 6] {
        let d = on.mem_decision(BlockId(0), idx, SafetyProperty::NoAliasingViolation);
        assert!(d.is_none() || d.is_some_and(|d| d.proven), "coexisting shared borrows must not be flagged (idx {idx})");
    }
}

/// Build: `r0 = alloc`; two independent `&mut` reborrows of it (`r1`, `r2`); then a store
/// through the chosen one. If `use_first` the store is through `r1` — which the creation of
/// `r2` invalidated (two live `&mut` to the same place) → a use-after-invalidation. If not,
/// the store is through `r2` (the currently-valid borrow) → safe.
fn two_mut_borrows(use_first: bool) -> Function {
    let (r0, r1, r2) = (RegId(0), RegId(1), RegId(2));
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: r0,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 8,
    });
    // r1 = &mut *r0  (root reborrow)
    bb0.insts.push(Inst::Assign { dst: r1, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb0.insts.push(retag(r1, r0));
    // r2 = &mut *r0  (a second, sibling root reborrow — invalidates r1)
    bb0.insts.push(Inst::Assign { dst: r2, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb0.insts.push(retag(r2, r0));
    let via = if use_first { r1 } else { r2 };
    bb0.insts.push(Inst::Store {
        ty: Type::int(64),
        ptr: Operand::Reg(via),
        value: Operand::int(64, 5),
        align: 8,
        volatile: false,
    });
    Function { id: FuncId(0), name: "two_mut".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb0], entry: BlockId(0) }
}

#[test]
fn use_of_mut_borrow_after_sibling_invalidated_it_is_flagged() {
    let f = two_mut_borrows(true); // store through the invalidated first borrow
    let store = (BlockId(0), 5usize);
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    let d = on
        .mem_decision(store.0, store.1, SafetyProperty::NoAliasingViolation)
        .expect("aliasing obligation recorded");
    assert!(!d.proven && d.refutation.is_some(), "using r1 after r2 invalidated it is a borrow-stack violation");
    // Off by default: nothing checked.
    let off = discharge_with(&f, crate::ExecLimits::default());
    assert!(off.mem_decision(store.0, store.1, SafetyProperty::NoAliasingViolation).is_none());
}

#[test]
fn use_of_the_currently_valid_borrow_is_not_flagged() {
    // Store through r2 (the live borrow) — no violation, even with the model on.
    let f = two_mut_borrows(false);
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    let d = on.mem_decision(BlockId(0), 5, SafetyProperty::NoAliasingViolation);
    assert!(d.is_none() || d.is_some_and(|d| d.proven), "the valid borrow's write must not be flagged");
}

#[test]
fn legitimate_reborrow_chain_is_not_flagged() {
    // r1 = &mut *r0 (root); r2 = &mut *r1 (child); *r2 then *r1 — a normal nested reborrow.
    let (r0, r1, r2) = (RegId(0), RegId(1), RegId(2));
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc { dst: r0, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 8), align: 8 });
    bb0.insts.push(Inst::Assign { dst: r1, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb0.insts.push(retag(r1, r0));
    bb0.insts.push(Inst::Assign { dst: r2, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r1)) });
    bb0.insts.push(retag(r2, r1)); // child of r1
    bb0.insts.push(Inst::Store { ty: Type::int(64), ptr: Operand::Reg(r2), value: Operand::int(64, 5), align: 8, volatile: false });
    bb0.insts.push(Inst::Store { ty: Type::int(64), ptr: Operand::Reg(r1), value: Operand::int(64, 6), align: 8, volatile: false });
    let f = Function { id: FuncId(0), name: "reborrow".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb0], entry: BlockId(0) };
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    for idx in [5usize, 6] {
        let d = on.mem_decision(BlockId(0), idx, SafetyProperty::NoAliasingViolation);
        assert!(d.is_none() || d.is_some_and(|d| d.proven), "a legitimate reborrow chain must not be flagged (idx {idx})");
    }
}

/// A write through a shared `&T` borrow: materialise a shared reference, then (via a copy)
/// store through it. This is the unambiguous Rust aliasing (borrow-stack) violation.
fn write_through_shared_ref(writable: bool) -> Function {
    let r0 = RegId(0);
    let r1 = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::RefWitness {
        dst: r0,
        size: Some(8),
        align: 8,
        writable,
        assumed: false,
        src: None,
    });
    // A pointer copy (models `&T as *const T as *mut T`): the shared tag flows through.
    bb0.insts.push(Inst::Assign {
        dst: r1,
        ty: Type::ptr(Type::int(64)),
        value: RValue::Use(Operand::Reg(r0)),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(64),
        ptr: Operand::Reg(r1),
        value: Operand::int(64, 5),
        align: 8,
        volatile: false,
    });
    Function {
        id: FuncId(0),
        name: "write_through_shared".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn write_through_shared_ref_is_flagged_only_with_the_aliasing_model() {
    let f = write_through_shared_ref(false);
    // The store is at index 2 (RefWitness, Assign, Store).
    let store = (BlockId(0), 2usize);

    // With the aliasing model ON: a definite borrow-stack violation, refuted with a witness.
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    let d = on
        .mem_decision(store.0, store.1, SafetyProperty::NoAliasingViolation)
        .expect("aliasing obligation recorded");
    assert!(!d.proven, "write through &T is a violation");
    assert!(d.refutation.is_some(), "refuted with a feasibility witness");

    // With the aliasing model OFF (the default): no such obligation exists at all.
    let off = discharge_with(&f, crate::ExecLimits::default());
    assert!(
        off.mem_decision(store.0, store.1, SafetyProperty::NoAliasingViolation).is_none(),
        "the aliasing model is opt-in — nothing is checked by default"
    );
}

#[test]
fn write_through_mut_ref_is_not_an_aliasing_violation() {
    // A `&mut T` write is legitimate — never flagged, even with the model on.
    let f = write_through_shared_ref(true);
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    assert!(
        on.mem_decision(BlockId(0), 2, SafetyProperty::NoAliasingViolation).is_none(),
        "a write through &mut is allowed"
    );
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


#[test]
fn borrow_tag_flows_through_memory_store_load() {
    // r1 = &mut *r0; store r1 into slot; r2 = load slot; r3 = &mut *r0 (invalidates r1);
    // *r2 = 5  — r2 (loaded from memory) still carries r1's tag, which r3 invalidated → UB.
    let (r0, slot, r1, r2, r3) = (RegId(0), RegId(1), RegId(2), RegId(3), RegId(4));
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb.insts.push(Inst::Alloc { dst: r0, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 8), align: 8 });
    bb.insts.push(Inst::Alloc { dst: slot, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 8), align: 8 });
    bb.insts.push(Inst::Assign { dst: r1, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb.insts.push(retag(r1, r0));
    // store the borrow pointer r1 into the slot
    bb.insts.push(Inst::Store { ty: Type::ptr(Type::int(64)), ptr: Operand::Reg(slot), value: Operand::Reg(r1), align: 8, volatile: false });
    // load it back into r2 (the tag must survive the round-trip through memory)
    bb.insts.push(Inst::Load { dst: r2, ty: Type::ptr(Type::int(64)), ptr: Operand::Reg(slot), align: 8, volatile: false });
    // a sibling reborrow r3 invalidates r1
    bb.insts.push(Inst::Assign { dst: r3, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb.insts.push(retag(r3, r0));
    // use r2 (which carries r1's tag) → r1 was invalidated → UB
    bb.insts.push(Inst::Store { ty: Type::int(64), ptr: Operand::Reg(r2), value: Operand::int(64, 5), align: 8, volatile: false });
    let f = Function { id: FuncId(0), name: "mem".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb], entry: BlockId(0) };
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    let d = on.mem_decision(BlockId(0), 8, SafetyProperty::NoAliasingViolation).expect("aliasing obligation at the final store");
    assert!(!d.proven && d.refutation.is_some(), "the borrow tag must survive store→load, so using r2 after r1 was invalidated is UB");
}

#[test]
fn passing_an_invalidated_mut_borrow_to_a_call_is_flagged() {
    // r1 = &mut *r0; r2 = &mut *r0 (invalidates r1); foo(r1)  — passing the dead r1 is UB.
    let (r0, r1, r2) = (RegId(0), RegId(1), RegId(2));
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb.insts.push(Inst::Alloc { dst: r0, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 8), align: 8 });
    bb.insts.push(Inst::Assign { dst: r1, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb.insts.push(retag(r1, r0));
    bb.insts.push(Inst::Assign { dst: r2, ty: Type::ptr(Type::int(64)), value: RValue::Use(Operand::Reg(r0)) });
    bb.insts.push(retag(r2, r0));
    bb.insts.push(Inst::Call { dst: None, callee: csolver_ir::Callee::Symbol("foo".into()), args: vec![Operand::Reg(r1)], ret_ty: Type::Unit, ret_ref: None });
    let f = Function { id: FuncId(0), name: "callarg".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb], entry: BlockId(0) };
    let on = discharge_with(&f, crate::ExecLimits { aliasing_model: true, ..Default::default() });
    let d = on.mem_decision(BlockId(0), 5, SafetyProperty::NoAliasingViolation).expect("aliasing obligation at the call");
    assert!(!d.proven && d.refutation.is_some(), "passing an invalidated &mut as a call argument is a use-after-invalidation");
}
