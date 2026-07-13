use super::*;
use csolver_ir::{BasicBlock, FuncId};

/// `guarded(i, len)`: scalar SafetyCheck `i < len` under guard `i < len`.
fn guarded() -> Function {
    let i = RegId(0);
    let len = RegId(1);
    let c = RegId(2);
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
        value: RValue::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::Reg(i),
            rhs: Operand::Reg(len),
        },
    });
    let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
    bb1.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::Reg(i),
            rhs: Operand::Reg(len),
        },
        note: "guard".into(),
    });
    let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
    Function {
        id: FuncId(0),
        name: "guarded".into(),
        params: vec![(i, Type::int(64)), (len, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2],
        entry: BlockId(0),
    }
}

#[test]
fn scalar_guarded_check_still_proven() {
    let r = discharge_function(&guarded());
    assert_eq!(r.outcome(BlockId(1), 0), Some(SymOutcome::Proven));
}

/// `masked(x)`: `j = x | 8; check j < 8` — always false (definite violation).
fn masked_check() -> Function {
    let x = RegId(0);
    let j = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Assign {
        dst: j,
        ty: Type::int(64),
        value: RValue::Bin { op: BinOp::Or, lhs: Operand::Reg(x), rhs: Operand::int(64, 8) , flags: Default::default() },
    });
    bb0.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(j), rhs: Operand::int(64, 8) },
        note: "x|8 < 8".into(),
    });
    Function {
        id: FuncId(0),
        name: "masked".into(),
        params: vec![(x, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn definite_violation_is_refuted_with_model() {
    let r = discharge_function(&masked_check());
    match r.outcome(BlockId(0), 1) {
        Some(SymOutcome::Refuted(model)) => {
            assert!(model.get("arg0").is_some(), "witness names the input: {model:?}");
        }
        other => panic!("expected Refuted, got {other:?}"),
    }
}

/// Symbolic alignment proof: a load at a **masked** (aligned) offset from an aligned base is
/// proved aligned even though `gcd` cannot see the mask. `base_align` (the alloc alignment)
/// gates it: an under-aligned base leaves it unproven (sound, never a false PASS).
fn masked_offset_load(base_align: u32) -> Function {
    let i = RegId(0);
    let buf = RegId(1);
    let m = RegId(2);
    let q = RegId(3);
    let v = RegId(4);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    // buf = alloc [64 x i8], align base_align
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 64),
        align: base_align,
    });
    // m = i & 12  → m ∈ {0,4,8,12}: 4-aligned and in bounds.
    bb0.insts.push(Inst::Assign {
        dst: m,
        ty: Type::int(64),
        value: RValue::Bin { op: BinOp::And, lhs: Operand::Reg(i), rhs: Operand::int(64, 12) , flags: Default::default() },
    });
    // q = buf + m (i8 stride = byte offset)
    bb0.insts.push(Inst::PtrOffset {
        dst: q,
        base: Operand::Reg(buf),
        index: Operand::Reg(m),
        elem: Type::int(8),
    });
    // v = load i32 from q, align 4
    bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(q), align: 4, volatile: false });
    Function {
        id: FuncId(0),
        name: "masked".into(),
        params: vec![(i, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn masked_offset_from_aligned_base_is_proved_aligned() {
    // Base 16-aligned, offset masked to 4-aligned → the load (idx 3) is proved 4-aligned.
    let r = discharge_function(&masked_offset_load(16));
    let d = r
        .mem_decision(BlockId(0), 3, SafetyProperty::Alignment)
        .expect("Alignment obligation for the load");
    assert!(d.proven, "a masked offset from an aligned base is proved aligned: {d:?}");
    // Under-aligned base (align 2 < 4): the symbolic proof is gated off → not proven (sound).
    let r2 = discharge_function(&masked_offset_load(2));
    let d2 = r2
        .mem_decision(BlockId(0), 3, SafetyProperty::Alignment)
        .expect("Alignment obligation");
    assert!(!d2.proven, "an under-aligned base leaves alignment unproven (no false PASS): {d2:?}");
}

/// `uninit()`: `buf = alloc i32*4; v = load buf` — read before any write.
fn uninit() -> Function {
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
    bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(buf), align: 4 , volatile: false});
    Function {
        id: FuncId(0),
        name: "uninit".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn uninitialized_read_is_refuted() {
    // The load (block 0, idx 1) reads a freshly-allocated, never-written
    // region: a definite read of uninitialized memory, refuted as ValidRead.
    let r = discharge_function(&uninit());
    let d = r
        .mem_decision(BlockId(0), 1, SafetyProperty::ValidRead)
        .expect("ValidRead obligation for the load");
    assert!(!d.proven, "an uninitialized read must not be proven");
    assert!(d.refutation.is_some(), "it is refuted with a witness: {d:?}");
}

/// `store 7 -> a; memcpy(b, a, 4); load b`: the copy *initializes* `b`, so
/// the load must not be refuted as an uninitialized read. Before the bulk
/// write was modelled, the heap was merely cleared and the load looked
/// never-written — a definite-UB verdict on rustc's pervasive aggregate-copy
/// pattern (a false FAIL on `Result::map_err` et al.).
#[test]
fn memcpy_transfers_initialization() {
    let a = RegId(0);
    let b = RegId(1);
    let v = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    for dst in [a, b] {
        bb0.insts.push(Inst::Alloc {
            dst,
            region: RegionKind::Stack,
            elem: Type::int(32),
            count: Operand::int(64, 1),
            align: 4,
        });
    }
    bb0.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(a),
        value: Operand::int(32, 7),
        align: 4, volatile: false
    });
    bb0.insts.push(Inst::MemIntrinsic {
        kind: MemKind::Copy,
        dst: Operand::Reg(b),
        src: Some(Operand::Reg(a)),
        len: Operand::int(64, 4),
    });
    bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(b), align: 4 , volatile: false});
    let f = Function {
        id: FuncId(0),
        name: "copy_init".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let r = discharge_function(&f);
    let d = r
        .mem_decision(BlockId(0), 4, SafetyProperty::ValidRead)
        .expect("ValidRead obligation for the load");
    assert!(
        d.refutation.is_none(),
        "a load of memcpy-initialized bytes must not be refuted: {d:?}"
    );
}

/// `memcpy` within ONE buffer at overlapping (`gap < len`) vs. disjoint (`gap >= len`)
/// offsets. Overlap is UB for `memcpy` (that is what `memmove` is for).
fn same_buffer_memcpy(gap: u128, len: u128, use_move: bool) -> Function {
    let buf = RegId(0);
    let dstp = RegId(1);
    let srcp = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc { dst: buf, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 64), align: 1 });
    // dst = buf + 0, src = buf + gap (same base object).
    bb0.insts.push(Inst::PtrOffset { dst: dstp, base: Operand::Reg(buf), index: Operand::int(64, 0), elem: Type::int(8) });
    bb0.insts.push(Inst::PtrOffset { dst: srcp, base: Operand::Reg(buf), index: Operand::int(64, gap), elem: Type::int(8) });
    bb0.insts.push(Inst::MemIntrinsic {
        kind: if use_move { MemKind::Move } else { MemKind::Copy },
        dst: Operand::Reg(dstp),
        src: Some(Operand::Reg(srcp)),
        len: Operand::int(64, len),
    });
    Function { id: FuncId(0), name: "cp".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb0], entry: BlockId(0) }
}

#[test]
fn memcpy_overlap_is_refuted_disjoint_and_memmove_are_not() {
    let mi = 3; // the MemIntrinsic index
    // Overlapping memcpy (gap 4 < len 8) → a definite forbidden overlap, refuted.
    let r = discharge_function(&same_buffer_memcpy(4, 8, false));
    let d = r.mem_decision(BlockId(0), mi, SafetyProperty::NoForbiddenOverlap).expect("overlap obligation");
    assert!(!d.proven && d.refutation.is_some(), "overlapping memcpy is refuted: {d:?}");
    // Disjoint memcpy (gap 8 >= len 8) → proven no overlap.
    let r = discharge_function(&same_buffer_memcpy(8, 8, false));
    let d = r.mem_decision(BlockId(0), mi, SafetyProperty::NoForbiddenOverlap).expect("overlap obligation");
    assert!(d.proven, "disjoint memcpy has no overlap: {d:?}");
    // memmove permits overlap → carries no such obligation.
    let r = discharge_function(&same_buffer_memcpy(4, 8, true));
    assert!(r.mem_decision(BlockId(0), mi, SafetyProperty::NoForbiddenOverlap).is_none(), "memmove has no overlap obligation");
}

/// Allocate an 8-byte kernel buffer, optionally initialize it, then `copy_to_user`
/// (a `UserDrain`) its bytes. Copying the uninitialized buffer is an information
/// leak (`NoInfoLeak` refuted); initializing it first must clear the leak.
pub(super) fn info_leak_fn(init: bool) -> Function {
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 8,
    });
    if init {
        bb0.insts.push(Inst::MemIntrinsic {
            kind: MemKind::Set,
            dst: Operand::Reg(buf),
            src: None,
            len: Operand::int(64, 8),
        });
    }
    bb0.insts.push(Inst::MemIntrinsic {
        kind: MemKind::UserDrain,
        dst: Operand::Reg(buf),
        src: None,
        len: Operand::int(64, 8),
    });
    Function {
        id: FuncId(0),
        name: "drain".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}
