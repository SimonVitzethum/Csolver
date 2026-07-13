//! A built-in MSIR module used by `solver demo` to exercise the full pipeline
//! (MSIR → CFG → interval analysis → verifier → report) without any frontend.

use csolver_core::{RegionKind, SafetyProperty};
use csolver_ir::{
    BasicBlock, BlockId, CmpOp, Condition, FuncId, Function, Inst, Module, Operand, RegId,
    Terminator, Type,
};

/// Build a module exercising every verdict path: an interval PASS + symbolic
/// UNKNOWN, a guarded access proved by symbolic execution, and a constant OOB.
pub(crate) fn build_demo_module() -> Module {
    let mut m = Module::new("demo");
    m.functions.push(bounded_get());
    m.functions.push(guarded_get());
    m.functions.push(safe_buffer_store());
    m.functions.push(loop_array_store());
    m.functions.push(indirect_store());
    m.functions.push(wrapper_first());
    m.functions.push(interproc_caller());
    m.functions.push(oob_write());
    m
}

/// `first(b: *i32) -> *i32 { b + 0 }` — a pointer-returning wrapper.
fn wrapper_first() -> Function {
    let b = RegId(0);
    let q = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(q))));
    bb0.insts.push(Inst::PtrOffset {
        dst: q,
        base: Operand::Reg(b),
        index: Operand::int(64, 0),
        elem: Type::int(32),
    });
    Function {
        id: FuncId(6),
        name: "first".into(),
        params: vec![(b, Type::ptr(Type::int(32)))],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `interproc_caller()`: allocate, get a pointer from `first`, dereference it.
/// The summary for `first` preserves provenance, so the deref proves.
fn interproc_caller() -> Function {
    let buf = RegId(0);
    let p = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 8),
        align: 4,
    });
    bb0.insts.push(Inst::Call {
        dst: Some(p),
        callee: csolver_ir::Callee::Direct(FuncId(6)),
        args: vec![Operand::Reg(buf)],
        ret_ty: Type::ptr(Type::int(32)),
        ret_ref: None,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    });
    Function {
        id: FuncId(7),
        name: "interproc_caller".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `indirect_store()`: store a pointer into a slot, load it back, and write
/// through it. The alias-aware symbolic heap preserves provenance across the
/// round-trip, so the final dereference is fully proved.
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
        id: FuncId(5),
        name: "indirect_store".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `loop_array_store(n)`: `for i in 0..n { buf[i] = 0 }` over a freshly
/// allocated `[i32; n]` — every in-loop memory obligation is proved using the
/// interval invariant (`i >= 0`) plus the loop guard (`i < n`).
fn loop_array_store() -> Function {
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
        value: csolver_ir::RValue::Cmp {
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
        value: csolver_ir::RValue::Bin {
            op: csolver_ir::BinOp::Add,
            lhs: Operand::Reg(j),
            rhs: Operand::int(64, 1),
            flags: Default::default(),
        },
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(4),
        name: "loop_array_store".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

/// `safe_buffer_store(i, n)`: alloc `n` i32s, then store into `buf[i]` only
/// under `0 <= i && i < n` — every memory obligation is proved symbolically.
fn safe_buffer_store() -> Function {
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
        value: csolver_ir::RValue::Cmp {
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
        value: csolver_ir::RValue::Cmp {
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
        id: FuncId(3),
        name: "safe_buffer_store".into(),
        params: vec![(i, Type::int(64)), (n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

/// `guarded_get(i, len)`: `a[i]` only on the branch where `i < len` holds.
/// Intervals leave it UNKNOWN; symbolic execution proves it (PASS).
fn guarded_get() -> Function {
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
        value: csolver_ir::RValue::Cmp {
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
        note: "a[i] under guard i < len".into(),
    });

    let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));

    Function {
        id: FuncId(2),
        name: "guarded_get".into(),
        params: vec![(i, Type::int(64)), (len, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2],
        entry: BlockId(0),
    }
}

/// `bounded_get(i)`: a constant in-bounds check (PASS) plus a symbolic one that
/// the interval domain cannot decide (UNKNOWN) → function verdict UNKNOWN.
fn bounded_get() -> Function {
    let i = RegId(0);
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));

    // Provable: 3 < 8.
    bb.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::int(64, 3),
            rhs: Operand::int(64, 8),
        },
        note: "constant index 3 into len-8 buffer".into(),
    });
    // Unknown: i < 8, where i is an unconstrained parameter.
    bb.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::Reg(i),
            rhs: Operand::int(64, 8),
        },
        note: "parameter index i into len-8 buffer".into(),
    });

    Function {
        id: FuncId(0),
        name: "bounded_get".into(),
        params: vec![(i, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb],
        entry: BlockId(0),
    }
}

/// `oob_write()`: a constant out-of-bounds check (FAIL) → function verdict FAIL.
fn oob_write() -> Function {
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::int(64, 10),
            rhs: Operand::int(64, 8),
        },
        note: "constant index 10 into len-8 buffer".into(),
    });
    Function {
        id: FuncId(1),
        name: "oob_write".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb],
        entry: BlockId(0),
    }
}
