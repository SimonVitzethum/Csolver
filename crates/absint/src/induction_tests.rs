use super::*;
use csolver_ir::{BasicBlock, FuncId, Type};

/// `while i != 8 { …; i += 1 }`:
///   bb0: br bb1(0)
///   bb1(i): c = (i == 8); condbr c -> bb3 / bb2
///   bb2: ni = i + 1; br bb1(ni)
///   bb3: return
fn eq_exit() -> Function {
    let i = RegId(0);
    let c = RegId(1);
    let ni = RegId(2);
    let bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::int(64, 0)] },
    );
    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(3),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        },
    );
    bb1.params = vec![(i, Type::int(64))];
    bb1.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Eq, lhs: Operand::Reg(i), rhs: Operand::int(64, 8) },
    });
    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(ni)] },
    );
    bb2.insts.push(Inst::Assign {
        dst: ni,
        ty: Type::int(64),
        value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(i), rhs: Operand::int(64, 1) , flags: Default::default() },
    });
    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
    Function {
        id: FuncId(0),
        name: "eq_exit".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

#[test]
fn recognizes_equality_exit_induction() {
    let a = analyze_induction(&eq_exit());
    let vars = a.eq_exit_indvars(BlockId(1));
    assert_eq!(
        vars,
        &[EqExitIndVar { reg: RegId(0), bound: Operand::int(64, 8), stride: 1 }]
    );
}

/// `while iter != end { …; iter = iter + 1 (elem i32) }`:
///   bb0: br bb1(base)
///   bb1(iter): c = (iter == end); condbr c -> bb3 / bb2
///   bb2: nx = iter + 1 (i32); br bb1(nx)
///   bb3: return
fn ptr_walk() -> Function {
    let base = RegId(0);
    let end = RegId(1);
    let iter = RegId(2);
    let c = RegId(3);
    let nx = RegId(4);
    let bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(base)] },
    );
    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(3),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        },
    );
    bb1.params = vec![(iter, Type::ptr(Type::int(32)))];
    bb1.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Eq, lhs: Operand::Reg(iter), rhs: Operand::Reg(end) },
    });
    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(nx)] },
    );
    bb2.insts.push(Inst::PtrOffset {
        dst: nx,
        base: Operand::Reg(iter),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });
    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
    Function {
        id: FuncId(0),
        name: "ptr_walk".into(),
        params: vec![(base, Type::ptr(Type::int(32))), (end, Type::ptr(Type::int(32)))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

#[test]
fn recognizes_pointer_equality_exit_induction() {
    let a = analyze_induction(&ptr_walk());
    let vars = a.eq_exit_ptr_indvars(BlockId(1));
    assert_eq!(
        vars,
        &[PtrIndVar {
            reg: RegId(2),
            end: Operand::Reg(RegId(1)),
            elem: Type::int(32),
            stride_elems: 1,
            bottom_test: false,
        }]
    );
    // It is a pointer induction, not an integer one.
    assert!(a.eq_exit_indvars(BlockId(1)).is_empty());
}

/// The rotated (`-O`) bottom-test walk — one block, load then step then test:
///   bb0: empty = (base == end); condbr empty -> bb2 / bb1(base)
///   bb1(iter): x = load iter; nx = iter + 1; atend = (nx == end);
///              condbr atend -> bb2 / bb1(nx)
///   bb2: return
fn ptr_walk_bottom() -> Function {
    let base = RegId(0);
    let end = RegId(1);
    let empty = RegId(2);
    let iter = RegId(3);
    let x = RegId(4);
    let nx = RegId(5);
    let atend = RegId(6);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(empty),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(1),
            else_args: vec![Operand::Reg(base)],
        },
    );
    bb0.insts.push(Inst::Assign {
        dst: empty,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Eq, lhs: Operand::Reg(base), rhs: Operand::Reg(end) },
    });

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(atend),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(1),
            else_args: vec![Operand::Reg(nx)],
        },
    );
    bb1.params = vec![(iter, Type::ptr(Type::int(32)))];
    bb1.insts.push(Inst::Load {
        dst: x,
        ty: Type::int(32),
        ptr: Operand::Reg(iter),
        align: 4, volatile: false
    });
    bb1.insts.push(Inst::PtrOffset {
        dst: nx,
        base: Operand::Reg(iter),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });
    bb1.insts.push(Inst::Assign {
        dst: atend,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Eq, lhs: Operand::Reg(nx), rhs: Operand::Reg(end) },
    });

    let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
    Function {
        id: FuncId(0),
        name: "ptr_walk_bottom".into(),
        params: vec![(base, Type::ptr(Type::int(32))), (end, Type::ptr(Type::int(32)))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2],
        entry: BlockId(0),
    }
}

#[test]
fn recognizes_bottom_test_pointer_walk() {
    let a = analyze_induction(&ptr_walk_bottom());
    let vars = a.eq_exit_ptr_indvars(BlockId(1));
    assert_eq!(
        vars,
        &[PtrIndVar {
            reg: RegId(3),
            end: Operand::Reg(RegId(1)),
            elem: Type::int(32),
            stride_elems: 1,
            bottom_test: true,
        }]
    );
}

#[test]
fn ignores_a_less_than_exit() {
    // The same loop but with `i < 8` (not an equality exit) is not matched —
    // it is already handled by the interval domain, and the recogniser must
    // not claim it.
    let mut f = eq_exit();
    f.blocks[1].insts[0] = Inst::Assign {
        dst: RegId(1),
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Slt, lhs: Operand::Reg(RegId(0)), rhs: Operand::int(64, 8) },
    };
    // With `Slt`, the continue edge is the `then` (i < 8 true) — but our
    // fixture's `then` exits. Either way it is not an Eq/Ne exit.
    let a = analyze_induction(&f);
    assert!(a.eq_exit_indvars(BlockId(1)).is_empty());
}
