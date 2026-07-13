use super::*;

/// `ptr_walk_loop()`: the fully-optimized iterator shape — walk a `[i32; 8]` by
/// a moving pointer until it reaches the end pointer.
///
/// ```text
///   bb0: buf = alloc i32 * 8 ; end = buf + 8 ; br bb1(buf)
///   bb1(iter): c = (iter == end) ; condbr c -> bb3 / bb2
///   bb2: x = load iter ; nx = iter + 1 ; br bb1(nx)
///   bb3: return
/// ```
///
/// The loop exits on the **pointer** equality `iter == end`; the equality-exit
/// pointer-induction analysis keeps `iter`'s region provenance with a bounded,
/// stride-aligned offset (`0 ≤ o ≤ end_off ≤ size`, `o ≡ 0 mod 4`), and the guard
/// `iter != end` then proves the `load iter` in bounds → PASS.
pub fn ptr_walk_loop() -> Function {
    ptr_walk_to(8)
}

/// As [`ptr_walk_loop`] but the end pointer is past the buffer (`buf + 16` over a
/// `[i32; 8]`): the walk would read out of bounds, so the load must NOT be
/// proved PASS. The `end_off ≤ size` side-condition fails, so the pointer keeps
/// opaque (the bounded offset is never installed) and the access stays UNKNOWN.
pub fn ptr_walk_loop_oob() -> Function {
    ptr_walk_to(16)
}

fn ptr_walk_to(end_elems: u128) -> Function {
    let buf = RegId(0);
    let end = RegId(1);
    let iter = RegId(2);
    let c = RegId(3);
    let nx = RegId(4);
    let x = RegId(5);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(buf)] },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 8),
        align: 4,
    });
    bb0.insts.push(Inst::PtrOffset {
        dst: end,
        base: Operand::Reg(buf),
        index: Operand::int(64, end_elems),
        elem: Type::int(32),
    });

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
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Eq,
            lhs: Operand::Reg(iter),
            rhs: Operand::Reg(end),
        },
    });

    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(nx)] },
    );
    bb2.insts.push(Inst::Load {
        dst: x,
        ty: Type::int(32),
        ptr: Operand::Reg(iter),
        align: 4, volatile: false
    });
    bb2.insts.push(Inst::PtrOffset {
        dst: nx,
        base: Operand::Reg(iter),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "ptr_walk_loop".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

/// `ptr_walk_bottom_loop(n)`: the **rotated** (`-O`) iterator shape — the load
/// precedes the `next == end` exit check, guarded by an `is_empty` preheader
/// test. Walks an `alloc [i32; n]` of a *symbolic* length.
///
/// ```text
///   bb0: buf = alloc i32 * n ; end = buf + n ; empty = (buf == end)
///        condbr empty -> bb2 / bb1(buf)
///   bb1(iter): x = load iter ; nx = iter + 1 ; atend = (nx == end)
///              condbr atend -> bb2 / bb1(nx)
///   bb2: return
/// ```
///
/// The bound `iter + stride ≤ end` holds because the loop is entered only when
/// `buf != end` (the preheader guard, which the engine reads from the path
/// condition to prove the base case). Verifies PASS.
pub fn ptr_walk_bottom_loop() -> Function {
    ptr_walk_bottom_impl(true)
}

/// As [`ptr_walk_bottom_loop`] but **without** the `is_empty` preheader guard:
/// the load precedes the exit check, so on an empty range (`n == 0`) it would
/// read out of bounds. The base case `0 + stride ≤ end` is then unprovable, so
/// the bounded offset is never installed and the load is not proved PASS — the
/// soundness boundary of the rotated form.
pub fn ptr_walk_bottom_unguarded() -> Function {
    ptr_walk_bottom_impl(false)
}

fn ptr_walk_bottom_impl(guard: bool) -> Function {
    let n = RegId(0);
    let buf = RegId(1);
    let end = RegId(2);
    let empty = RegId(3);
    let iter = RegId(4);
    let x = RegId(5);
    let nx = RegId(6);
    let atend = RegId(7);

    let bb0_term = if guard {
        Terminator::CondBr {
            cond: Operand::Reg(empty),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(1),
            else_args: vec![Operand::Reg(buf)],
        }
    } else {
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(buf)] }
    };
    let mut bb0 = BasicBlock::new(BlockId(0), bb0_term);
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 4,
    });
    bb0.insts.push(Inst::PtrOffset {
        dst: end,
        base: Operand::Reg(buf),
        index: Operand::Reg(n),
        elem: Type::int(32),
    });
    if guard {
        bb0.insts.push(Inst::Assign {
            dst: empty,
            ty: Type::Bool,
            value: csolver_ir::RValue::Cmp {
                op: CmpOp::Eq,
                lhs: Operand::Reg(buf),
                rhs: Operand::Reg(end),
            },
        });
    }

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
    bb1.insts.push(Inst::Load { dst: x, ty: Type::int(32), ptr: Operand::Reg(iter), align: 4 , volatile: false});
    bb1.insts.push(Inst::PtrOffset {
        dst: nx,
        base: Operand::Reg(iter),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });
    bb1.insts.push(Inst::Assign {
        dst: atend,
        ty: Type::Bool,
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Eq,
            lhs: Operand::Reg(nx),
            rhs: Operand::Reg(end),
        },
    });

    let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "ptr_walk_bottom".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2],
        entry: BlockId(0),
    }
}
