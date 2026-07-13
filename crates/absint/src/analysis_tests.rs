#![allow(clippy::unwrap_used, clippy::expect_used)]
use super::*;
use csolver_ir::{BasicBlock, FuncId, Type};

#[test]
fn straight_line_constant_folding() {
    // bb0: %0 = 3 ; %1 = %0 + 4 ; return
    let r0 = RegId(0);
    let r1 = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Assign {
        dst: r0,
        ty: Type::int(64),
        value: RValue::Use(Operand::int(64, 3)),
    });
    bb0.insts.push(Inst::Assign {
        dst: r1,
        ty: Type::int(64),
        value: RValue::Bin {
            op: BinOp::Add,
            lhs: Operand::Reg(r0),
            rhs: Operand::int(64, 4),
        flags: Default::default(),
        },
    });
    let f = Function {
        id: FuncId(0),
        name: "f".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let a = analyze_intervals(&f);
    let node = a.cfg().index_of(BlockId(0)).unwrap();
    let out = &a.solution.out_states[node];
    assert_eq!(out.get(r0), Interval::singleton(3));
    assert_eq!(out.get(r1), Interval::singleton(7));
}

/// A counting loop:
///   bb0:                br bb1(0)
///   bb1(i): %c = i<10 ; condbr %c -> bb2(i) / bb3
///   bb2(i): %n = i+1  ; br bb1(%n)
///   bb3:                return
fn counting_loop() -> Function {
    let i = RegId(0);
    let c = RegId(1);
    let i2 = RegId(2);
    let n = RegId(3);

    let bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br {
            target: BlockId(1),
            args: vec![Operand::int(64, 0)],
        },
    );

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
            op: csolver_ir::CmpOp::Ult,
            lhs: Operand::Reg(i),
            rhs: Operand::int(64, 10),
        },
    });

    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br {
            target: BlockId(1),
            args: vec![Operand::Reg(n)],
        },
    );
    bb2.params = vec![(i2, Type::int(64))];
    bb2.insts.push(Inst::Assign {
        dst: n,
        ty: Type::int(64),
        value: RValue::Bin {
            op: BinOp::Add,
            lhs: Operand::Reg(i2),
            rhs: Operand::int(64, 1),
        flags: Default::default(),
        },
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "count".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

#[test]
fn condition_eval_is_trivalent_and_sound() {
    use csolver_ir::Condition;
    // bb0: %0 = 3 ; safety-check(%0 < N) ; return
    let r0 = RegId(0);
    let mk = |n: u128| {
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Assign {
            dst: r0,
            ty: Type::int(64),
            value: RValue::Use(Operand::int(64, 3)),
        });
        bb0.insts.push(Inst::SafetyCheck {
            property: csolver_core::SafetyProperty::InBounds,
            condition: Condition::Cmp {
                op: CmpOp::Ult,
                lhs: Operand::Reg(r0),
                rhs: Operand::int(64, n),
            },
            note: "idx < n".into(),
        });
        Function {
            id: FuncId(0),
            name: "f".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    };
    // The SafetyCheck is instruction index 1 in bb0.
    let f_true = mk(4);
    let a = analyze_intervals(&f_true);
    let cond = match &f_true.block(BlockId(0)).unwrap().insts[1] {
        Inst::SafetyCheck { condition, .. } => condition.clone(),
        _ => unreachable!(),
    };
    assert_eq!(a.eval_condition(&f_true, BlockId(0), 1, &cond), Trivalent::True);

    let f_false = mk(2);
    let a2 = analyze_intervals(&f_false);
    let cond2 = match &f_false.block(BlockId(0)).unwrap().insts[1] {
        Inst::SafetyCheck { condition, .. } => condition.clone(),
        _ => unreachable!(),
    };
    assert_eq!(a2.eval_condition(&f_false, BlockId(0), 1, &cond2), Trivalent::False);
}

#[test]
fn negative_constant_is_interpreted_signed() {
    use csolver_ir::Condition;
    // bb0: safety-check(  (i64)-1  >=  0  ) ; return
    // The constant -1 must enter the interval domain as -1, so `-1 >= 0`
    // evaluates to False (a real violation) — not True (a former false PASS).
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::SafetyCheck {
        property: csolver_core::SafetyProperty::InBounds,
        condition: Condition::Cmp {
            op: CmpOp::Sge,
            lhs: Operand::int(64, u64::MAX as u128), // bit pattern of -1
            rhs: Operand::int(64, 0),
        },
        note: "-1 >= 0".into(),
    });
    let f = Function {
        id: FuncId(0),
        name: "neg".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let a = analyze_intervals(&f);
    let cond = match &f.block(BlockId(0)).unwrap().insts[0] {
        Inst::SafetyCheck { condition, .. } => condition.clone(),
        _ => unreachable!(),
    };
    assert_eq!(a.eval_condition(&f, BlockId(0), 0, &cond), Trivalent::False);
}

#[test]
fn loop_terminates_with_sound_invariant() {
    // The analysis must terminate (widening) and infer a sound invariant. Even
    // with guard refinement on the body edge, the *loop-header* value widens to
    // [0, +inf] (widening subsumes the refined back-edge without narrowing) — a
    // sound over-approximation: i is always >= 0.
    let f = counting_loop();
    let a = analyze_intervals(&f);
    let header_i = a.entry_interval(BlockId(1), RegId(0));
    assert!(!header_i.is_bottom(), "header must be reachable");
    assert!(header_i.is_at_least(0), "i >= 0 is a sound invariant, got {header_i}");
    // It is NOT bounded above at the header (widening, no narrowing there).
    assert!(!header_i.is_strictly_below(10));
}

/// An **irreducible** two-entry cycle whose SCC has no natural-loop header, with a
/// counter that grows around it. The natural-loop detector finds no header here, so
/// without the engine's revisit-count widening safety net the fixpoint would ascend
/// forever (the value grows by a constant each traversal). This test must simply
/// *terminate*; it is the regression guard for the kernel functions (`__unmap_range`
/// et al.) whose optimized CFGs hung the interval analysis before the fix.
///
///   bb0(sel):            condbr sel -> bb1(0) / bb2(0)   ← two entries into {bb1,bb2}
///   bb1(i):   n1 = i+1 ; br bb2(n1)
///   bb2(j):   c = j<1e9; n2 = j+1 ; condbr c -> bb1(n2) / bb3
///   bb3:                 return
#[test]
fn irreducible_cycle_terminates_via_fallback_widening() {
    let sel = RegId(0);
    let i = RegId(1);
    let n1 = RegId(2);
    let j = RegId(3);
    let n2 = RegId(4);
    let c = RegId(5);

    let bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(sel),
            then_blk: BlockId(1),
            then_args: vec![Operand::int(64, 0)],
            else_blk: BlockId(2),
            else_args: vec![Operand::int(64, 0)],
        },
    );

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::Br { target: BlockId(2), args: vec![Operand::Reg(n1)] },
    );
    bb1.params = vec![(i, Type::int(64))];
    bb1.insts.push(Inst::Assign {
        dst: n1,
        ty: Type::int(64),
        value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(i), rhs: Operand::int(64, 1) , flags: Default::default() },
    });

    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(1),
            then_args: vec![Operand::Reg(n2)],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb2.params = vec![(j, Type::int(64))];
    bb2.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: RValue::Cmp {
            op: CmpOp::Slt,
            lhs: Operand::Reg(j),
            rhs: Operand::int(64, 1_000_000_000),
        },
    });
    bb2.insts.push(Inst::Assign {
        dst: n2,
        ty: Type::int(64),
        value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(j), rhs: Operand::int(64, 1) , flags: Default::default() },
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    let f = Function {
        id: FuncId(0),
        name: "irreducible".into(),
        params: vec![(sel, Type::Bool)],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    };

    // The assertion is that this returns at all (no hang). The counter is a sound
    // over-approximation: reachable and non-negative at the cycle entries.
    let a = analyze_intervals(&f);
    let iv = a.entry_interval(BlockId(1), RegId(1));
    assert!(!iv.is_bottom(), "the irreducible cycle head must be reachable");
    assert!(iv.is_at_least(0), "the counter is >= 0, got {iv}");
}
