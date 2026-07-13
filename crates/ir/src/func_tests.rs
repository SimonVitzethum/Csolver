#![allow(clippy::unwrap_used, clippy::expect_used)]
use super::*;
use crate::inst::{CmpOp, Const, RValue};
use csolver_core::SafetyProperty;

/// Build a tiny function:
///   bb0: %2 = icmp ult %0, %1 ; safety-check in_bounds ; condbr -> bb1/bb2
///   bb1: return %0
///   bb2: unreachable
fn sample() -> Function {
    let r0 = RegId(0);
    let r1 = RegId(1);
    let r2 = RegId(2);
    let bb0 = {
        let mut b = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(r2),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(2),
                else_args: vec![],
            },
        );
        b.insts.push(Inst::Assign {
            dst: r2,
            ty: Type::Bool,
            value: RValue::Cmp {
                op: CmpOp::Ult,
                lhs: Operand::Reg(r0),
                rhs: Operand::Reg(r1),
            },
        });
        b.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: crate::inst::Condition::Cmp {
                op: CmpOp::Ult,
                lhs: Operand::Reg(r0),
                rhs: Operand::Reg(r1),
            },
            note: "index < len".into(),
        });
        b
    };
    let bb1 = BasicBlock::new(BlockId(1), Terminator::Return(Some(Operand::Reg(r0))));
    let bb2 = BasicBlock::new(BlockId(2), Terminator::Unreachable);

    Function {
        id: FuncId(0),
        name: "sample".into(),
        params: vec![(r0, Type::int(64)), (r1, Type::int(64))],
        ret_ty: Type::int(64),
        blocks: vec![bb0, bb1, bb2],
        entry: BlockId(0),
    }
}

#[test]
fn successors_and_lookup() {
    let f = sample();
    assert_eq!(f.block_count(), 3);
    let entry = f.block(f.entry).unwrap();
    assert_eq!(entry.successors(), vec![BlockId(1), BlockId(2)]);
    assert_eq!(f.block(BlockId(1)).unwrap().successors(), vec![]);
}

#[test]
fn defined_registers() {
    let f = sample();
    let defs: Vec<_> = f
        .block(BlockId(0))
        .unwrap()
        .insts
        .iter()
        .filter_map(Inst::defined_reg)
        .collect();
    assert_eq!(defs, vec![RegId(2)]);
}

#[test]
fn const_null_is_distinct() {
    assert_ne!(Const::Null, Const::Undef);
}

/// Cross-file linking resolves a call that crossed a translation-unit boundary:
/// file A calls `foo` (a `Callee::Symbol`, opaque per-TU); file B defines `foo`.
/// After `merge_modules`, A's call points at B's definition, and internal-linkage
/// functions keep their own identity (never resolved by name).
fn one_fn(name: &str, call: Option<Callee>, internal: bool) -> Module {
    let mut m = Module::new("tu");
    let mut b = BasicBlock::new(BlockId(0), Terminator::Return(None));
    if let Some(callee) = call {
        b.insts.push(Inst::Call {
            dst: None,
            callee,
            args: vec![],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
    }
    let f = Function {
        id: FuncId(0),
        name: name.into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![b],
        entry: BlockId(0),
    };
    if internal {
        m.internal.insert(f.id);
    }
    m.functions.push(f);
    m
}

#[test]
fn merge_resolves_cross_file_call_by_name() {
    let a = one_fn("caller", Some(Callee::Symbol("foo".into())), false);
    let b = one_fn("foo", None, false);
    let merged = merge_modules(vec![a, b], "prog");
    assert_eq!(merged.functions.len(), 2);
    let caller = merged.functions.iter().find(|f| f.name == "caller").unwrap();
    let foo = merged.functions.iter().find(|f| f.name == "foo").unwrap();
    let Inst::Call { callee, .. } = &caller.blocks[0].insts[0] else {
        panic!("expected a call");
    };
    assert_eq!(*callee, Callee::Direct(foo.id), "the cross-file call now resolves to foo");
}

#[test]
fn merge_keeps_internal_functions_unresolved_by_name() {
    // Two files each with a `static helper` — same name, distinct functions. A call to
    // an undefined external `helper` must stay opaque, never bind to a file-local static.
    let a = one_fn("helper", None, true);
    let b = one_fn("helper", None, true);
    let caller = one_fn("c", Some(Callee::Symbol("helper".into())), false);
    let merged = merge_modules(vec![a, b, caller], "prog");
    assert_eq!(merged.functions.len(), 3);
    let c = merged.functions.iter().find(|f| f.name == "c").unwrap();
    let Inst::Call { callee, .. } = &c.blocks[0].insts[0] else {
        panic!("expected a call");
    };
    assert_eq!(*callee, Callee::Symbol("helper".into()), "internal names never resolve");
}
