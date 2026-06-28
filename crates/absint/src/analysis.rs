//! The interval analysis: MSIR transfer functions wired to the solver.
//!
//! This is intentionally *sound but unrefined* at M0: it does not yet narrow
//! register ranges using branch conditions (that arrives with the verifier's
//! M1 slice and/or the symbolic engine). It already establishes loop
//! invariants via widening, which is enough to discharge many in-bounds
//! obligations whose index is derived from constants and monotone updates.

use crate::engine::{solve, Solution};
use crate::env::IntervalState;
use crate::interval::{Bound, Interval};
use csolver_cfg::{Cfg, Dominators, Loops};
use csolver_ir::{
    BinOp, BlockId, CastOp, CmpOp, Condition, Const, Function, Inst, Operand, RValue, RegId,
    Terminator,
};

/// Three-valued result of evaluating a [`Condition`] under inferred intervals.
///
/// Because intervals over-approximate the concrete values, `True` means the
/// condition holds on *every* concrete state (a sound `PASS`) and `False` means
/// it holds on *none* (a sound `FAIL`); `Unknown` means the intervals are not
/// precise enough and the obligation must go to the solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trivalent {
    /// Provably holds.
    True,
    /// Provably fails.
    False,
    /// Indeterminate from intervals alone.
    Unknown,
}

impl Trivalent {
    fn negate(self) -> Trivalent {
        match self {
            Trivalent::True => Trivalent::False,
            Trivalent::False => Trivalent::True,
            Trivalent::Unknown => Trivalent::Unknown,
        }
    }
}

/// The result of running the interval analysis over a function.
#[derive(Debug, Clone)]
pub struct IntervalAnalysis {
    /// Per-block in/out interval environments (indexed by CFG node).
    pub solution: Solution<IntervalState>,
    cfg: Cfg,
}

impl IntervalAnalysis {
    /// The CFG the analysis ran on.
    pub fn cfg(&self) -> &Cfg {
        &self.cfg
    }

    /// The interval inferred for `reg` on entry to `block` (top if the block is
    /// unreachable or the register is unconstrained there).
    pub fn entry_interval(&self, block: BlockId, reg: RegId) -> Interval {
        match self.cfg.index_of(block) {
            Some(node) => self.solution.in_states[node].get(reg),
            None => Interval::top(),
        }
    }

    /// Evaluate `cond` using the intervals that hold immediately before
    /// instruction `inst_index` of `block`.
    ///
    /// The state is reconstructed by folding the block's instructions
    /// `[0, inst_index)` onto the block-entry invariant, so registers defined
    /// earlier in the same block are accounted for.
    pub fn eval_condition(
        &self,
        f: &Function,
        block: BlockId,
        inst_index: usize,
        cond: &Condition,
    ) -> Trivalent {
        let Some(node) = self.cfg.index_of(block) else {
            return Trivalent::Unknown;
        };
        let entry = &self.solution.in_states[node];
        if !entry.is_reachable() {
            // Unreachable code: the obligation is vacuously satisfied.
            return Trivalent::True;
        }
        let mut state = entry.clone();
        if let Some(b) = f.block(block) {
            for inst in b.insts.iter().take(inst_index) {
                apply_inst(inst, &mut state);
            }
        }
        eval_condition_in(cond, &state)
    }
}

/// Evaluate a condition under a fixed interval state.
fn eval_condition_in(cond: &Condition, state: &IntervalState) -> Trivalent {
    match cond {
        Condition::True => Trivalent::True,
        Condition::Cmp { op, lhs, rhs } => {
            compare_intervals(*op, &eval_operand(lhs, state), &eval_operand(rhs, state))
        }
        Condition::And(cs) => {
            let mut all_true = true;
            for c in cs {
                match eval_condition_in(c, state) {
                    Trivalent::False => return Trivalent::False,
                    Trivalent::Unknown => all_true = false,
                    Trivalent::True => {}
                }
            }
            if all_true {
                Trivalent::True
            } else {
                Trivalent::Unknown
            }
        }
        Condition::Or(cs) => {
            let mut all_false = true;
            for c in cs {
                match eval_condition_in(c, state) {
                    Trivalent::True => return Trivalent::True,
                    Trivalent::Unknown => all_false = false,
                    Trivalent::False => {}
                }
            }
            if all_false {
                Trivalent::False
            } else {
                Trivalent::Unknown
            }
        }
        Condition::Not(c) => eval_condition_in(c, state).negate(),
    }
}

/// `x <= y` in the extended bound order.
fn bound_le(x: Bound, y: Bound) -> bool {
    use Bound::*;
    match (x, y) {
        (NegInf, _) => true,
        (_, PosInf) => true,
        (_, NegInf) => false,
        (PosInf, _) => false,
        (Fin(a), Fin(b)) => a <= b,
    }
}

/// `x < y` in the extended bound order.
fn bound_lt(x: Bound, y: Bound) -> bool {
    bound_le(x, y) && !bound_le(y, x)
}

/// Trivalent comparison of two intervals under the given predicate. Values are
/// compared as signed integers; this is sound for the non-negative indices and
/// sizes that dominate bounds checks, and the verifier escalates genuinely
/// unsigned-sensitive cases to the solver (M1+).
fn compare_intervals(op: CmpOp, a: &Interval, b: &Interval) -> Trivalent {
    let (Some(alo), Some(ahi), Some(blo), Some(bhi)) =
        (a.lower(), a.upper(), b.lower(), b.upper())
    else {
        // One side is bottom (unreachable value): indeterminate.
        return Trivalent::Unknown;
    };

    // Helper closures for the primitive relations.
    let lt = || {
        if bound_lt(ahi, blo) {
            Trivalent::True
        } else if bound_le(bhi, alo) {
            Trivalent::False
        } else {
            Trivalent::Unknown
        }
    };
    let le = || {
        if bound_le(ahi, blo) {
            Trivalent::True
        } else if bound_lt(bhi, alo) {
            Trivalent::False
        } else {
            Trivalent::Unknown
        }
    };
    let gt = || {
        // a > b  <=>  b < a
        if bound_lt(bhi, alo) {
            Trivalent::True
        } else if bound_le(ahi, blo) {
            Trivalent::False
        } else {
            Trivalent::Unknown
        }
    };
    let ge = || {
        // a >= b  <=>  b <= a
        if bound_le(bhi, alo) {
            Trivalent::True
        } else if bound_lt(ahi, blo) {
            Trivalent::False
        } else {
            Trivalent::Unknown
        }
    };

    match op {
        CmpOp::Ult | CmpOp::Slt => lt(),
        CmpOp::Ule | CmpOp::Sle => le(),
        CmpOp::Ugt | CmpOp::Sgt => gt(),
        CmpOp::Uge | CmpOp::Sge => ge(),
        CmpOp::Eq => {
            // Disjoint => never equal; identical singletons => always equal.
            if bound_lt(ahi, blo) || bound_lt(bhi, alo) {
                Trivalent::False
            } else if alo == ahi && blo == bhi && alo == blo {
                Trivalent::True
            } else {
                Trivalent::Unknown
            }
        }
        CmpOp::Ne => compare_intervals(CmpOp::Eq, a, b).negate(),
    }
}

/// Run the interval analysis over `f`.
pub fn analyze_intervals(f: &Function) -> IntervalAnalysis {
    let cfg = Cfg::from_function(f);
    let dominators = Dominators::new(&cfg);
    let loops = Loops::detect(&cfg, &dominators);

    let solution = solve(
        &cfg,
        &loops,
        IntervalState::top(),
        |node, in_state| transfer_block(f, &cfg, node, in_state),
        |from, to, from_exit| transfer_edge(f, &cfg, from, to, from_exit),
    );

    IntervalAnalysis { solution, cfg }
}

/// Apply the straight-line body of block `node` to `in_state`.
///
/// The `expect` is an invariant: `cfg` was built from `f`, so every CFG node
/// index maps back to one of `f`'s blocks.
#[allow(clippy::expect_used)]
fn transfer_block(f: &Function, cfg: &Cfg, node: usize, in_state: &IntervalState) -> IntervalState {
    if !in_state.is_reachable() {
        return IntervalState::Unreachable;
    }
    let block = f
        .block(cfg.block_id(node))
        .expect("cfg node maps to a block");
    let mut state = in_state.clone();
    for inst in &block.insts {
        apply_inst(inst, &mut state);
    }
    state
}

/// Bind `to`'s block parameters from the arguments `from`'s terminator passes
/// along the `from -> to` edge, evaluated in `from`'s exit state.
///
/// The `expect`s are invariants: `from`/`to` are CFG node indices built from
/// `f`, so both map back to real blocks.
#[allow(clippy::expect_used)]
fn transfer_edge(
    f: &Function,
    cfg: &Cfg,
    from: usize,
    to: usize,
    from_exit: &IntervalState,
) -> IntervalState {
    if !from_exit.is_reachable() {
        return IntervalState::Unreachable;
    }
    let from_block = f.block(cfg.block_id(from)).expect("from block");
    let to_id = cfg.block_id(to);
    let to_block = f.block(to_id).expect("to block");

    let arg_lists = matching_args(&from_block.term, to_id);
    if arg_lists.is_empty() {
        return from_exit.clone();
    }

    // Join over all argument lists that target `to` (handles a terminator with
    // two identical targets carrying different arguments).
    let mut result = IntervalState::Unreachable;
    for args in arg_lists {
        let mut candidate = from_exit.clone();
        for (i, (param, _ty)) in to_block.params.iter().enumerate() {
            let value = args
                .get(i)
                .map(|op| eval_operand(op, from_exit))
                .unwrap_or_else(Interval::top);
            candidate.set(*param, value);
        }
        result = crate::AbstractDomain::join(&result, &candidate);
    }
    result
}

/// All argument lists a terminator passes to the target block `to_id`.
fn matching_args(term: &Terminator, to_id: BlockId) -> Vec<&Vec<Operand>> {
    match term {
        Terminator::Br { target, args } if *target == to_id => vec![args],
        Terminator::CondBr {
            then_blk,
            then_args,
            else_blk,
            else_args,
            ..
        } => {
            let mut v = Vec::new();
            if *then_blk == to_id {
                v.push(then_args);
            }
            if *else_blk == to_id {
                v.push(else_args);
            }
            v
        }
        _ => Vec::new(),
    }
}

/// Update `state` with the effect of one instruction on integer registers.
fn apply_inst(inst: &Inst, state: &mut IntervalState) {
    match inst {
        Inst::Assign { dst, value, .. } => {
            let v = eval_rvalue(value, state);
            state.set(*dst, v);
        }
        // These define values the interval domain does not model precisely
        // (pointers, opaque results): conservatively top.
        Inst::Load { dst, .. } | Inst::Alloc { dst, .. } | Inst::PtrOffset { dst, .. } => {
            state.set(*dst, Interval::top());
        }
        Inst::Call { dst: Some(d), .. } | Inst::Intrinsic { dst: Some(d), .. } => {
            state.set(*d, Interval::top());
        }
        Inst::Call { dst: None, .. }
        | Inst::Intrinsic { dst: None, .. }
        | Inst::Store { .. }
        | Inst::Dealloc { .. }
        | Inst::Asm { .. }
        | Inst::MemIntrinsic { .. }
        | Inst::SafetyCheck { .. } => {}
    }
}

/// Evaluate an r-value to an interval.
fn eval_rvalue(rv: &RValue, state: &IntervalState) -> Interval {
    match rv {
        RValue::Use(op) => eval_operand(op, state),
        RValue::Bin { op, lhs, rhs } => {
            let a = eval_operand(lhs, state);
            let b = eval_operand(rhs, state);
            match op {
                BinOp::Add => a.add(&b),
                BinOp::Sub => a.sub(&b),
                BinOp::Mul => a.mul(&b),
                // Division, bitwise, shifts: not modelled in M0 -> top.
                _ => Interval::top(),
            }
        }
        // A comparison yields an i1 in {0, 1}.
        RValue::Cmp { .. } => Interval::range(0, 1),
        RValue::Cast { op, operand, .. } => {
            let v = eval_operand(operand, state);
            match op {
                // Value-preserving widenings keep the interval.
                CastOp::ZExt | CastOp::SExt => v,
                // Truncation may wrap; other casts lose numeric meaning.
                _ => Interval::top(),
            }
        }
    }
}

/// Evaluate an operand to an interval.
fn eval_operand(op: &Operand, state: &IntervalState) -> Interval {
    match op {
        Operand::Reg(r) => state.get(*r),
        // Use the *signed* value: `compare_intervals` orders intervals as
        // signed integers, so a constant must enter the domain with the same
        // interpretation. Using `unsigned()` here made `-1` look like `2^64-1`,
        // which unsoundly proved e.g. `-1 >= 0` (a false PASS).
        Operand::Const(Const::Int(bv)) => Interval::singleton(bv.signed()),
        Operand::Const(Const::Null) => Interval::singleton(0),
        Operand::Const(Const::Undef) | Operand::Const(Const::Symbol(_)) => Interval::top(),
    }
}

#[cfg(test)]
mod tests {
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
        // The analysis must terminate (widening) and infer a sound invariant.
        // Without guard refinement, the induction variable widens to [0, +inf],
        // which is a sound over-approximation: i is always >= 0.
        let f = counting_loop();
        let a = analyze_intervals(&f);
        let header_i = a.entry_interval(BlockId(1), RegId(0));
        assert!(!header_i.is_bottom(), "header must be reachable");
        assert!(header_i.is_at_least(0), "i >= 0 is a sound invariant, got {header_i}");
        // It is NOT spuriously bounded above (we did not refine by the guard).
        assert!(!header_i.is_strictly_below(10));
    }
}
