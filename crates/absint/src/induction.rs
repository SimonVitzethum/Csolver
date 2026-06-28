//! Equality-exit induction recognition — stage 1 of proving the `iter != end`
//! / pointer-walk loop.
//!
//! It finds, per loop header, an integer induction variable `v` that
//!   1. is a header block-parameter incremented by a positive constant stride
//!      on the (single) back-edge (`v := v + c`, `c > 0`), and
//!   2. governs the loop exit through an **equality** test: the header branches
//!      on `v == bound`, continuing the loop exactly while `v != bound`.
//!
//! This is the shape an `==`/`!=`-bounded counting loop takes, and the integer
//! precursor of the pointer walk (`iter != end`). The recogniser is purely
//! syntactic and **conservative**: anything it is unsure about yields no
//! induction variable. The actual bound `start ≤ v ≤ bound` is asserted by the
//! symbolic engine only after it has **solver-checked** the soundness
//! side-conditions (`0 ≤ start ≤ bound ≤ isize::MAX`, and `stride | bound −
//! start` so `bound` lies on the induction's grid — otherwise the counter would
//! overshoot `bound` and the bound would be unsound). Recognition alone never
//! authorises a fact; it only proposes one to verify.

use csolver_cfg::{Cfg, Dominators, Loops};
use csolver_ir::{
    BinOp, BlockId, CmpOp, Const, Function, Inst, Operand, RValue, RegId, Terminator,
};
use std::collections::HashMap;

/// A recognized equality-exit induction variable at a loop header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EqExitIndVar {
    /// The induction register (a header block-parameter).
    pub reg: RegId,
    /// The value `v` is compared against for the loop exit: the loop runs while
    /// `v != bound` and exits when `v == bound`.
    pub bound: Operand,
    /// The per-iteration increment (`> 0`; the loop counts up toward `bound`).
    pub stride: i128,
}

/// Per-loop-header equality-exit induction variables.
#[derive(Debug, Clone, Default)]
pub struct InductionAnalysis {
    by_header: HashMap<BlockId, Vec<EqExitIndVar>>,
}

impl InductionAnalysis {
    /// The equality-exit induction variables governing `header`'s loop.
    pub fn eq_exit_indvars(&self, header: BlockId) -> &[EqExitIndVar] {
        self.by_header.get(&header).map(Vec::as_slice).unwrap_or(&[])
    }
}

/// Recognize equality-exit induction variables in every natural loop of `f`.
pub fn analyze_induction(f: &Function) -> InductionAnalysis {
    let cfg = Cfg::from_function(f);
    let doms = Dominators::new(&cfg);
    let loops = Loops::detect(&cfg, &doms);
    let mut by_header = HashMap::new();
    for l in loops.all() {
        if let Some(var) = recognize(f, &cfg, l) {
            by_header.entry(cfg.block_id(l.header)).or_insert_with(Vec::new).push(var);
        }
    }
    InductionAnalysis { by_header }
}

/// Try to recognize the governing equality-exit induction variable of loop `l`.
fn recognize(f: &Function, cfg: &Cfg, l: &csolver_cfg::Loop) -> Option<EqExitIndVar> {
    // A single back-edge keeps the induction unambiguous.
    let [latch] = l.latches[..] else { return None };
    let header_id = cfg.block_id(l.header);
    let header = f.block(header_id)?;

    // The header must branch on an equality comparison `cmp(Eq|Ne, …)`.
    let Terminator::CondBr { cond: Operand::Reg(c), then_blk, else_blk, .. } = &header.term else {
        return None;
    };
    let (op, lhs, rhs) = find_cmp(header, *c)?;

    // Decide which successor stays in the loop and require the *other* to leave
    // it, so the exit is genuinely governed by this branch.
    let then_in = cfg.index_of(*then_blk).is_some_and(|n| l.body.contains(&n));
    let else_in = cfg.index_of(*else_blk).is_some_and(|n| l.body.contains(&n));
    if then_in == else_in {
        return None; // both or neither in the loop: not a clean exit branch
    }
    // The loop continues on the in-loop edge; that edge must correspond to
    // `v != bound`. For `cmp Ne` the true edge is `!=`; for `cmp Eq` the false
    // edge is `!=`.
    let continue_is_true = match op {
        CmpOp::Ne => true,
        CmpOp::Eq => false,
        _ => return None,
    };
    let in_loop_is_then = then_in;
    if in_loop_is_then != continue_is_true {
        return None; // the loop continues on the `==` edge — not a count-up exit
    }

    // One side of the comparison is a header parameter (the induction variable),
    // the other the loop bound.
    let (reg, bound) = induction_and_bound(header, &lhs, &rhs)?;

    // The bound must be loop-invariant: a constant, or a register not redefined
    // anywhere in the loop body.
    if let Operand::Reg(r) = &bound {
        if defined_in_loop(f, cfg, l, *r) {
            return None;
        }
    }

    // The back-edge must carry `reg := reg + stride` (a positive constant step).
    let pos = header.params.iter().position(|(p, _)| *p == reg)?;
    let next = edge_arg(f.block(cfg.block_id(latch))?, header_id, pos)?;
    let Operand::Reg(nv) = next else { return None };
    let stride = self_increment(f, cfg, l, nv, reg)?;
    if stride <= 0 {
        return None;
    }

    Some(EqExitIndVar { reg, bound, stride })
}

/// Find the comparison a boolean register was assigned in `block` (SSA: one def).
fn find_cmp(block: &csolver_ir::BasicBlock, c: RegId) -> Option<(CmpOp, Operand, Operand)> {
    block.insts.iter().find_map(|inst| match inst {
        Inst::Assign { dst, value: RValue::Cmp { op, lhs, rhs }, .. } if *dst == c => {
            Some((*op, lhs.clone(), rhs.clone()))
        }
        _ => None,
    })
}

/// From a comparison `lhs op rhs`, pick the operand that is a header parameter
/// (the induction variable) and return `(induction reg, bound operand)`.
fn induction_and_bound(
    header: &csolver_ir::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<(RegId, Operand)> {
    let is_param = |r: RegId| header.params.iter().any(|(p, _)| *p == r);
    match (lhs, rhs) {
        (Operand::Reg(a), _) if is_param(*a) => Some((*a, rhs.clone())),
        (_, Operand::Reg(b)) if is_param(*b) => Some((*b, lhs.clone())),
        _ => None,
    }
}

/// Whether register `r` is defined (redefined) anywhere in the loop body.
fn defined_in_loop(f: &Function, cfg: &Cfg, l: &csolver_cfg::Loop, r: RegId) -> bool {
    l.body.iter().any(|&node| {
        f.block(cfg.block_id(node)).is_some_and(|b| {
            b.params.iter().any(|(p, _)| *p == r)
                || b.insts.iter().any(|i| i.defined_reg() == Some(r))
        })
    })
}

/// If `nv` is defined within the loop as `base + c` (or `base - c`) for the
/// induction register `base`, return the signed stride `c`; else `None`.
fn self_increment(
    f: &Function,
    cfg: &Cfg,
    l: &csolver_cfg::Loop,
    nv: RegId,
    base: RegId,
) -> Option<i128> {
    for &node in &l.body {
        let block = f.block(cfg.block_id(node))?;
        for inst in &block.insts {
            if inst.defined_reg() != Some(nv) {
                continue;
            }
            if let Inst::Assign {
                value: RValue::Bin { op: op @ (BinOp::Add | BinOp::Sub), lhs: Operand::Reg(a), rhs: Operand::Const(Const::Int(bv)) },
                ..
            } = inst
            {
                if *a != base {
                    return None;
                }
                let c = bv.signed();
                return Some(if *op == BinOp::Sub { -c } else { c });
            }
            return None; // defined, but not as a constant step
        }
    }
    None
}

/// The argument a terminator passes at position `pos` along the `_ -> to` edge.
fn edge_arg(block: &csolver_ir::BasicBlock, to: BlockId, pos: usize) -> Option<Operand> {
    let args = match &block.term {
        Terminator::Br { target, args } if *target == to => args,
        Terminator::CondBr { then_blk, then_args, else_blk, else_args, .. } => {
            if *then_blk == to {
                then_args
            } else if *else_blk == to {
                else_args
            } else {
                return None;
            }
        }
        _ => return None,
    };
    args.get(pos).cloned()
}

#[cfg(test)]
mod tests {
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
            value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(i), rhs: Operand::int(64, 1) },
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
}
