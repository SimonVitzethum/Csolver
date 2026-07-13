//! The interval analysis: MSIR transfer functions wired to the solver.
//!
//! Loop invariants come from widening; branch conditions **refine** each taken
//! edge (`transfer_edge`): the `then` edge asserts the guard and the `else` edge
//! its negation, tightening the operands' intervals (and propagating along copy
//! chains a promoted spill leaves behind). This is what lets a clamped bound
//! (`if (n>cap) n=cap;`) reach the loop as `n <= cap`. Refinement is sound for
//! signed comparisons; unsigned and `!=` are left unrefined. Note it narrows
//! *edges*, not the widened loop-header fixpoint itself.

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

#[path = "cond.rs"]
mod cond;
pub(crate) use cond::*;

/// Run the interval analysis over `f`.
pub fn analyze_intervals(f: &Function) -> IntervalAnalysis {
    let cfg = Cfg::from_function(f);
    let dominators = Dominators::new(&cfg);
    let loops = Loops::detect(&cfg, &dominators);

    // The comparison behind each `i1` register, so a `CondBr` on it can refine the
    // taken edge (`then` asserts it, `else` its negation). Plus copy chains, so a
    // guard on a copy (`%c = n; if %c > 8`) also refines the original — which the
    // block parameter downstream actually carries.
    let cmps = collect_cmps(f);
    let copies = collect_copies(f);

    let solution = solve(
        &cfg,
        &loops,
        IntervalState::top(),
        |node, in_state| transfer_block(f, &cfg, node, in_state),
        |from, to, from_exit| transfer_edge(f, &cfg, from, to, from_exit, &cmps, &copies),
    );

    IntervalAnalysis { solution, cfg }
}

/// Map each `i1` register to the comparison that defines it.
fn collect_cmps(f: &Function) -> std::collections::HashMap<RegId, (CmpOp, Operand, Operand)> {
    let mut m = std::collections::HashMap::new();
    for b in &f.blocks {
        for inst in &b.insts {
            if let Inst::Assign { dst, value: RValue::Cmp { op, lhs, rhs }, .. } = inst {
                m.insert(*dst, (*op, lhs.clone(), rhs.clone()));
            }
        }
    }
    m
}

/// Map each register defined as a plain register copy (`dst = src`) to its source
/// — for propagating a refinement to the equal register (mem2reg leaves such
/// copies when a promoted load feeds a comparison).
fn collect_copies(f: &Function) -> std::collections::HashMap<RegId, RegId> {
    let mut m = std::collections::HashMap::new();
    for b in &f.blocks {
        for inst in &b.insts {
            if let Inst::Assign { dst, value: RValue::Use(Operand::Reg(src)), .. } = inst {
                m.insert(*dst, *src);
            }
        }
    }
    m
}

/// Refine `state` by asserting a comparison `lhs OP rhs` holds (or its negation),
/// tightening the intervals of its register operands. Sound for signed
/// comparisons; unsigned and disequality are left unrefined (still sound).
fn refine_by_cmp(
    state: &mut IntervalState,
    op: CmpOp,
    lhs: &Operand,
    rhs: &Operand,
    negate: bool,
    copies: &std::collections::HashMap<RegId, RegId>,
) {
    let op = if negate { negate_cmp(op) } else { op };
    let li = eval_operand(lhs, state);
    let ri = eval_operand(rhs, state);
    // (new lhs bound source, new rhs bound source) via the half-line constraints.
    let (nl, nr) = match op {
        CmpOp::Slt => (Some(ri.as_upper_constraint(true)), Some(li.as_lower_constraint(true))),
        CmpOp::Sle => (Some(ri.as_upper_constraint(false)), Some(li.as_lower_constraint(false))),
        CmpOp::Sgt => (Some(ri.as_lower_constraint(true)), Some(li.as_upper_constraint(true))),
        CmpOp::Sge => (Some(ri.as_lower_constraint(false)), Some(li.as_upper_constraint(false))),
        CmpOp::Eq => (Some(ri), Some(li)),
        // Unsigned comparisons and `!=` are not soundly refined on the signed
        // interval lattice here — leave the operands as-is.
        _ => (None, None),
    };
    if let (Operand::Reg(r), Some(c)) = (lhs, nl) {
        refine_reg(state, *r, &li.meet(&c), copies);
    }
    if let (Operand::Reg(r), Some(c)) = (rhs, nr) {
        refine_reg(state, *r, &ri.meet(&c), copies);
    }
}

/// Set `reg` to `iv`, and propagate the same bound along its copy chain (`reg`
/// was defined `= src`, so they are equal). Bounded to avoid a cycle.
fn refine_reg(
    state: &mut IntervalState,
    mut reg: RegId,
    iv: &Interval,
    copies: &std::collections::HashMap<RegId, RegId>,
) {
    for _ in 0..64 {
        let cur = state.get(reg);
        state.set(reg, cur.meet(iv));
        match copies.get(&reg) {
            Some(&src) if src != reg => reg = src,
            _ => break,
        }
    }
}

fn negate_cmp(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::Slt => CmpOp::Sge,
        CmpOp::Sle => CmpOp::Sgt,
        CmpOp::Sgt => CmpOp::Sle,
        CmpOp::Sge => CmpOp::Slt,
        CmpOp::Ult => CmpOp::Uge,
        CmpOp::Ule => CmpOp::Ugt,
        CmpOp::Ugt => CmpOp::Ule,
        CmpOp::Uge => CmpOp::Ult,
        CmpOp::Eq => CmpOp::Ne,
        CmpOp::Ne => CmpOp::Eq,
    }
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
    cmps: &std::collections::HashMap<RegId, (CmpOp, Operand, Operand)>,
    copies: &std::collections::HashMap<RegId, RegId>,
) -> IntervalState {
    if !from_exit.is_reachable() {
        return IntervalState::Unreachable;
    }
    let from_block = f.block(cfg.block_id(from)).expect("from block");
    let to_id = cfg.block_id(to);
    let to_block = f.block(to_id).expect("to block");

    // Apply the branch guard: on a `CondBr`, the `then` edge asserts the condition
    // and the `else` edge its negation, tightening the operands' intervals before
    // block-parameter binding (and before this edge's contribution is joined).
    let mut refined = from_exit.clone();
    if let Terminator::CondBr { cond: Operand::Reg(c), then_blk, else_blk, .. } = &from_block.term {
        if let Some((op, lhs, rhs)) = cmps.get(c) {
            let is_then = *then_blk == to_id;
            let is_else = *else_blk == to_id;
            // Only refine when the edge is unambiguously one side (a self-loop
            // `then == else` would assert both, so refine neither).
            if is_then ^ is_else {
                refine_by_cmp(&mut refined, *op, lhs, rhs, is_else, copies);
            }
        }
    }
    let from_exit = &refined;

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
        Inst::Load { dst, .. }
        | Inst::Alloc { dst, .. }
        | Inst::PtrOffset { dst, .. }
        | Inst::FieldPtr { dst, .. }
        | Inst::RefWitness { dst, .. } => {
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
        | Inst::ProvLabel { .. }
        | Inst::CapRequire { .. }
        | Inst::ProvPropagate { .. }
        | Inst::CapRequireIfAlias { .. }
        | Inst::CapRequireIfAliasFields { .. }
        | Inst::TaintSource { .. }
        | Inst::TaintCheck { .. }
        | Inst::TaintClear { .. }
        | Inst::TypestateSet { .. }
        | Inst::TypestateRequire { .. }
        | Inst::TypestateYield { .. }
        | Inst::Refcount { .. }
        | Inst::TypestateLeakCheck { .. }
        | Inst::SecretCheck { .. }
        | Inst::Barrier { .. }
        | Inst::Spawn { .. }
        | Inst::Join
        | Inst::Cas { .. }
        | Inst::SafetyCheck { .. } => {}
    }
}

/// Evaluate an r-value to an interval.
fn eval_rvalue(rv: &RValue, state: &IntervalState) -> Interval {
    match rv {
        RValue::Use(op) => eval_operand(op, state),
        RValue::Bin { op, lhs, rhs, .. } => {
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
        // The result is one of the two operands; the interval domain has no join, so
        // stay conservative here (`top`). The symbolic executor recovers the precise
        // per-alternative reasoning via `Prov::Select` / `ite`.
        RValue::Select { .. } => Interval::top(),
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
        Operand::Const(Const::Undef)
        | Operand::Const(Const::Symbol(_))
        | Operand::Const(Const::SymbolOffset(..)) => Interval::top(),
    }
}

#[cfg(test)]
#[path = "analysis_tests.rs"]
mod tests;
