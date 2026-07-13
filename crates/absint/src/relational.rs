//! The zone (relational) analysis: MSIR transfer functions wired to the solver,
//! inferring difference invariants `vₐ − v_b ≤ c` between registers — the
//! relational facts the per-variable interval domain cannot express.
//!
//! It is intentionally conservative: only *affine* register updates
//! (`x = c`, `x = y`, `x = y ± c`, and the self-increment `x = x ± c`) refine the
//! zone precisely; anything else **forgets** the assigned register (sound). A
//! conditional branch refines the zone with the guard (and its negation on the
//! other edge), using a static map from each boolean register to the comparison
//! it holds. The result feeds the symbolic engine's loop-header invariants.

use crate::engine::{solve, Solution};
use crate::zone::Zone;
use csolver_cfg::{Cfg, Dominators, Loops};
use csolver_ir::{
    BinOp, BlockId, CmpOp, Const, Function, Inst, Operand, RValue, RegId, Terminator,
};
use std::collections::HashMap;

/// Cap on the number of tracked registers (the DBM is `(n+1)²`). Past this the
/// analysis tracks nothing (sound: it just yields no relations).
const MAX_VARS: usize = 32;

/// A relational analysis result: difference invariants per block.
#[derive(Debug, Clone)]
pub struct ZoneAnalysis {
    solution: Option<Solution<Zone>>,
    cfg: Cfg,
    /// Tracked register → zone variable index (1-based; 0 is the zero node).
    index: HashMap<RegId, usize>,
}

impl ZoneAnalysis {
    /// The difference invariants `a − b ≤ c` (both real registers) that hold on
    /// entry to `block`. Used to relate a loop header's variables.
    pub fn entry_diffs(&self, block: BlockId) -> Vec<(RegId, RegId, i128)> {
        let Some(solution) = &self.solution else {
            return Vec::new();
        };
        let Some(node) = self.cfg.index_of(block) else {
            return Vec::new();
        };
        let zone = &solution.in_states[node];
        if zone.is_bottom() {
            return Vec::new();
        }
        let mut out = Vec::new();
        for (&ra, &ia) in &self.index {
            for (&rb, &ib) in &self.index {
                if ra == rb {
                    continue;
                }
                if let Some(c) = zone.diff_upper(ia, ib) {
                    out.push((ra, rb, c));
                }
            }
        }
        out
    }
}

/// Run the zone analysis over `f`.
pub fn analyze_zones(f: &Function) -> ZoneAnalysis {
    let cfg = Cfg::from_function(f);
    let index = build_index(f);
    if index.is_empty() {
        return ZoneAnalysis { solution: None, cfg, index };
    }
    let nvars = index.len();
    let cmp_map = build_cmp_map(f);
    let dominators = Dominators::new(&cfg);
    let loops = Loops::detect(&cfg, &dominators);

    let ctx = Ctx { f, cfg: &cfg, index: &index, cmp_map };
    let solution = solve(
        &cfg,
        &loops,
        Zone::top(nvars),
        |node, in_state| ctx.transfer_block(node, in_state),
        |from, to, exit| ctx.transfer_edge(from, to, exit),
    );
    ZoneAnalysis { solution: Some(solution), cfg, index }
}

/// Analysis context shared by the transfer closures — borrows the function,
/// CFG and index from the caller (cloning the whole `Function` per analysis
/// was a measurable waste on large functions).
struct Ctx<'a> {
    f: &'a Function,
    cfg: &'a Cfg,
    index: &'a HashMap<RegId, usize>,
    cmp_map: HashMap<RegId, (CmpOp, Operand, Operand)>,
}

impl Ctx<'_> {
    fn idx(&self, r: RegId) -> Option<usize> {
        self.index.get(&r).copied()
    }

    fn transfer_block(&self, node: usize, in_state: &Zone) -> Zone {
        if in_state.is_bottom() {
            return in_state.clone();
        }
        let mut z = in_state.clone();
        if let Some(b) = self.f.block(self.cfg.block_id(node)) {
            for inst in &b.insts {
                self.apply_inst(inst, &mut z);
            }
        }
        z
    }

    /// Apply one instruction's effect to the zone (precise affine update, else
    /// forget the defined register).
    fn apply_inst(&self, inst: &Inst, z: &mut Zone) {
        let Some(dst) = inst.defined_reg() else {
            return;
        };
        let Some(di) = self.idx(dst) else {
            return;
        };
        match inst {
            Inst::Assign { value: RValue::Use(Operand::Const(Const::Int(bv))), .. } => {
                let c = bv.signed();
                z.forget(di);
                z.add_constraint(di, 0, c); // dst ≤ c
                z.add_constraint(0, di, -c); // dst ≥ c
            }
            Inst::Assign { value: RValue::Use(Operand::Reg(src)), .. } => match self.idx(*src) {
                Some(si) => {
                    z.forget(di);
                    z.add_constraint(di, si, 0); // dst - src ≤ 0
                    z.add_constraint(si, di, 0); // src - dst ≤ 0
                }
                None => z.forget(di),
            },
            Inst::Assign { value: RValue::Bin { op: op @ (BinOp::Add | BinOp::Sub), lhs: Operand::Reg(a), rhs: Operand::Const(Const::Int(bv)), .. }, .. } => {
                let mut c = bv.signed();
                if *op == BinOp::Sub {
                    c = -c;
                }
                match self.idx(*a) {
                    Some(ai) if ai == di => z.translate(di, c), // x = x + c (self-update)
                    Some(ai) => {
                        z.forget(di);
                        z.add_constraint(di, ai, c); // dst - a ≤ c
                        z.add_constraint(ai, di, -c); // a - dst ≤ -c
                    }
                    None => z.forget(di),
                }
            }
            _ => z.forget(di),
        }
    }

    fn transfer_edge(&self, from: usize, to: usize, exit: &Zone) -> Zone {
        if exit.is_bottom() {
            return exit.clone();
        }
        let mut z = exit.clone();
        let Some(fb) = self.f.block(self.cfg.block_id(from)) else {
            return z;
        };
        let to_block = self.cfg.block_id(to);

        // Refine with the branch guard (or its negation on the else edge).
        if let Terminator::CondBr { cond: Operand::Reg(c), then_blk, else_blk, .. } = &fb.term {
            if let Some((op, lhs, rhs)) = self.cmp_map.get(c) {
                let taken = if to_block == *then_blk {
                    Some(*op)
                } else if to_block == *else_blk {
                    Some(negate(*op))
                } else {
                    None
                };
                if let Some(op) = taken {
                    self.refine(&mut z, op, lhs, rhs);
                }
            }
        }

        // Bind the target block's parameters from this edge's arguments.
        if let Some(args) = edge_args(&fb.term, to_block) {
            if let Some(tb) = self.f.block(to_block) {
                for (i, (param, _)) in tb.params.iter().enumerate() {
                    let Some(pi) = self.idx(*param) else { continue };
                    match args.get(i) {
                        Some(Operand::Reg(r)) => match self.idx(*r) {
                            Some(ri) => {
                                z.forget(pi);
                                z.add_constraint(pi, ri, 0);
                                z.add_constraint(ri, pi, 0);
                            }
                            None => z.forget(pi),
                        },
                        Some(Operand::Const(Const::Int(bv))) => {
                            let c = bv.signed();
                            z.forget(pi);
                            z.add_constraint(pi, 0, c);
                            z.add_constraint(0, pi, -c);
                        }
                        _ => z.forget(pi),
                    }
                }
            }
        }
        z
    }

    /// Tighten the zone with `lhs op rhs` (a sound narrowing). Only register and
    /// integer-constant operands are handled; others are ignored (sound).
    fn refine(&self, z: &mut Zone, op: CmpOp, lhs: &Operand, rhs: &Operand) {
        let (a, av) = self.operand(lhs);
        let (b, bv) = self.operand(rhs);
        // Express each side as (index, const offset): a value is `v_idx + off`,
        // where idx == 0 denotes the constant `off`.
        let (Some(ai), Some(bi)) = (a, b) else { return };
        // a op b, with a = v_ai + av, b = v_bi + bv.
        // `a ≤ b`  ⇔  v_ai - v_bi ≤ bv - av.
        match op {
            CmpOp::Sle | CmpOp::Ule => z.add_constraint(ai, bi, bv - av),
            CmpOp::Slt | CmpOp::Ult => z.add_constraint(ai, bi, bv - av - 1),
            CmpOp::Sge | CmpOp::Uge => z.add_constraint(bi, ai, av - bv),
            CmpOp::Sgt | CmpOp::Ugt => z.add_constraint(bi, ai, av - bv - 1),
            CmpOp::Eq => {
                z.add_constraint(ai, bi, bv - av);
                z.add_constraint(bi, ai, av - bv);
            }
            CmpOp::Ne => {}
        }
    }

    /// An operand as `(zone index, constant offset)`: a register is
    /// `(Some(idx), 0)`; an integer constant is `(Some(0), c)` (the zero node);
    /// anything untracked is `(None, 0)`.
    fn operand(&self, op: &Operand) -> (Option<usize>, i128) {
        match op {
            Operand::Reg(r) => (self.idx(*r), 0),
            Operand::Const(Const::Int(bv)) => (Some(0), bv.signed()),
            _ => (None, 0),
        }
    }
}

/// The negation of a comparison predicate (`csolver_ir::CmpOp` has none).
fn negate(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::Eq => CmpOp::Ne,
        CmpOp::Ne => CmpOp::Eq,
        CmpOp::Ult => CmpOp::Uge,
        CmpOp::Uge => CmpOp::Ult,
        CmpOp::Ule => CmpOp::Ugt,
        CmpOp::Ugt => CmpOp::Ule,
        CmpOp::Slt => CmpOp::Sge,
        CmpOp::Sge => CmpOp::Slt,
        CmpOp::Sle => CmpOp::Sgt,
        CmpOp::Sgt => CmpOp::Sle,
    }
}

/// The arguments a terminator passes along the `_ -> to` edge.
fn edge_args(term: &Terminator, to: BlockId) -> Option<&[Operand]> {
    match term {
        Terminator::Br { target, args } if *target == to => Some(args),
        Terminator::CondBr { then_blk, then_args, else_blk, else_args, .. } => {
            if *then_blk == to {
                Some(then_args)
            } else if *else_blk == to {
                Some(else_args)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Build the tracked-register → index map (1-based), or empty if over the cap.
fn build_index(f: &Function) -> HashMap<RegId, usize> {
    let mut regs: Vec<RegId> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let add = |r: RegId, regs: &mut Vec<RegId>, seen: &mut std::collections::HashSet<RegId>| {
        if seen.insert(r) {
            regs.push(r);
        }
    };
    for b in &f.blocks {
        for (p, _) in &b.params {
            add(*p, &mut regs, &mut seen);
        }
        for inst in &b.insts {
            if let Some(d) = inst.defined_reg() {
                add(d, &mut regs, &mut seen);
            }
        }
    }
    if regs.len() > MAX_VARS {
        return HashMap::new();
    }
    regs.into_iter().enumerate().map(|(i, r)| (r, i + 1)).collect()
}

/// Map each boolean register to the comparison it was assigned (SSA: at most one
/// definition), so a `CondBr` on it can refine the zone.
fn build_cmp_map(f: &Function) -> HashMap<RegId, (CmpOp, Operand, Operand)> {
    let mut map = HashMap::new();
    for b in &f.blocks {
        for inst in &b.insts {
            if let Inst::Assign { dst, value: RValue::Cmp { op, lhs, rhs }, .. } = inst {
                map.insert(*dst, (*op, lhs.clone(), rhs.clone()));
            }
        }
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::{BasicBlock, FuncId, Type};

    /// `loop_two_indices(n)`:
    ///   bb0: i=0; j=0; br bb1(i, j)
    ///   bb1(i, j): c = i < n ; condbr c -> bb2(i,j) / bb3
    ///   bb2(i, j): ni = i+1 ; nj = j+1 ; br bb1(ni, nj)
    ///   bb3: return
    /// The relation `j == i` (so `j - i ≤ 0`) is a zone invariant at the header.
    fn loop_two_indices() -> Function {
        let n = RegId(0);
        let i = RegId(1);
        let j = RegId(2);
        let c = RegId(3);
        let ni = RegId(4);
        let nj = RegId(5);

        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::Br { target: BlockId(1), args: vec![Operand::int(64, 0), Operand::int(64, 0)] },
        );
        // (no insts; args carry the initial i=0, j=0)
        let _ = &mut bb0;

        let mut bb1 = BasicBlock::new(
            BlockId(1),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(2),
                then_args: vec![],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb1.params = vec![(i, Type::int(64)), (j, Type::int(64))];
        bb1.insts.push(Inst::Assign {
            dst: c,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Slt, lhs: Operand::Reg(i), rhs: Operand::Reg(n) },
        });

        // The body uses the header's `i`/`j` directly (it is dominated by bb1).
        let mut bb2 = BasicBlock::new(
            BlockId(2),
            Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(ni), Operand::Reg(nj)] },
        );
        bb2.insts.push(Inst::Assign {
            dst: ni,
            ty: Type::int(64),
            value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(i), rhs: Operand::int(64, 1) , flags: Default::default() },
        });
        bb2.insts.push(Inst::Assign {
            dst: nj,
            ty: Type::int(64),
            value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(j), rhs: Operand::int(64, 1) , flags: Default::default() },
        });

        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

        Function {
            id: FuncId(0),
            name: "loop_two_indices".into(),
            params: vec![(n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    #[test]
    fn infers_equal_induction_variables() {
        let f = loop_two_indices();
        let za = analyze_zones(&f);
        let diffs = za.entry_diffs(BlockId(1));
        // j - i ≤ 0 and i - j ≤ 0 (i.e. j == i) must be inferred at the header.
        assert!(
            diffs.iter().any(|&(a, b, c)| a == RegId(2) && b == RegId(1) && c <= 0),
            "expected j - i <= 0 at the loop header, got {diffs:?}"
        );
        assert!(
            diffs.iter().any(|&(a, b, c)| a == RegId(1) && b == RegId(2) && c <= 0),
            "expected i - j <= 0 at the loop header"
        );
    }
}
