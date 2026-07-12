//! `mem2reg`: promote non-escaping scalar stack slots to SSA registers.
//!
//! Unoptimized (`-O0`) front-end output spills every local — including loop
//! induction variables and pointer parameters — to an `alloca`, then reloads it
//! on each use. That defeats the induction/interval analysis (a reloaded counter
//! is a fresh unconstrained symbol, so `p[i]` cannot be bounded) and store-load
//! provenance across loop back-edges (a reloaded pointer loses its region). This
//! pass rewrites such slots back into SSA form — exactly the promotion `-O1`
//! would have done — so the analysis sees register values with induction bounds
//! and provenance intact.
//!
//! It is the standard SSA-construction algorithm (Cytron et al.): place block
//! parameters (MSIR's PHIs) at the iterated dominance frontier of a slot's stores,
//! then rename loads to the reaching value and drop the stores/alloca.
//!
//! ## Soundness
//!
//! The transform is semantics-preserving, and it only ever *promotes* — it never
//! removes a safety obligation, it moves the same value from memory into a
//! register. A slot is promoted only when it provably cannot alias anything: a
//! single scalar `alloca` whose pointer is used **exclusively** as the address of
//! full-width loads and stores (never offset, cast, stored, passed, or otherwise
//! escaped). A block that would need a PHI reachable across a `switch` edge (which
//! carries no arguments in MSIR) is left un-promoted. So a promotion is always a
//! faithful re-encoding of the original memory behaviour; anything the analysis
//! could not prove before, it still cannot prove after.

use csolver_cfg::{Cfg, Dominators};
use csolver_ir::{
    BasicBlock, BlockId, Const, Function, Inst, Module, Operand, RValue, RegId, Terminator, Type,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Promote eligible scalar slots in every function of the module to SSA.
pub(crate) fn promote_module(module: &Module) -> Module {
    let mut m = module.clone();
    for f in &mut m.functions {
        promote_function(f);
    }
    m
}

/// A scalar whose stack slot may be promoted, keyed by the `alloca`'s register.
struct Slot {
    ty: Type,
}

fn is_scalar(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Int { .. } | Type::Ptr { .. } | Type::Bool | Type::Opaque { .. }
    )
}

fn is_slot(o: &Operand, a: RegId) -> bool {
    matches!(o, Operand::Reg(r) if *r == a)
}

fn inst_mentions(inst: &Inst, a: RegId) -> bool {
    let mut found = false;
    visit_operands(inst, &mut |o| found |= is_slot(o, a));
    found
}

fn term_mentions(term: &Terminator, a: RegId) -> bool {
    let mut found = false;
    visit_term_operands(term, &mut |o| found |= is_slot(o, a));
    found
}

/// Redirect one `switch` target through a fresh single-predecessor `Br` block iff the
/// target has more than one predecessor (a *critical* edge). Reuses one split block per
/// distinct target within the same switch.
fn redirect_switch_target(
    t: &mut BlockId,
    pred_count: &std::collections::HashMap<BlockId, usize>,
    splits: &mut std::collections::HashMap<BlockId, BlockId>,
    new_blocks: &mut Vec<BasicBlock>,
    next_id: &mut u32,
) {
    if pred_count.get(t).copied().unwrap_or(0) <= 1 {
        return;
    }
    let sid = *splits.entry(*t).or_insert_with(|| {
        let id = BlockId(*next_id);
        *next_id += 1;
        new_blocks.push(BasicBlock::new(id, Terminator::Br { target: *t, args: Vec::new() }));
        id
    });
    *t = sid;
}

/// Split every critical edge out of a `switch` — an edge to a block with more than one
/// predecessor — by inserting a fresh single-predecessor `Br` block on it. MSIR `Switch`
/// carries no per-target arguments, so mem2reg cannot place a PHI argument on a switch
/// edge; the `Br` on the split block can. Semantics-preserving (an unconditional jump to
/// the original target), and the executor already handles the extra `Br` blocks.
fn split_critical_switch_edges(f: &mut Function) {
    use std::collections::{HashMap, HashSet};
    let mut pred_count: HashMap<BlockId, usize> = HashMap::new();
    for b in &f.blocks {
        // Count distinct predecessor *blocks* (two switch cases to the same target are one
        // predecessor), matching how the CFG counts predecessors.
        for s in b.term.successors().into_iter().collect::<HashSet<_>>() {
            *pred_count.entry(s).or_default() += 1;
        }
    }
    let mut next_id = f.blocks.iter().map(|b| b.id.0).max().map_or(0, |m| m + 1);
    let mut new_blocks: Vec<BasicBlock> = Vec::new();
    for b in &mut f.blocks {
        let Terminator::Switch { cases, default, .. } = &mut b.term else { continue };
        let mut splits: HashMap<BlockId, BlockId> = HashMap::new();
        for (_, t) in cases.iter_mut() {
            redirect_switch_target(t, &pred_count, &mut splits, &mut new_blocks, &mut next_id);
        }
        redirect_switch_target(default, &pred_count, &mut splits, &mut new_blocks, &mut next_id);
    }
    f.blocks.extend(new_blocks);
}

fn promote_function(f: &mut Function) {
    // 0. Split critical edges out of `switch`es. MSIR `Switch` carries no per-target
    //    arguments, so a PHI a promotion needs at a block reachable through a switch edge
    //    cannot get its argument on that edge — the slot would be dropped (unpromoted),
    //    which is exactly what left the crypto worker's request-pointer slot spilled and
    //    broke provenance across the switch. Inserting a single-predecessor `Br` block on
    //    each such edge lets the PHI argument ride the `Br` (which does carry args).
    split_critical_switch_edges(f);

    // 1. Candidate slots: a single-element scalar `alloca` whose pointer is used
    //    only as the address of a matching-width load/store.
    let mut slots: BTreeMap<RegId, Slot> = BTreeMap::new();
    for b in &f.blocks {
        for inst in &b.insts {
            if let Inst::Alloc { dst, elem, count, .. } = inst {
                let one = matches!(count, Operand::Const(Const::Int(bv)) if bv.unsigned() == 1);
                if one && is_scalar(elem) {
                    slots.insert(*dst, Slot { ty: elem.clone() });
                }
            }
        }
    }
    slots.retain(|a, s| eligible(f, *a, &s.ty));
    if slots.is_empty() {
        return;
    }

    // 2. CFG, dominators, dominance frontiers.
    let cfg = Cfg::from_function(f);
    let dom = Dominators::new(&cfg);
    let df = dominance_frontiers(&cfg, &dom);

    // 3. Per-slot PHI placement (iterated dominance frontier of its store blocks).
    //    Drop a slot if any PHI block is reachable through a `switch` edge, which
    //    cannot carry the PHI argument.
    let switch_nodes: BTreeSet<usize> = (0..cfg.node_count())
        .filter(|&n| matches!(f.block(cfg.block_id(n)).map(|b| &b.term), Some(Terminator::Switch { .. })))
        .collect();
    let mut phi_blocks: BTreeMap<RegId, BTreeSet<usize>> = BTreeMap::new();
    for a in slots.keys().copied().collect::<Vec<_>>() {
        let mut defs: BTreeSet<usize> = BTreeSet::new();
        for n in 0..cfg.node_count() {
            if block_stores_to(f, cfg.block_id(n), a) {
                defs.insert(n);
            }
        }
        let phis = iterated_frontier(&defs, &df);
        let switch_conflict = phis
            .iter()
            .any(|&n| cfg.predecessors(n).iter().any(|p| switch_nodes.contains(p)));
        if switch_conflict {
            slots.remove(&a);
        } else {
            phi_blocks.insert(a, phis);
        }
    }
    if slots.is_empty() {
        return;
    }

    // 4. Materialize PHIs as fresh block parameters (deterministic: slots sorted
    //    by register, one param per (block, slot)).
    let mut next = next_reg(f);
    // (node, slot) -> the PHI's fresh register.
    let mut phi_reg: HashMap<(usize, RegId), RegId> = HashMap::new();
    // Per block, the slots that gained a PHI, in the order their params were added.
    let mut block_phi_order: HashMap<usize, Vec<RegId>> = HashMap::new();
    for (a, s) in &slots {
        for &n in &phi_blocks[a] {
            let reg = RegId(next);
            next += 1;
            phi_reg.insert((n, *a), reg);
            block_phi_order.entry(n).or_default().push(*a);
            if let Some(b) = f.block_mut(cfg.block_id(n)) {
                b.params.push((reg, s.ty.clone()));
            }
        }
    }

    // 5. Rename: a dominator-tree DFS carrying each slot's reaching value.
    let children = dom_children(&cfg, &dom);
    let init: HashMap<RegId, Operand> =
        slots.keys().map(|a| (*a, Operand::Const(Const::Undef))).collect();
    let mut stack = vec![(cfg.entry(), init)];
    while let Some((node, mut cur)) = stack.pop() {
        // PHIs defined at this block become the reaching value on entry.
        for a in block_phi_order.get(&node).into_iter().flatten() {
            cur.insert(*a, Operand::Reg(phi_reg[&(node, *a)]));
        }
        rewrite_block(f, cfg.block_id(node), &slots, &mut cur);
        // Supply PHI arguments to successors, and recurse.
        append_phi_args(f, cfg.block_id(node), &cfg, &block_phi_order, &cur);
        for &c in &children[node] {
            stack.push((c, cur.clone()));
        }
    }
}

/// A slot is eligible iff its pointer register is used *only* as the address of a
/// load/store whose type matches the slot's element type. Any other appearance
/// (as a value, an offset base, a call argument, a store value, …) means it may
/// alias, so it is not promoted.
fn eligible(f: &Function, a: RegId, ty: &Type) -> bool {
    for b in &f.blocks {
        for inst in &b.insts {
            match inst {
                // The two permitted uses — but only at a matching width.
                Inst::Load { ptr: Operand::Reg(r), ty: lty, .. } if *r == a => {
                    if lty != ty {
                        return false;
                    }
                }
                Inst::Store { ptr: Operand::Reg(r), value, ty: sty, .. } if *r == a => {
                    // A matching-width store whose *value* is not the slot pointer.
                    if sty != ty || is_slot(value, a) {
                        return false;
                    }
                }
                // The `alloca` itself defines the slot; ignore.
                Inst::Alloc { dst, .. } if *dst == a => {}
                // Any other appearance escapes the slot.
                _ if inst_mentions(inst, a) => return false,
                _ => {}
            }
        }
        if term_mentions(&b.term, a) {
            return false;
        }
    }
    true
}

/// Rewrite one block's body: replace loads of a promoted slot with the reaching
/// value, drop its stores (updating the reaching value) and its `alloca`.
fn rewrite_block(
    f: &mut Function,
    block: csolver_ir::BlockId,
    slots: &BTreeMap<RegId, Slot>,
    cur: &mut HashMap<RegId, Operand>,
) {
    let Some(b) = f.block_mut(block) else { return };
    let has_spans = b.inst_spans.len() == b.insts.len();
    let mut insts = Vec::with_capacity(b.insts.len());
    let mut spans = Vec::with_capacity(b.insts.len());
    for (i, inst) in std::mem::take(&mut b.insts).into_iter().enumerate() {
        let span = if has_spans { b.inst_spans.get(i).cloned().flatten() } else { None };
        match inst {
            Inst::Alloc { dst, .. } if slots.contains_key(&dst) => {}
            Inst::Load { dst, ptr: Operand::Reg(a), .. } if slots.contains_key(&a) => {
                let value = cur[&a].clone();
                insts.push(Inst::Assign { dst, ty: slots[&a].ty.clone(), value: RValue::Use(value) });
                spans.push(span);
            }
            Inst::Store { ptr: Operand::Reg(a), value, .. } if slots.contains_key(&a) => {
                cur.insert(a, value);
            }
            other => {
                insts.push(other);
                spans.push(span);
            }
        }
    }
    b.insts = insts;
    b.inst_spans = if has_spans { spans } else { Vec::new() };
}

/// Append each successor's PHI arguments for the edge out of `block`, matching
/// the parameter order recorded in `block_phi_order`.
fn append_phi_args(
    f: &mut Function,
    block: csolver_ir::BlockId,
    cfg: &Cfg,
    block_phi_order: &HashMap<usize, Vec<RegId>>,
    cur: &HashMap<RegId, Operand>,
) {
    let empty = Vec::new();
    let args_for = |target: usize| -> Vec<Operand> {
        block_phi_order.get(&target).unwrap_or(&empty).iter().map(|a| cur[a].clone()).collect()
    };
    let Some(b) = f.block_mut(block) else { return };
    match &mut b.term {
        Terminator::Br { target, args } => {
            let t = cfg.index_of(*target);
            if let Some(t) = t {
                args.extend(args_for(t));
            }
        }
        Terminator::CondBr { then_blk, then_args, else_blk, else_args, .. } => {
            if let Some(t) = cfg.index_of(*then_blk) {
                then_args.extend(args_for(t));
            }
            if let Some(e) = cfg.index_of(*else_blk) {
                else_args.extend(args_for(e));
            }
        }
        // `switch` edges carry no args; slots needing a PHI here were not promoted.
        Terminator::Switch { .. } | Terminator::Return(_) | Terminator::Unreachable => {}
    }
}

// ---- CFG helpers ---------------------------------------------------------

fn block_stores_to(f: &Function, block: csolver_ir::BlockId, a: RegId) -> bool {
    f.block(block).is_some_and(|b| {
        b.insts.iter().any(|i| matches!(i, Inst::Store { ptr: Operand::Reg(r), .. } if *r == a))
    })
}

/// Dominance frontiers via Cooper–Harvey–Kennedy.
fn dominance_frontiers(cfg: &Cfg, dom: &Dominators) -> Vec<BTreeSet<usize>> {
    let n = cfg.node_count();
    let mut df: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n];
    for b in 0..n {
        let preds = cfg.predecessors(b);
        if preds.len() < 2 {
            continue;
        }
        let Some(idom_b) = dom.immediate_dominator(b) else { continue };
        for &p in preds {
            let mut runner = p;
            while runner != idom_b {
                df[runner].insert(b);
                match dom.immediate_dominator(runner) {
                    Some(next) if next != runner => runner = next,
                    _ => break,
                }
            }
        }
    }
    df
}

/// Iterated dominance frontier of a set of definition blocks (PHI placement).
fn iterated_frontier(defs: &BTreeSet<usize>, df: &[BTreeSet<usize>]) -> BTreeSet<usize> {
    let mut phis: BTreeSet<usize> = BTreeSet::new();
    let mut work: Vec<usize> = defs.iter().copied().collect();
    while let Some(x) = work.pop() {
        for &y in &df[x] {
            if phis.insert(y) && !defs.contains(&y) {
                work.push(y);
            }
        }
    }
    phis
}

/// Dominator-tree children of each node (sorted, for deterministic traversal).
fn dom_children(cfg: &Cfg, dom: &Dominators) -> Vec<Vec<usize>> {
    let n = cfg.node_count();
    let mut children = vec![Vec::new(); n];
    for c in 0..n {
        if let Some(p) = dom.immediate_dominator(c) {
            if p != c {
                children[p].push(c);
            }
        }
    }
    for ch in &mut children {
        ch.sort_unstable();
    }
    children
}

/// One past the largest register id used anywhere in `f`.
fn next_reg(f: &Function) -> u32 {
    let mut max = 0u32;
    let mut note = |r: RegId| max = max.max(r.0 + 1);
    for b in &f.blocks {
        for (r, _) in &b.params {
            note(*r);
        }
        for inst in &b.insts {
            if let Some(d) = inst.defined_reg() {
                note(d);
            }
        }
    }
    max
}

// ---- operand visiting ----------------------------------------------------

fn visit_operands(inst: &Inst, op: &mut impl FnMut(&Operand)) {
    match inst {
        Inst::Alloc { count, .. } => op(count),
        Inst::Load { ptr, .. } => op(ptr),
        Inst::Store { ptr, value, .. } => {
            op(ptr);
            op(value);
        }
        Inst::PtrOffset { base, index, .. } => {
            op(base);
            op(index);
        }
        Inst::FieldPtr { base, .. } => op(base),
        Inst::RefWitness { .. } => {}
        Inst::Assign { value, .. } => match value {
            RValue::Use(o) => op(o),
            RValue::Bin { lhs, rhs, .. } | RValue::Cmp { lhs, rhs, .. } => {
                op(lhs);
                op(rhs);
            }
            RValue::Cast { operand, .. } => op(operand),
            RValue::Select { cond, then_val, else_val } => {
                op(cond);
                op(then_val);
                op(else_val);
            }
        },
        Inst::Call { args, .. } | Inst::Intrinsic { args, .. } => args.iter().for_each(op),
        Inst::MemIntrinsic { dst, src, len, .. } => {
            op(dst);
            if let Some(s) = src {
                op(s);
            }
            op(len);
        }
        Inst::Dealloc { ptr, .. } => op(ptr),
        Inst::ProvLabel { ptr, .. } | Inst::CapRequire { ptr, .. } => op(ptr),
        Inst::ProvPropagate { dst, src } => {
            op(dst);
            op(src);
        }
        Inst::CapRequireIfAlias { a, b, .. } => {
            op(a);
            op(b);
        }
        Inst::CapRequireIfAliasFields { obj, .. } => op(obj),
        Inst::TaintSource { val, .. } | Inst::TaintCheck { val, .. } | Inst::TaintClear { val, .. } => {
            op(val)
        }
        Inst::TypestateSet { val, .. }
        | Inst::TypestateRequire { val, .. }
        | Inst::Refcount { val, .. }
        | Inst::SecretCheck { val, .. } => op(val),
        Inst::TypestateLeakCheck { escaping, .. } => {
            if let Some(e) = escaping {
                op(e);
            }
        }
        Inst::TypestateYield { .. } | Inst::Barrier { .. } | Inst::Spawn { .. } | Inst::Join | Inst::Cas { .. } => {}
        Inst::SafetyCheck { condition, .. } => condition_operands(condition, op),
        Inst::Asm { .. } => {}
    }
}

fn visit_term_operands(term: &Terminator, op: &mut impl FnMut(&Operand)) {
    match term {
        Terminator::Return(Some(o)) => op(o),
        Terminator::CondBr { cond, then_args, else_args, .. } => {
            op(cond);
            then_args.iter().for_each(&mut *op);
            else_args.iter().for_each(&mut *op);
        }
        Terminator::Br { args, .. } => args.iter().for_each(op),
        Terminator::Switch { value, .. } => op(value),
        Terminator::Return(None) | Terminator::Unreachable => {}
    }
}

fn condition_operands(c: &csolver_ir::Condition, op: &mut impl FnMut(&Operand)) {
    use csolver_ir::Condition;
    match c {
        Condition::True => {}
        Condition::Cmp { lhs, rhs, .. } => {
            op(lhs);
            op(rhs);
        }
        Condition::And(cs) | Condition::Or(cs) => cs.iter().for_each(|c| condition_operands(c, op)),
        Condition::Not(c) => condition_operands(c, op),
    }
}
