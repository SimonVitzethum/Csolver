//! The acyclic path-enumerating symbolic executor with a symbolic memory model.
//!
//! Each path carries a [`PathState`]: a symbolic register environment
//! (scalars and pointers), a per-path region table (so allocate/free is
//! path-sensitive), a path condition, and a set of assumed facts. At every
//! memory operation the executor decides the canonical safety obligations using
//! the path condition, the region table and the linear solver.
//!
//! This increment proves (`Proven`) or leaves open (`Unknown`) — it never
//! refutes, because a sound refutation needs a satisfiable model on a provably
//! reachable path, which the UNSAT-only solver cannot supply.

use crate::ExecLimits;
use csolver_absint::{
    analyze_induction, analyze_intervals, analyze_zones, Bound, EqExitIndVar, InductionAnalysis,
    IntervalAnalysis, PtrIndVar, ZoneAnalysis,
};
use csolver_cfg::{Dominators, Loops};
use csolver_core::{Model, RegionKind, SafetyProperty};
use crate::summary::{Affine, RetSummary, Summary};
use csolver_ir::{
    BasicBlock, BinOp, BlockId, Callee, CastOp, CmpOp, Condition, Const, DataLayout, FuncId,
    Function, Inst, MemKind, Operand, PtrContract, RValue, RegId, SizeSpec, Terminator, Type,
};
use csolver_memory::{AliasResult, LifetimeState, Permissions};
use csolver_solver::{
    bitprecise, prove_implies_method, BvOp, CmpOp as SCmp, ExprCtx, ExprId, ProofMethod,
};
use std::collections::{HashMap, HashSet};

const PTR_WIDTH: u32 = 64;
const LAYOUT: DataLayout = DataLayout::LP64;
/// The largest valid allocation/offset magnitude: `isize::MAX`. A successful
/// allocation (or a valid Rust slice/reference) has a byte size in
/// `[0, isize::MAX]` — the allocator and `Layout` guarantee it — so its element
/// count times the element size does not wrap. Recording this lets a memory-OOB
/// counterexample over a *symbolic*-size region stay faithful (no wrapped
/// `count * stride` fabricating a too-small buffer).
const ISIZE_MAX: u128 = i64::MAX as u128;

/// Named assumptions a symbolic proof may rely on.
const ALLOC_SUCCEEDS: &str = "alloc-succeeds";
const LINEAR_NO_OVERFLOW: &str = "linear-no-overflow";
const PARAM_CONTRACTS: &str = "param-contracts";
const SLICE_ABI: &str = "slice-abi";

/// Whether a scalar `SafetyCheck` was discharged symbolically.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymOutcome {
    /// Proved on every path that reaches it.
    Proven,
    /// Not proved.
    Unknown,
    /// Refuted: on an exact (genuinely reachable) path the property is *always*
    /// violated, witnessed by the concrete model.
    Refuted(Model),
}

/// The decision for one implied memory-op obligation.
#[derive(Debug, Clone)]
pub struct MemDecision {
    /// Whether it was proved (on every reaching path).
    pub proven: bool,
    /// A concrete counterexample, when the obligation was *refuted* on an exact
    /// path (a definite violation). `None` for proved or merely-undecided.
    pub refutation: Option<Model>,
    /// A human-readable rendering of what was (or would be) shown.
    pub predicate: String,
    /// Why it is not proved (empty when proved).
    pub residual: String,
}

/// The result of symbolically discharging a function.
#[derive(Debug, Clone, Default)]
pub struct SymbolicReport {
    /// Decisions for explicit `SafetyCheck` instructions, keyed by (block, idx).
    pub decided: HashMap<(BlockId, usize), SymOutcome>,
    /// Decisions for implied memory-op obligations, keyed by (block, idx, prop).
    pub mem: HashMap<(BlockId, usize, SafetyProperty), MemDecision>,
    /// Named assumptions the proofs depend on.
    pub assumptions: Vec<String>,
    /// Whether exploration was truncated (then no decisions are reported).
    pub truncated: bool,
}

impl SymbolicReport {
    /// The outcome for an explicit `SafetyCheck`.
    pub fn outcome(&self, block: BlockId, index: usize) -> Option<SymOutcome> {
        self.decided.get(&(block, index)).cloned()
    }

    /// The decision for an implied memory obligation.
    pub fn mem_decision(
        &self,
        block: BlockId,
        index: usize,
        prop: SafetyProperty,
    ) -> Option<&MemDecision> {
        self.mem.get(&(block, index, prop))
    }
}

/// Symbolically discharge the obligations of `f` (default limits, no
/// interprocedural summaries — calls are havoc'd).
pub fn discharge_function(f: &Function) -> SymbolicReport {
    discharge_inner(f, ExecLimits::default(), &HashMap::new(), &[])
}

/// As [`discharge_function`], but using the given function summaries to reason
/// about calls (provenance-preserving returns, effect-aware heap handling).
pub fn discharge_with_summaries(
    f: &Function,
    summaries: &HashMap<FuncId, Summary>,
) -> SymbolicReport {
    discharge_inner(f, ExecLimits::default(), summaries, &[])
}

/// As [`discharge_with_summaries`], plus per-parameter pointer contracts: a
/// contracted pointer parameter is modelled as a known live region of its
/// `dereferenceable` size, so accesses through it can be proved (under the
/// `param-contracts` assumption).
pub fn discharge_full(
    f: &Function,
    summaries: &HashMap<FuncId, Summary>,
    contracts: &[Option<PtrContract>],
) -> SymbolicReport {
    discharge_inner(f, ExecLimits::default(), summaries, contracts)
}

/// As [`discharge_function`], with explicit limits and no summaries.
///
/// Loops are handled by *cutting* back-edges and replacing each loop header's
/// parameters with fresh symbols constrained by the sound interval invariant at
/// that header (from `csolver-absint`). One symbolic pass over the loop body —
/// under that invariant plus the loop guard (a path condition) — therefore
/// covers every iteration.
pub fn discharge_with(f: &Function, limits: ExecLimits) -> SymbolicReport {
    discharge_inner(f, limits, &HashMap::new(), &[])
}

fn discharge_inner(
    f: &Function,
    limits: ExecLimits,
    summaries: &HashMap<FuncId, Summary>,
    contracts: &[Option<PtrContract>],
) -> SymbolicReport {
    let analysis = analyze_intervals(f);
    let zones = analyze_zones(f);
    let inductions = analyze_induction(f);
    let dominators = Dominators::new(analysis.cfg());
    let loops = Loops::detect(analysis.cfg(), &dominators);

    // Per loop header: the set of registers the loop body may redefine (so they
    // can be havoc'd — not just the header's own parameters), and whether the
    // body may free memory (so region lifetimes can be invalidated). These are
    // what make a single body pass a *sound* over-approximation of all
    // iterations.
    let mut headers: HashSet<BlockId> = HashSet::new();
    let mut loop_modified: HashMap<BlockId, Vec<RegId>> = HashMap::new();
    let mut loop_frees: HashMap<BlockId, bool> = HashMap::new();
    for l in loops.all() {
        let header = analysis.cfg().block_id(l.header);
        headers.insert(header);
        let mut modified: HashSet<RegId> = HashSet::new();
        let mut frees = false;
        for &node in &l.body {
            let bid = analysis.cfg().block_id(node);
            if let Some(b) = f.block(bid) {
                modified.extend(b.params.iter().map(|(r, _)| *r));
                for inst in &b.insts {
                    if let Some(r) = inst.defined_reg() {
                        modified.insert(r);
                    }
                    if matches!(inst, Inst::Dealloc { .. }) {
                        frees = true;
                    }
                }
            }
        }
        loop_modified.insert(header, modified.into_iter().collect());
        loop_frees.insert(header, frees);
    }

    let mut ex = Explorer {
        ctx: ExprCtx::new(),
        fresh: 0,
        visits: 0,
        truncated: false,
        limits,
        scalar: HashMap::new(),
        mem: HashMap::new(),
        assumptions: HashSet::new(),
        analysis,
        zones,
        inductions,
        dominators,
        headers,
        loop_modified,
        loop_frees,
        summaries: summaries.clone(),
        f,
    };

    let mut env: HashMap<RegId, SymValue> = HashMap::new();
    let mut regions: Vec<SymRegion> = Vec::new();
    let mut facts: Vec<ExprId> = Vec::new();
    // Pass 1: every parameter without a pointer contract (so length parameters
    // a slice contract refers to are available in pass 2).
    for (i, (reg, ty)) in f.params.iter().enumerate() {
        if contracts.get(i).and_then(|c| c.as_ref()).is_none() {
            // Name scalar parameters `arg{i}` so a counterexample model is
            // readable; pointer parameters get the usual opaque placeholder.
            let v = if ty.is_ptr() {
                ex.fresh_value(ty)
            } else {
                SymValue::Scalar(ex.ctx.symbol(format!("arg{i}"), type_width(ty)))
            };
            env.insert(*reg, v);
        }
    }
    // Pass 2: contracted pointer parameters become known live regions.
    for (i, (reg, _ty)) in f.params.iter().enumerate() {
        let Some(c) = contracts.get(i).and_then(|c| c.as_ref()) else {
            continue;
        };
        let (size, assumption, nowrap) = match c.size {
            // A concrete byte size cannot wrap; nothing extra is needed (`true`).
            SizeSpec::Bytes(n) => {
                let truth = ex.ctx.boolean(true);
                (ex.ctx.int(PTR_WIDTH, n as u128), PARAM_CONTRACTS, truth)
            }
            SizeSpec::ParamElements { len_param, elem_size } => {
                let len_reg = f.params[len_param as usize].0;
                let len_e = match env.get(&len_reg) {
                    Some(SymValue::Scalar(e)) => *e,
                    _ => ex.fresh_scalar(PTR_WIDTH),
                };
                let es = ex.ctx.int(PTR_WIDTH, elem_size as u128);
                let size = ex.ctx.bin(BvOp::Mul, len_e, es);
                // A valid slice has `len * size_of::<T>() <= isize::MAX`, so the
                // length times the element size does not wrap (`slice-abi`).
                let nowrap = ex.size_no_wrap_fact(len_e, elem_size);
                (size, SLICE_ABI, nowrap)
            }
        };
        let zero = ex.ctx.int(PTR_WIDTH, 0);
        let nonneg = ex.ctx.cmp(SCmp::Sle, zero, size);
        facts.push(nonneg);
        let rid = regions.len();
        regions.push(SymRegion {
            kind: RegionKind::Heap,
            size,
            state: LifetimeState::Live,
            perms: Permissions {
                read: c.readable,
                write: c.writable,
                exec: false,
            },
            contract: Some(assumption),
            size_nowrap: Some(nowrap),
        });
        env.insert(
            *reg,
            SymValue::Ptr(SymPointer {
                prov: Prov::Region(rid),
                offset: zero,
                align: c.align.max(1) as u64,
            }),
        );
    }
    let state = PathState {
        env,
        regions,
        pathcond: Vec::new(),
        facts,
        heap: Vec::new(),
        exact: true,
    };
    ex.run_merged(state);

    if ex.truncated {
        return SymbolicReport {
            truncated: true,
            ..Default::default()
        };
    }

    let decided = ex
        .scalar
        .into_iter()
        .map(|(k, agg)| {
            let outcome = match agg.refutation {
                Some(model) => SymOutcome::Refuted(model),
                None if agg.all_proven => SymOutcome::Proven,
                None => SymOutcome::Unknown,
            };
            (k, outcome)
        })
        .collect();
    let mem = ex
        .mem
        .into_iter()
        .map(|(k, agg)| {
            (
                k,
                MemDecision {
                    proven: agg.all_proven,
                    refutation: agg.refutation,
                    predicate: agg.predicate,
                    residual: if agg.all_proven { String::new() } else { agg.residual },
                },
            )
        })
        .collect();
    let mut assumptions: Vec<String> = ex.assumptions.into_iter().map(String::from).collect();
    assumptions.sort();

    SymbolicReport {
        decided,
        mem,
        assumptions,
        truncated: false,
    }
}

/// Provenance of a symbolic pointer.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Prov {
    Null,
    Region(usize),
    Unknown,
}

#[derive(Debug, Clone)]
struct SymPointer {
    prov: Prov,
    offset: ExprId,
    align: u64,
}

#[derive(Debug, Clone)]
struct SymRegion {
    #[allow(dead_code)]
    kind: RegionKind,
    size: ExprId,
    state: LifetimeState,
    perms: Permissions,
    /// If this region models a caller-guaranteed pointer parameter, the named
    /// assumption its validity rests on (`param-contracts` / `slice-abi`);
    /// `None` for a freshly-allocated region (which rests on `alloc-succeeds`).
    contract: Option<&'static str>,
    /// `Some(fact)` when the byte size is known not to wrap (`fact` is the
    /// `count <= isize::MAX/stride` premise, trivially `true` for a concrete
    /// size). Then a memory-OOB obligation over the region is **refutable** with
    /// a faithful witness, with `fact` added to the refutation query only (not to
    /// the proving assumptions, to keep proofs cheap). `None` ⇒ not refutable.
    size_nowrap: Option<ExprId>,
}

#[derive(Debug, Clone)]
enum SymValue {
    Scalar(ExprId),
    Ptr(SymPointer),
}

/// Captured data for asserting a pointer equality-exit induction's offset bound
/// (`iter != end`), taken before the loop header havoc clobbers `iter`.
struct PtrIndCapture {
    /// The induction pointer register (a header block-parameter).
    reg: RegId,
    /// The allocation `iter` walks within.
    region: usize,
    /// `iter`'s start offset (its preheader value's offset).
    b0: ExprId,
    /// `iter`'s start alignment.
    align: u64,
    /// The end pointer's offset within the same allocation.
    end_off: ExprId,
    /// The allocation's byte size.
    size: ExprId,
    /// The per-iteration byte stride (`elem size × element step`).
    stride_bytes: u64,
    /// `true` for the rotated form (load precedes the `next == end` check): the
    /// bound is `o + stride ≤ end_off` and its base case is proved from the
    /// preheader guard. `false` for the header-test form (`o ≤ end_off`).
    bottom_test: bool,
}

/// Where a loaded value comes from, per the store log (most-recent-first scan).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LoadOrigin {
    /// A prior store definitely determines the value (`Must` alias).
    Stored,
    /// A prior store *might* determine it (`May` alias) — value is unknown.
    Uncertain,
    /// No store reaches this location (every record is `No` alias): the bytes
    /// are whatever the region held at allocation. For a freshly-allocated
    /// region that is *uninitialized* memory.
    Unwritten,
}

/// A recorded store: "`size` bytes equal to `value` were written through
/// `target`". Most-recent-last.
#[derive(Clone)]
struct StoreRecord {
    target: SymPointer,
    value: SymValue,
    size: u64,
}

#[derive(Clone)]
struct PathState {
    env: HashMap<RegId, SymValue>,
    regions: Vec<SymRegion>,
    pathcond: Vec<ExprId>,
    facts: Vec<ExprId>,
    /// The symbolic store, in program order (for read-your-writes).
    heap: Vec<StoreRecord>,
    /// Whether this path is *exact*: no over-approximation (loop-header havoc,
    /// opaque call, or non-determined load) has been introduced. A symbolic
    /// **refutation** (sound `FAIL` + counterexample) is only emitted on an
    /// exact path, where the path condition characterizes genuinely reachable
    /// states, so a violating model is a real execution. Proofs (`PASS`) do not
    /// need this — over-approximation is sound for proving.
    exact: bool,
}

/// One incoming control-flow edge into a block, queued during the reverse-
/// postorder walk: the predecessor's post-state, the edge's guard (the branch
/// condition under which it is taken; `None` for an unconditional `Br`), and the
/// block-parameter arguments it supplies.
struct EdgeState {
    pred_state: PathState,
    guard: Option<ExprId>,
    args: Vec<Operand>,
}

/// Per-obligation aggregation across paths.
struct MemAgg {
    all_proven: bool,
    /// A counterexample from any path that definitely violated the obligation.
    refutation: Option<Model>,
    predicate: String,
    residual: String,
}

/// Per scalar-check aggregation across paths.
struct ScalarAgg {
    /// Proved on every path so far.
    all_proven: bool,
    /// A counterexample from any path that definitely violated the check.
    refutation: Option<Model>,
}

/// The outcome of deciding a safety goal on one path.
enum Decision {
    /// Proved to hold.
    Proven,
    /// Neither proved nor (soundly) refuted.
    Unknown,
    /// Violated on this exact path, witnessed by the model.
    Refuted(Model),
}

/// How aggressively a goal may be refuted (see [`Explorer::try_refute`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RefuteMode {
    /// Never refute (prove-only).
    Off,
    /// Refute only a goal that is *always* violated on the path.
    Definite,
    /// Refute a goal violated by *some* reaching input (the operation executes,
    /// so any such input is a real runtime violation).
    Possible,
}

struct Explorer<'f> {
    ctx: ExprCtx,
    fresh: u32,
    visits: usize,
    truncated: bool,
    limits: ExecLimits,
    /// Scalar `SafetyCheck` aggregation, keyed by (block, idx).
    scalar: HashMap<(BlockId, usize), ScalarAgg>,
    mem: HashMap<(BlockId, usize, SafetyProperty), MemAgg>,
    assumptions: HashSet<&'static str>,
    /// Sound interval invariants (the source of loop invariants).
    analysis: IntervalAnalysis,
    /// Relational (zone) invariants — difference constraints between registers
    /// that the per-register interval domain cannot express.
    zones: ZoneAnalysis,
    /// Equality-exit induction variables (`while i != n`), whose `start ≤ i ≤ n`
    /// bound the interval domain cannot derive from a `!=` guard.
    inductions: InductionAnalysis,
    dominators: Dominators,
    /// Block ids that are loop headers.
    headers: HashSet<BlockId>,
    /// Per loop header: registers the loop body may redefine (havoc set).
    loop_modified: HashMap<BlockId, Vec<RegId>>,
    /// Per loop header: whether the loop body may free memory.
    loop_frees: HashMap<BlockId, bool>,
    /// Interprocedural summaries, by callee id (empty = havoc all calls).
    summaries: HashMap<FuncId, Summary>,
    f: &'f Function,
}

impl Explorer<'_> {
    fn fresh_scalar(&mut self, width: u32) -> ExprId {
        let name = format!("?{}", self.fresh);
        self.fresh += 1;
        self.ctx.symbol(name, width)
    }

    fn fresh_value(&mut self, ty: &Type) -> SymValue {
        if ty.is_ptr() {
            SymValue::Ptr(SymPointer {
                prov: Prov::Unknown,
                offset: self.ctx.int(PTR_WIDTH, 0),
                align: 1,
            })
        } else {
            SymValue::Scalar(self.fresh_scalar(type_width(ty)))
        }
    }

    /// Drive the analysis over the (back-edge-cut) CFG in **reverse postorder**,
    /// processing **each block exactly once**. Every non-back-edge predecessor is
    /// processed before a block, so its incoming edge-states are all available and
    /// **merged** into one entry state (see [`Explorer::merge_edges`]). This
    /// collapses the per-path explosion of the old recursive walk: a join with N
    /// predecessors is analysed once instead of once per path, so wide CFGs no
    /// longer blow up the path count (or trip the visit budget into truncation).
    fn run_merged(&mut self, entry_state: PathState) {
        let rpo: Vec<BlockId> = {
            let cfg = self.analysis.cfg();
            cfg.reverse_postorder().into_iter().map(|n| cfg.block_id(n)).collect()
        };
        let mut incoming: HashMap<BlockId, Vec<EdgeState>> = HashMap::new();
        incoming.insert(
            self.f.entry,
            vec![EdgeState { pred_state: entry_state, guard: None, args: Vec::new() }],
        );

        for block in rpo {
            if self.truncated {
                return;
            }
            let Some(edges) = incoming.remove(&block) else {
                continue; // unreachable in the DAG (or all incoming edges pruned)
            };
            if edges.is_empty() {
                continue;
            }
            self.visits += 1;
            if self.visits > self.limits.max_visits {
                self.truncated = true;
                return;
            }

            let mut state = self.merge_edges(block, edges);
            // At a loop header, over-approximate every iteration by replacing the
            // loop-carried parameters with fresh symbols constrained by the sound
            // interval invariant.
            if self.headers.contains(&block) {
                self.havoc_header(block, &mut state);
            }
            let Some(b) = self.f.block(block) else {
                continue;
            };
            for (idx, inst) in b.insts.iter().enumerate() {
                self.step(block, idx, inst, &mut state);
            }
            self.propagate_edges(block, b, state, &mut incoming);
        }
    }

    /// Push the out-edges of `block` (with their guards / block-parameter args) to
    /// the successors' incoming sets. Back-edges are cut; a branch whose guard is
    /// bit-precisely unreachable is pruned (see [`Explorer::branch_infeasible`]).
    fn propagate_edges(
        &mut self,
        block: BlockId,
        b: &BasicBlock,
        state: PathState,
        incoming: &mut HashMap<BlockId, Vec<EdgeState>>,
    ) {
        match &b.term {
            Terminator::Return(_) | Terminator::Unreachable => {}
            Terminator::Br { target, args } => {
                if !self.is_back_edge(block, *target) {
                    incoming.entry(*target).or_default().push(EdgeState {
                        pred_state: state,
                        guard: None,
                        args: args.clone(),
                    });
                }
            }
            Terminator::CondBr { cond, then_blk, then_args, else_blk, else_args } => {
                let ce = self.eval_scalar(cond, &state);
                let nce = self.ctx.not(ce);
                if !self.is_back_edge(block, *then_blk) && !self.branch_infeasible(ce, &state) {
                    incoming.entry(*then_blk).or_default().push(EdgeState {
                        pred_state: state.clone(),
                        guard: Some(ce),
                        args: then_args.clone(),
                    });
                }
                if !self.is_back_edge(block, *else_blk) && !self.branch_infeasible(nce, &state) {
                    incoming.entry(*else_blk).or_default().push(EdgeState {
                        pred_state: state,
                        guard: Some(nce),
                        args: else_args.clone(),
                    });
                }
            }
            Terminator::Switch { value, cases, default } => {
                let ve = self.eval_scalar(value, &state);
                for (cv, target) in cases {
                    if self.is_back_edge(block, *target) {
                        continue;
                    }
                    let k = self.ctx.constant(*cv);
                    let eq = self.ctx.cmp(SCmp::Eq, ve, k);
                    if self.branch_infeasible(eq, &state) {
                        continue;
                    }
                    incoming.entry(*target).or_default().push(EdgeState {
                        pred_state: state.clone(),
                        guard: Some(eq),
                        args: Vec::new(),
                    });
                }
                if !self.is_back_edge(block, *default) {
                    incoming.entry(*default).or_default().push(EdgeState {
                        pred_state: state,
                        guard: None,
                        args: Vec::new(),
                    });
                }
            }
        }
    }

    /// Merge the incoming edge-states of a block into one entry state. A single
    /// predecessor is applied precisely (its guard and block-param args); multiple
    /// predecessors are joined by [`Explorer::merge_multi`].
    fn merge_edges(&mut self, block: BlockId, mut edges: Vec<EdgeState>) -> PathState {
        if edges.len() == 1 {
            let e = edges.swap_remove(0);
            let mut s = e.pred_state;
            if let Some(g) = e.guard {
                s.pathcond.push(g);
            }
            self.bind_params_into(block, &e.args, &mut s);
            return s;
        }
        self.merge_multi(block, edges)
    }

    /// Bind a block's parameters from the incoming `args`, evaluated in `s`.
    fn bind_params_into(&mut self, block: BlockId, args: &[Operand], s: &mut PathState) {
        let params = self.f.block(block).map(|b| b.params.clone()).unwrap_or_default();
        let vals: Vec<SymValue> = (0..params.len())
            .map(|j| match args.get(j) {
                Some(a) => self.eval_value(a, s),
                None => self.fresh_value(&params[j].1),
            })
            .collect();
        for ((preg, _), v) in params.iter().zip(vals) {
            s.env.insert(*preg, v);
        }
    }

    /// Join several incoming edge-states. Block parameters (PHIs) are merged with
    /// an `ITE` keyed on each edge's discriminating condition (its full path
    /// condition); the rest is over-approximated by [`Explorer::merge_core`].
    fn merge_multi(&mut self, block: BlockId, edges: Vec<EdgeState>) -> PathState {
        // Each edge's discriminator: the conjunction of its path condition (plus
        // its branch guard) — the condition under which control arrives by it.
        let discs: Vec<ExprId> = edges
            .iter()
            .map(|e| {
                let mut conds = e.pred_state.pathcond.clone();
                if let Some(g) = e.guard {
                    conds.push(g);
                }
                self.ctx.and(conds)
            })
            .collect();

        let mut merged = self.merge_core(&edges);

        let params = self.f.block(block).map(|b| b.params.clone()).unwrap_or_default();
        for (j, (preg, pty)) in params.iter().enumerate() {
            let vals: Vec<(ExprId, SymValue)> = edges
                .iter()
                .zip(&discs)
                .map(|(e, &d)| {
                    let v = match e.args.get(j) {
                        Some(a) => self.eval_value(a, &e.pred_state),
                        None => self.fresh_value(pty),
                    };
                    (d, v)
                })
                .collect();
            let mv = self.merge_values(&vals, pty);
            merged.env.insert(*preg, mv);
        }
        merged
    }

    /// The non-parameter part of a multi-predecessor merge: a sound
    /// over-approximation of all incoming states. Regions keep the common prefix
    /// (identical byte size) with a conservative lifetime (`Live` only if live on
    /// every edge); the register environment is taken from the first edge (in SSA
    /// the registers live past a join are defined before the split, hence equal),
    /// sanitizing any pointer into a dropped region; the path condition is the
    /// longest common prefix and the facts their intersection (both sound,
    /// weaker); the heap is forgotten and the path is no longer `exact`.
    fn merge_core(&self, edges: &[EdgeState]) -> PathState {
        let first = &edges[0].pred_state;

        let mut regions = Vec::new();
        'prefix: for i in 0..first.regions.len() {
            let size = first.regions[i].size;
            for e in edges {
                match e.pred_state.regions.get(i) {
                    Some(r) if r.size == size => {}
                    _ => break 'prefix,
                }
            }
            let live_all = edges
                .iter()
                .all(|e| e.pred_state.regions[i].state == LifetimeState::Live);
            let mut r = first.regions[i].clone();
            r.state = if live_all { LifetimeState::Live } else { LifetimeState::Freed };
            regions.push(r);
        }
        let rcount = regions.len();

        let mut env = first.env.clone();
        for v in env.values_mut() {
            if let SymValue::Ptr(p) = v {
                if let Prov::Region(rid) = p.prov {
                    if rid >= rcount {
                        p.prov = Prov::Unknown;
                    }
                }
            }
        }

        let mut pathcond = Vec::new();
        for k in 0..first.pathcond.len() {
            let c = first.pathcond[k];
            if edges.iter().all(|e| e.pred_state.pathcond.get(k) == Some(&c)) {
                pathcond.push(c);
            } else {
                break;
            }
        }

        let facts: Vec<ExprId> = first
            .facts
            .iter()
            .copied()
            .filter(|f| edges.iter().all(|e| e.pred_state.facts.contains(f)))
            .collect();

        PathState { env, regions, pathcond, facts, heap: Vec::new(), exact: false }
    }

    /// Merge per-edge values into one, as a right-folded `ITE` over the edge
    /// discriminators (the last edge is the final `else`).
    fn merge_values(&mut self, vals: &[(ExprId, SymValue)], ty: &Type) -> SymValue {
        let Some((_, last)) = vals.last().cloned() else {
            return self.fresh_value(ty);
        };
        let mut acc = last;
        for (d, v) in vals[..vals.len() - 1].iter().rev() {
            acc = self.select(*d, v.clone(), acc, ty);
        }
        acc
    }

    /// `select(d, a, b)` = `if d then a else b`, structurally: `ITE` on scalars
    /// and on same-provenance pointer offsets; differing provenance degrades to an
    /// opaque pointer (sound over-approximation).
    fn select(&mut self, d: ExprId, a: SymValue, b: SymValue, ty: &Type) -> SymValue {
        match (a, b) {
            (SymValue::Scalar(ea), SymValue::Scalar(eb)) => SymValue::Scalar(self.ctx.ite(d, ea, eb)),
            (SymValue::Ptr(pa), SymValue::Ptr(pb)) if pa.prov == pb.prov => SymValue::Ptr(SymPointer {
                prov: pa.prov,
                offset: self.ctx.ite(d, pa.offset, pb.offset),
                align: gcd(pa.align, pb.align),
            }),
            (SymValue::Ptr(_), SymValue::Ptr(_)) => SymValue::Ptr(SymPointer {
                prov: Prov::Unknown,
                offset: self.ctx.int(PTR_WIDTH, 0),
                align: 1,
            }),
            _ => self.fresh_value(ty),
        }
    }

    /// Whether `cond` is **bit-precisely** unsatisfiable under the current path,
    /// i.e. `pathcond ∧ facts ⟹ ¬cond` holds *exactly*. Then the branch guarded
    /// by `cond` has no concrete execution and is soundly pruned.
    ///
    /// The check is deliberately **bit-precise**, not linear: pruning on a
    /// `linear-no-overflow`-dependent implication could discard a branch that is
    /// actually reachable only through wraparound and so hide a real violation
    /// (a false PASS). A bit-precise `⟹ ¬cond` holds for *every* machine value,
    /// so the branch is genuinely dead. Missing a (linear-only) infeasibility
    /// just keeps a redundant path — never unsound.
    fn branch_infeasible(&mut self, cond: ExprId, state: &PathState) -> bool {
        let not_cond = self.ctx.not(cond);
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        bitprecise::prove_implies(&self.ctx, &assumptions, not_cond)
    }

    /// Whether the edge `from -> to` is a loop back-edge (cut during
    /// exploration). A back-edge targets a loop header that dominates its
    /// source.
    fn is_back_edge(&self, from: BlockId, to: BlockId) -> bool {
        if !self.headers.contains(&to) {
            return false;
        }
        let cfg = self.analysis.cfg();
        let (Some(fi), Some(ti)) = (cfg.index_of(from), cfg.index_of(to)) else {
            return false;
        };
        self.dominators.dominates(ti, fi)
    }

    /// Replace a loop header's parameters with fresh symbols constrained by the
    /// interval invariant that holds at the header on every iteration.
    fn havoc_header(&mut self, header: BlockId, state: &mut PathState) {
        // Havocking introduces over-approximation, so this path is no longer
        // exact: it may stand for unreachable states, so we must not refute on it.
        state.exact = false;
        // The loop may have written arbitrary memory across iterations, so the
        // stored-value knowledge is no longer reliable: forget it (sound
        // over-approximation; loads then return fresh unknowns).
        state.heap.clear();

        // Equality-exit induction variables (`while i != n { … i += c }`): capture
        // each one's start (its pre-havoc value) and bound now, before the havoc
        // below replaces it with a fresh symbol. The sound bound is asserted after
        // the havoc (see `assert_eq_exit_bound`).
        let inductions: Vec<(EqExitIndVar, ExprId, ExprId)> = self
            .inductions
            .eq_exit_indvars(header)
            .to_vec()
            .into_iter()
            .filter_map(|iv| {
                let start = match state.env.get(&iv.reg) {
                    Some(SymValue::Scalar(e)) => *e,
                    _ => return None,
                };
                let bound = self.eval_scalar(&iv.bound, state);
                Some((iv, start, bound))
            })
            .collect();

        // Pointer equality-exit induction (`iter != end`): capture each one's
        // base region/offset/alignment, the end pointer's offset in that same
        // region, and the region byte size — all before the havoc clobbers
        // `iter`. The bounded offset is installed after the havoc (see
        // `assert_ptr_walk_bound`).
        let ptr_inductions: Vec<PtrIndCapture> = self
            .inductions
            .eq_exit_ptr_indvars(header)
            .to_vec()
            .into_iter()
            .filter_map(|iv: PtrIndVar| {
                let SymValue::Ptr(base) = state.env.get(&iv.reg)?.clone() else { return None };
                let Prov::Region(region) = base.prov else { return None };
                let size = state.regions.get(region)?.size;
                let SymValue::Ptr(end) = self.eval_value(&iv.end, state) else { return None };
                let Prov::Region(end_region) = end.prov else { return None };
                if end_region != region {
                    return None; // end is in a different allocation: cannot relate
                }
                let elem_stride = iv.elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let stride_bytes = u64::try_from(iv.stride_elems).ok()?.checked_mul(elem_stride)?;
                Some(PtrIndCapture {
                    reg: iv.reg,
                    region,
                    b0: base.offset,
                    align: base.align,
                    end_off: end.offset,
                    size,
                    stride_bytes,
                    bottom_test: iv.bottom_test,
                })
            })
            .collect();

        // If the loop body may free memory, then on any iteration after the
        // first a region could already be freed — so no region's liveness can
        // be proved inside (or after) the loop. Invalidate liveness
        // conservatively. (Loops that never free are unaffected.)
        if self.loop_frees.get(&header).copied().unwrap_or(false) {
            for r in &mut state.regions {
                if r.state == LifetimeState::Live {
                    r.state = LifetimeState::Freed;
                }
            }
        }

        // Havoc *every* register the loop body may redefine — not just the
        // header's own parameters. In strict SSA the loop-carried values are
        // header parameters and the rest are recomputed before use, so this is
        // usually redundant; but it makes the analysis robust to non-SSA input
        // (a register reassigned in the body keeps no stale pre-loop value).
        let modified = self
            .loop_modified
            .get(&header)
            .cloned()
            .unwrap_or_default();
        for reg in modified {
            match state.env.get(&reg) {
                Some(SymValue::Ptr(_)) => {
                    // A loop-modified pointer loses provenance (conservative).
                    let offset = self.ctx.int(PTR_WIDTH, 0);
                    state.env.insert(
                        reg,
                        SymValue::Ptr(SymPointer { prov: Prov::Unknown, offset, align: 1 }),
                    );
                }
                Some(SymValue::Scalar(_)) => {
                    let s = self.fresh_scalar(PTR_WIDTH);
                    // Constrain by the sound interval invariant at the header
                    // (only faithfully-encodable, non-negative bounds).
                    let iv = self.analysis.entry_interval(header, reg);
                    if let Some(Bound::Fin(lo)) = iv.lower() {
                        if lo >= 0 {
                            let k = self.ctx.int(PTR_WIDTH, lo as u128);
                            let fact = self.ctx.cmp(SCmp::Sge, s, k);
                            state.facts.push(fact);
                        }
                    }
                    if let Some(Bound::Fin(hi)) = iv.upper() {
                        if hi >= 0 {
                            let k = self.ctx.int(PTR_WIDTH, hi as u128);
                            let fact = self.ctx.cmp(SCmp::Sle, s, k);
                            state.facts.push(fact);
                        }
                    }
                    state.env.insert(reg, SymValue::Scalar(s));
                }
                None => {} // not live at the header; defined fresh in the body
            }
        }

        // Relational (zone) invariants: difference constraints `a - b <= c`
        // between the freshly-havoc'd register values that hold on every header
        // visit (e.g. `j <= i`). These are exactly what the per-register interval
        // bounds above cannot express, so they let a loop whose safety is a
        // *relation* between variables (a second induction variable, `buf[j]`
        // with `j <= i < n`) be proved. Sound under the same `linear-no-overflow`
        // assumption as the interval facts.
        let diffs: Vec<(ExprId, ExprId, i128)> = self
            .zones
            .entry_diffs(header)
            .into_iter()
            .filter_map(|(a, b, c)| match (state.env.get(&a), state.env.get(&b)) {
                (Some(SymValue::Scalar(ea)), Some(SymValue::Scalar(eb))) => Some((*ea, *eb, c)),
                _ => None,
            })
            .collect();
        for (ea, eb, c) in diffs {
            // a - b <= c   ⟺   a <= b + c.
            let cexpr = self.const_expr(c);
            let rhs = self.ctx.bin(BvOp::Add, eb, cexpr);
            let fact = self.ctx.cmp(SCmp::Sle, ea, rhs);
            state.facts.push(fact);
        }

        // Equality-exit induction bounds: for each `while v != bound { … v += c }`
        // recognized at this header, assert `start ≤ v ≤ bound` on the now-havoc'd
        // `v` — after solver-checking the soundness side-conditions.
        for (iv, start_e, bound_e) in inductions {
            if let Some(SymValue::Scalar(v)) = state.env.get(&iv.reg).cloned() {
                self.assert_eq_exit_bound(state, v, start_e, bound_e, iv.stride);
            }
        }

        // Pointer-walk (`iter != end`) bounds: install the region-bounded offset
        // for each recognized pointer induction, replacing the conservative
        // opaque pointer the generic havoc produced.
        for cap in ptr_inductions {
            self.assert_ptr_walk_bound(state, cap);
        }
    }

    /// Install the sound offset bound for a pointer equality-exit induction. The
    /// generic havoc made `iter` opaque; here — only after **proving** the
    /// side-conditions — we restore its region provenance with a fresh offset `o`
    /// constrained by `b0 ≤ o`, the congruence `o ≡ b0 (mod stride)`, and an upper
    /// bound that depends on the loop form:
    ///   - **header-test** (`bottom_test == false`): `o ≤ end_off`. The load is
    ///     guarded, so with the guard `iter != end` (`o != end_off`) the
    ///     congruence gives `o ≤ end_off − stride`, hence `o + stride ≤ end_off`.
    ///   - **bottom-test / rotated** (`bottom_test == true`): `o + stride ≤
    ///     end_off`. The load is unconditional, so this stronger invariant is
    ///     needed directly; its base case (`b0 + stride ≤ end_off`) is provable
    ///     only when the loop is entered non-empty — i.e. from the preheader
    ///     guard `base != end`, which sits in this header's path condition.
    ///
    /// The common side-conditions: `0 ≤ b0`, `end_off ≤ size ≤ isize::MAX`, and
    /// `stride | (end_off − b0)` (so `end` lies on the walk's grid — otherwise the
    /// pointer steps over `end`, never satisfies the `== end` exit, and the bound
    /// would be unsound). Only power-of-two strides (the element sizes that arise)
    /// get the exact bit-precise divisibility; others are skipped.
    fn assert_ptr_walk_bound(&mut self, state: &mut PathState, cap: PtrIndCapture) {
        let stride = cap.stride_bytes;
        if stride == 0 || !(stride as u128).is_power_of_two() {
            return;
        }
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let isize_max = self.ctx.int(PTR_WIDTH, i64::MAX as u128);
        let mask = self.ctx.int(PTR_WIDTH, (stride as u128) - 1);
        // `lo + d` is the largest accessed offset's lower witness: for the rotated
        // form the load happens at the unincremented pointer, so the invariant is
        // shifted by one stride (`d = stride`); the header-test form has `d = 0`.
        let plus_d = |s: &mut Self, e: ExprId| -> ExprId {
            if cap.bottom_test {
                let d = s.ctx.int(PTR_WIDTH, stride as u128);
                s.ctx.bin(BvOp::Add, e, d)
            } else {
                e
            }
        };
        // (end_off − b0) & mask == 0: end is on the walk's grid.
        let ediff = self.ctx.bin(BvOp::Sub, cap.end_off, cap.b0);
        let emask = self.ctx.bin(BvOp::And, ediff, mask);
        let end_on_grid = self.ctx.cmp(SCmp::Eq, emask, zero);
        let b0_upper = plus_d(self, cap.b0);
        let gate = [
            self.ctx.cmp(SCmp::Sle, zero, cap.b0),           // 0 ≤ b0
            self.ctx.cmp(SCmp::Sle, b0_upper, cap.end_off),  // b0 (+ stride) ≤ end_off
            self.ctx.cmp(SCmp::Sle, cap.end_off, cap.size),  // end_off ≤ size
            self.ctx.cmp(SCmp::Sle, cap.size, isize_max),    // size ≤ isize::MAX
            end_on_grid,
        ];
        // The region's no-wrap premise (`size = count·stride ≤ isize::MAX`) lets
        // `size ≤ isize::MAX` be proved for a *symbolic* slice length, and the
        // preheader guard (already in `pathcond`) is what makes the rotated form's
        // `b0 + stride ≤ end_off` provable. Both are read from the current state.
        let nowrap = state.regions.get(cap.region).and_then(|r| r.size_nowrap);
        let restore = state.facts.len();
        if let Some(nw) = nowrap {
            state.facts.push(nw);
        }
        let proved = gate.into_iter().all(|g| self.prove(g, state));
        state.facts.truncate(restore);
        if !proved {
            return;
        }
        // Sound: a region pointer at a fresh, grid-aligned, in-range offset.
        let o = self.fresh_scalar(PTR_WIDTH);
        state.env.insert(
            cap.reg,
            SymValue::Ptr(SymPointer {
                prov: Prov::Region(cap.region),
                offset: o,
                align: gcd(cap.align, stride),
            }),
        );
        let o_upper = plus_d(self, o);
        let odiff = self.ctx.bin(BvOp::Sub, o, cap.b0);
        let omask = self.ctx.bin(BvOp::And, odiff, mask);
        let ediff2 = self.ctx.bin(BvOp::Sub, cap.end_off, cap.b0);
        let emask2 = self.ctx.bin(BvOp::And, ediff2, mask);
        let facts = [
            self.ctx.cmp(SCmp::Sle, zero, cap.b0),          // 0 ≤ b0
            self.ctx.cmp(SCmp::Sle, cap.b0, o),             // b0 ≤ o
            self.ctx.cmp(SCmp::Sle, zero, o_upper),         // 0 ≤ o (+ stride) (no wrap)
            self.ctx.cmp(SCmp::Sle, o_upper, cap.end_off),  // o (+ stride) ≤ end_off
            self.ctx.cmp(SCmp::Sle, o_upper, cap.size),     // o (+ stride) ≤ size
            self.ctx.cmp(SCmp::Sle, cap.end_off, cap.size), // end_off ≤ size
            self.ctx.cmp(SCmp::Sle, cap.size, isize_max),   // size ≤ isize::MAX (no wrap)
            self.ctx.cmp(SCmp::Eq, omask, zero),            // o ≡ b0 (mod stride)
            self.ctx.cmp(SCmp::Eq, emask2, zero),           // end_off ≡ b0 (mod stride)
        ];
        state.facts.extend(facts);
    }

    /// Assert the sound bound `start ≤ v ≤ bound` for an equality-exit induction
    /// variable, but only after **proving** the side-conditions that make it a
    /// true loop invariant: `0 ≤ start ≤ bound ≤ isize::MAX` (the counter starts
    /// in range and the bound does not wrap), and `stride | (bound − start)` so
    /// `bound` lies on the grid `{start + k·stride}` — otherwise `v` steps *over*
    /// `bound`, never satisfies the `v == bound` exit, and could exceed `bound`
    /// (making the bound unsound). If any condition is not proved, nothing is
    /// asserted (sound fallback). The divisibility check is exact only for
    /// power-of-two strides (the element sizes that arise); other strides are
    /// skipped.
    fn assert_eq_exit_bound(
        &mut self,
        state: &mut PathState,
        v: ExprId,
        start: ExprId,
        bound: ExprId,
        stride: i128,
    ) {
        if stride <= 0 {
            return;
        }
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let isize_max = self.ctx.int(PTR_WIDTH, i64::MAX as u128);
        let mut gate = vec![
            self.ctx.cmp(SCmp::Sle, zero, start),     // 0 ≤ start
            self.ctx.cmp(SCmp::Sle, start, bound),    // start ≤ bound
            self.ctx.cmp(SCmp::Sle, bound, isize_max), // bound ≤ isize::MAX
        ];
        if stride > 1 {
            if !(stride as u128).is_power_of_two() {
                return; // non-power-of-two stride: divisibility not encodable exactly
            }
            // (bound − start) & (stride − 1) == 0  ⟺  stride | (bound − start).
            let mask = self.ctx.int(PTR_WIDTH, (stride as u128) - 1);
            let diff = self.ctx.bin(BvOp::Sub, bound, start);
            let masked = self.ctx.bin(BvOp::And, diff, mask);
            gate.push(self.ctx.cmp(SCmp::Eq, masked, zero));
        }
        if !gate.into_iter().all(|g| self.prove(g, state)) {
            return;
        }
        let f_lo = self.ctx.cmp(SCmp::Sle, start, v);
        let f_hi = self.ctx.cmp(SCmp::Sle, v, bound);
        state.facts.push(f_lo);
        state.facts.push(f_hi);
    }

    fn step(&mut self, block: BlockId, idx: usize, inst: &Inst, state: &mut PathState) {
        match inst {
            Inst::Assign { dst, value, .. } => {
                let v = self.eval_rvalue(value, state);
                state.env.insert(*dst, v);
            }
            Inst::Alloc { dst, region, elem, count, align } => {
                let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let count_e = self.eval_scalar(count, state);
                let stride_e = self.ctx.int(PTR_WIDTH, stride as u128);
                let size = self.ctx.bin(BvOp::Mul, count_e, stride_e);
                let perms = if *region == RegionKind::Global {
                    Permissions::READ_ONLY
                } else {
                    Permissions::READ_WRITE
                };
                // A successful allocation has size <= isize::MAX, so the element
                // count times the stride does not wrap (`alloc-succeeds`). Kept
                // off `facts` (it would slow every proof) and used only to make a
                // memory-OOB counterexample faithful.
                let nowrap = self.size_no_wrap_fact(count_e, stride);
                let rid = state.regions.len();
                state.regions.push(SymRegion {
                    kind: *region,
                    size,
                    state: LifetimeState::Live,
                    perms,
                    contract: None,
                    size_nowrap: Some(nowrap),
                });
                // The byte size is non-negative by construction.
                let zero = self.ctx.int(PTR_WIDTH, 0);
                let nonneg = self.ctx.cmp(SCmp::Sle, zero, size);
                state.facts.push(nonneg);
                state.env.insert(
                    *dst,
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: zero,
                        align: *align as u64,
                    }),
                );
            }
            Inst::PtrOffset { dst, base, index, elem } => {
                let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let base_ptr = self.eval_pointer(base, state);
                let index_e = self.eval_scalar(index, state);
                let stride_e = self.ctx.int(PTR_WIDTH, stride as u128);
                let delta = self.ctx.bin(BvOp::Mul, index_e, stride_e);
                let new_off = self.ctx.bin(BvOp::Add, base_ptr.offset, delta);
                // Alignment after the offset: for a *constant* index use the
                // concrete byte delta (so `buf(16-aligned) + 16` stays
                // 16-aligned); for a symbolic index fall back to the stride.
                let new_align = match self.ctx.as_const(index_e) {
                    Some(c) => {
                        let d = c.signed().wrapping_mul(stride as i128).unsigned_abs() as u64;
                        gcd(base_ptr.align, d)
                    }
                    None => gcd(base_ptr.align, stride),
                };
                let result = SymPointer {
                    prov: base_ptr.prov.clone(),
                    offset: new_off,
                    align: new_align,
                };
                self.check_ptr_arith(block, idx, &result, state);
                state.env.insert(*dst, SymValue::Ptr(result));
            }
            Inst::Load { dst, ty, ptr, align } => {
                let p = self.eval_pointer(ptr, state);
                let asize = ty.size_bytes(&LAYOUT).unwrap_or(1);
                self.check_access((block, idx), &p, asize, *align as u64, SafetyProperty::ValidRead, state);
                let exact_before = state.exact;
                let (value, origin) = self.load_value(&p, asize, ty, state);
                match origin {
                    LoadOrigin::Stored => {}
                    LoadOrigin::Uncertain => state.exact = false,
                    LoadOrigin::Unwritten => {
                        // No store reaches this location. For a freshly-allocated
                        // region that is a read of uninitialized memory (UB). On
                        // an exact path it is a definite violation, refutable with
                        // a faithful witness. (Compute the witness before dropping
                        // `exact` for the unknown value below.)
                        if exact_before && self.is_fresh_alloc(&p, state) {
                            if let Some(model) = self.feasibility_witness(state) {
                                self.record_uninit_read(block, idx, model);
                            }
                        }
                        state.exact = false;
                    }
                }
                state.env.insert(*dst, value);
            }
            Inst::Store { ty, ptr, value, align } => {
                let p = self.eval_pointer(ptr, state);
                let asize = ty.size_bytes(&LAYOUT).unwrap_or(1);
                self.check_access((block, idx), &p, asize, *align as u64, SafetyProperty::ValidWrite, state);
                let v = self.eval_value(value, state);
                state.heap.push(StoreRecord { target: p, value: v, size: asize });
            }
            Inst::Dealloc { ptr, .. } => {
                let p = self.eval_pointer(ptr, state);
                self.check_dealloc(block, idx, &p, state);
            }
            Inst::Call { dst, callee, args, ret_ty } => {
                self.step_call(dst.as_ref(), callee, args, ret_ty, state);
            }
            Inst::Intrinsic { dst: Some(d), .. } => {
                let s = self.fresh_scalar(PTR_WIDTH);
                state.env.insert(*d, SymValue::Scalar(s));
            }
            Inst::SafetyCheck { condition, .. } => {
                let goal = self.eval_condition(condition, state);
                let decision = self.decide(&[goal], state, RefuteMode::Definite, &[]);
                self.record_scalar(block, idx, decision);
            }
            Inst::MemIntrinsic { kind, dst, src, len } => {
                self.check_mem_intrinsic((block, idx), *kind, dst, src.as_ref(), len, state);
                // A bulk write invalidates the symbolic heap's stored values.
                state.heap.clear();
            }
            Inst::Intrinsic { dst: None, .. } | Inst::Asm { .. } => {}
        }
    }

    /// Check a `memcpy`/`memmove`/`memset`: the destination must be writable and
    /// in bounds for `len` bytes, and (for copy/move) the source readable and in
    /// bounds for `len` bytes. Each property is recorded as the conjunction over
    /// the touched pointers.
    fn check_mem_intrinsic(
        &mut self,
        at: (BlockId, usize),
        kind: MemKind,
        dst_op: &Operand,
        src_op: Option<&Operand>,
        len_op: &Operand,
        state: &PathState,
    ) {
        use SafetyProperty::*;
        let (block, idx) = at;
        let dst = self.eval_pointer(dst_op, state);
        let len_e = self.eval_scalar(len_op, state);
        let need_src = matches!(kind, MemKind::Copy | MemKind::Move);
        let src = if need_src {
            src_op.map(|s| self.eval_pointer(s, state))
        } else {
            None
        };

        // Snapshot region facts (copied out, so no borrow is held).
        let dst_facts = region_facts(&dst, state);
        let src_facts = src.as_ref().and_then(|p| region_facts(p, state));

        let dst_nn = dst_facts.is_some();
        let src_nn = !need_src || src_facts.is_some();
        self.record(block, idx, NoNullDeref, dst_nn && src_nn, "memcpy pointers are non-null", "a memcpy pointer may be null or have opaque provenance");

        let dst_live = dst_facts.is_some_and(|f| f.live);
        let src_live = !need_src || src_facts.is_some_and(|f| f.live);
        self.record(block, idx, NoUseAfterFree, dst_live && src_live, "memcpy regions are live", "a memcpy region may be freed");

        let dst_inb = dst_facts.is_some_and(|f| self.prove_in_bounds_len(dst.offset, len_e, f.size, state));
        let src_inb = match (need_src, &src, src_facts) {
            (false, _, _) => true,
            (true, Some(p), Some(f)) => self.prove_in_bounds_len(p.offset, len_e, f.size, state),
            _ => false,
        };
        self.record(block, idx, InBounds, dst_inb && src_inb, "memcpy stays within both regions", "could not prove the copy stays in bounds");

        let dst_w = dst_facts.is_some_and(|f| f.perms.write);
        self.record(block, idx, ValidWrite, dst_w, "destination is writable", "destination is not writable");
        if need_src {
            let src_r = src_facts.is_some_and(|f| f.perms.read);
            self.record(block, idx, ValidRead, src_r, "source is readable", "source is not readable");
        }

        // Surface the assumptions the touched regions rest on.
        if dst_nn && src_nn && dst_live && src_live {
            for f in [dst_facts, src_facts].into_iter().flatten() {
                self.assumptions.insert(f.contract.unwrap_or(ALLOC_SUCCEEDS));
            }
        }
    }

    /// Prove `0 <= offset && offset + len <= size` (a `len`-byte access).
    fn prove_in_bounds_len(&mut self, offset: ExprId, len: ExprId, size: ExprId, state: &PathState) -> bool {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let end = self.ctx.bin(BvOp::Add, offset, len);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let upper = self.ctx.cmp(SCmp::Sle, end, size);
        self.prove(lower, state) && self.prove(upper, state)
    }

    /// Handle a call using the callee's summary: effect-aware heap handling and
    /// a provenance-preserving return binding.
    fn step_call(
        &mut self,
        dst: Option<&RegId>,
        callee: &Callee,
        args: &[Operand],
        ret_ty: &Type,
        state: &mut PathState,
    ) {
        // A call is an over-approximation point (havoc'd heap/return unless a
        // precise summary applies); conservatively mark the path inexact so we
        // never refute through a call. Proofs are unaffected (this only gates
        // refutation, not PASS).
        state.exact = false;
        let argvals: Vec<SymValue> = args.iter().map(|a| self.eval_value(a, state)).collect();
        let summary = match callee {
            Callee::Direct(fid) => self.summaries.get(fid).cloned(),
            _ => None,
        };

        // Effects: a writing or freeing callee invalidates the symbolic heap;
        // a *freeing* callee additionally invalidates region liveness (we do
        // not know which region it freed, so no region's liveness can be proved
        // afterwards). Without this, a use after a freeing call would be a false
        // PASS.
        let (writes, frees) = summary.as_ref().map_or((true, true), |s| (s.writes, s.frees));
        if writes || frees {
            state.heap.clear();
        }
        if frees {
            for r in &mut state.regions {
                if r.state == LifetimeState::Live {
                    r.state = LifetimeState::Freed;
                }
            }
        }

        if let Some(d) = dst {
            let value = match summary.as_ref().map(|s| &s.ret) {
                Some(RetSummary::PtrFromArg { arg, offset }) => {
                    self.instantiate_ptr(*arg, offset, &argvals, ret_ty)
                }
                Some(RetSummary::Scalar(aff)) => {
                    SymValue::Scalar(self.instantiate_affine(aff, &argvals))
                }
                _ => self.fresh_value(ret_ty),
            };
            state.env.insert(*d, value);
        }
    }

    /// Rebuild a pointer return value `arg + offset(args)`, keeping `arg`'s
    /// provenance.
    fn instantiate_ptr(
        &mut self,
        arg: usize,
        offset: &Affine,
        argvals: &[SymValue],
        ret_ty: &Type,
    ) -> SymValue {
        match argvals.get(arg) {
            Some(SymValue::Ptr(base)) => {
                let delta = self.instantiate_affine(offset, argvals);
                let new_off = self.ctx.bin(BvOp::Add, base.offset, delta);
                SymValue::Ptr(SymPointer {
                    prov: base.prov.clone(),
                    offset: new_off,
                    align: base.align,
                })
            }
            _ => self.fresh_value(ret_ty),
        }
    }

    /// Build the expression `constant + Σ coeff_k · arg_k` in the solver context.
    fn instantiate_affine(&mut self, aff: &Affine, argvals: &[SymValue]) -> ExprId {
        let mut acc = self.const_expr(aff.constant);
        for (&k, &coeff) in &aff.terms {
            let arg = match argvals.get(k) {
                Some(SymValue::Scalar(e)) => *e,
                _ => self.fresh_scalar(PTR_WIDTH),
            };
            let c = self.const_expr(coeff);
            let term = self.ctx.bin(BvOp::Mul, arg, c);
            acc = self.ctx.bin(BvOp::Add, acc, term);
        }
        acc
    }

    /// A signed integer constant as a `PTR_WIDTH` expression (faithful for
    /// negatives via subtraction).
    fn const_expr(&mut self, v: i128) -> ExprId {
        if v >= 0 {
            self.ctx.int(PTR_WIDTH, v as u128)
        } else {
            let zero = self.ctx.int(PTR_WIDTH, 0);
            let mag = self.ctx.int(PTR_WIDTH, (-v) as u128);
            self.ctx.bin(BvOp::Sub, zero, mag)
        }
    }

    // --- obligation decisions ----------------------------------------------

    fn check_access(
        &mut self,
        at: (BlockId, usize),
        p: &SymPointer,
        asize: u64,
        aalign: u64,
        perm_prop: SafetyProperty,
        state: &PathState,
    ) {
        use SafetyProperty::*;
        let (block, idx) = at;
        // Null.
        let non_null = matches!(p.prov, Prov::Region(_));
        self.record(block, idx, NoNullDeref, non_null, "pointer is non-null", "pointer may be null or have opaque provenance");

        let Prov::Region(rid) = p.prov else {
            for prop in [NoUseAfterFree, InBounds, Alignment, perm_prop] {
                self.record(block, idx, prop, false, "requires known provenance", "pointer provenance is not tracked");
            }
            return;
        };
        let region = &state.regions[rid];
        let rstate = region.state;
        let rperms = region.perms;
        let rsize = region.size;
        let contract = region.contract;
        let size_nowrap = region.size_nowrap;

        // Use-after-free: on an exact path a `Freed` region was definitely
        // deallocated, so the access is a certain UAF — refuted with a witness.
        let live = rstate == LifetimeState::Live;
        self.record_temporal((block, idx), NoUseAfterFree, !live, state, "region is live", "region may be freed (use-after-free)");

        // In-bounds: 0 <= offset && offset + asize <= size. Refutable (a real
        // OOB witness) whenever the region's byte size is known not to wrap
        // (concrete, or a symbolic `count * stride` with the recorded
        // `count <= isize::MAX/stride` bound): then a satisfying violation is a
        // genuine reachable OOB, since the only remaining free variable is the
        // access offset and the size cannot be a wrapped too-small value.
        let conjuncts = self.in_bounds_conjuncts(p.offset, asize, rsize);
        let (mode, extra) = match size_nowrap {
            Some(fact) => (RefuteMode::Possible, vec![fact]),
            None => (RefuteMode::Off, vec![]),
        };
        let decision = self.decide(&conjuncts, state, mode, &extra);
        self.record_mem(block, idx, InBounds, decision, "access stays within the allocation", "could not prove the access stays in bounds");

        // Alignment (concrete).
        let aligned = aalign <= 1 || p.align.is_multiple_of(aalign);
        self.record(block, idx, Alignment, aligned, "address meets the required alignment", "could not prove the required alignment");

        // Permission.
        let granted = match perm_prop {
            ValidRead => rperms.read,
            ValidWrite => rperms.write,
            _ => true,
        };
        self.record(block, idx, perm_prop, granted, "region grants the access permission", "region does not grant the access permission");

        if non_null && live {
            self.assumptions.insert(contract.unwrap_or(ALLOC_SUCCEEDS));
        }
    }

    fn check_ptr_arith(&mut self, block: BlockId, idx: usize, p: &SymPointer, state: &PathState) {
        use SafetyProperty::ValidPointerArith;
        let Prov::Region(rid) = p.prov else {
            self.record(block, idx, ValidPointerArith, false, "requires known provenance", "pointer provenance is not tracked");
            return;
        };
        let rsize = state.regions[rid].size;
        let contract = state.regions[rid].contract;
        // In-object or one-past-end: 0 <= offset <= size. Refutation off here:
        // the *access* in-bounds check (in `check_access`) is the one that
        // carries the OOB counterexample; the intermediate pointer arithmetic is
        // only proved.
        let conjuncts = self.in_range_conjuncts(p.offset, rsize);
        let decision = self.decide(&conjuncts, state, RefuteMode::Off, &[]);
        let proven = matches!(decision, Decision::Proven);
        self.record_mem(block, idx, ValidPointerArith, decision, "result stays within the object (or one-past-end)", "could not prove the offset stays in-object");
        if proven {
            self.assumptions.insert(contract.unwrap_or(ALLOC_SUCCEEDS));
        }
    }

    fn check_dealloc(&mut self, block: BlockId, idx: usize, p: &SymPointer, state: &mut PathState) {
        use SafetyProperty::NoDoubleFree;
        let Prov::Region(rid) = p.prov else {
            self.record(block, idx, NoDoubleFree, false, "requires known provenance", "freed pointer provenance is not tracked");
            return;
        };
        if state.regions[rid].contract.is_some() {
            // Freeing caller-owned (borrowed) memory is not ours to prove safe.
            self.record(block, idx, NoDoubleFree, false, "caller-owned region", "freeing a borrowed (caller-owned) region is not provably valid");
            return;
        }
        let rstate = state.regions[rid].state;
        if rstate != LifetimeState::Live {
            // On an exact path the region was definitely freed already, so this
            // is a certain double free — refuted with a witness.
            self.record_temporal((block, idx), NoDoubleFree, true, state, "region must be live to free", "region may already be freed (double free)");
            return;
        }
        // Must free the base pointer (offset == 0).
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let goal = self.ctx.cmp(SCmp::Eq, p.offset, zero);
        let at_base = self.prove(goal, state);
        self.record(block, idx, NoDoubleFree, at_base, "frees the base of a live allocation exactly once", "could not prove the freed pointer is the live base");
        if at_base {
            self.assumptions.insert(ALLOC_SUCCEEDS);
            state.regions[rid].state = LifetimeState::Freed;
        }
    }

    /// The conjuncts of in-bounds: `0 <= offset` and `offset + asize <= size`.
    fn in_bounds_conjuncts(&mut self, offset: ExprId, asize: u64, size: ExprId) -> [ExprId; 2] {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let asize_e = self.ctx.int(PTR_WIDTH, asize as u128);
        let end = self.ctx.bin(BvOp::Add, offset, asize_e);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let upper = self.ctx.cmp(SCmp::Sle, end, size);
        [lower, upper]
    }

    /// The fact `count <=u isize::MAX / stride`, so `count * stride` does not
    /// wrap and the byte size is faithful. Sound under `alloc-succeeds` /
    /// `slice-abi` (a successful allocation / valid slice has a size that fits).
    fn size_no_wrap_fact(&mut self, count: ExprId, stride: u64) -> ExprId {
        let max_count = ISIZE_MAX / (stride.max(1) as u128);
        let bound = self.ctx.int(PTR_WIDTH, max_count);
        self.ctx.cmp(SCmp::Ule, count, bound)
    }

    /// The conjuncts of in-range: `0 <= offset` and `offset <= size`
    /// (one-past-end allowed).
    fn in_range_conjuncts(&mut self, offset: ExprId, size: ExprId) -> [ExprId; 2] {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let upper = self.ctx.cmp(SCmp::Sle, offset, size);
        [lower, upper]
    }

    /// Decide a (possibly conjunctive) safety goal on one path. Tries to **prove**
    /// it (`A ⟹ P ∧ Q` by proving each conjunct — the linear procedure only takes
    /// conjunctive goals); failing that, on an **exact** path, tries to **refute**
    /// it per `mode` and return a concrete counterexample. `extra` adds premises
    /// used *only* for the refutation query (e.g. a region's no-wrap bound) — not
    /// for proving, which stays cheap.
    fn decide(
        &mut self,
        conjuncts: &[ExprId],
        state: &PathState,
        mode: RefuteMode,
        extra: &[ExprId],
    ) -> Decision {
        if conjuncts.iter().all(|&g| self.prove(g, state)) {
            return Decision::Proven;
        }
        if mode != RefuteMode::Off && state.exact {
            if let Some(model) = self.try_refute(conjuncts, state, mode, extra) {
                return Decision::Refuted(model);
            }
        }
        Decision::Unknown
    }

    /// On an exact path, return a concrete witness of a violation, or `None`.
    ///
    /// - [`RefuteMode::Definite`] refutes only a **definite** violation
    ///   (`assumptions ⟹ ¬goal`, proved bit-precisely): the goal can never hold
    ///   on this path. Used for scalar `SafetyCheck`s, so a merely
    ///   *satisfiable-but-not-valid* check (e.g. an unconstrained `i < 8`) stays
    ///   `Unknown` rather than becoming a FAIL.
    /// - [`RefuteMode::Possible`] refutes whenever **some** reaching input
    ///   violates the goal (`assumptions ∧ ¬goal` is satisfiable). Used for
    ///   memory accesses: the access *executes*, so any reachable input that
    ///   makes it out of bounds is a definite runtime violation. Sound because
    ///   the model satisfies the (exact) path condition, hence is genuinely
    ///   reachable, and callers restrict it to concrete-size regions (so a
    ///   wrapped allocation size can't fabricate a too-small buffer).
    ///
    /// Either way the witness existing also confirms the path is feasible.
    fn try_refute(
        &mut self,
        conjuncts: &[ExprId],
        state: &PathState,
        mode: RefuteMode,
        extra: &[ExprId],
    ) -> Option<Model> {
        let goal = if conjuncts.len() == 1 {
            conjuncts[0]
        } else {
            self.ctx.and(conjuncts.to_vec())
        };
        let not_goal = self.ctx.not(goal);
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        assumptions.extend_from_slice(extra);
        // For a *definite* refutation, first require that the goal can never hold
        // on this (feasible, exact) path — proved bit-precisely. A *possible*
        // refutation skips this: any satisfiable violation is a real one.
        if mode == RefuteMode::Definite
            && !bitprecise::prove_implies(&self.ctx, &assumptions, not_goal)
        {
            return None;
        }
        // The witness is a model of `assumptions ∧ ¬goal`: it satisfies the path
        // condition (reachable) and falsifies the goal (violating).
        bitprecise::find_counterexample(&self.ctx, &assumptions, goal)
    }

    /// On an exact, **feasible** path, a model of the path condition — a witness
    /// that this program point is genuinely reached. `None` if the path is
    /// over-approximated or infeasible. Used to witness a *definite* temporal
    /// violation (use-after-free / double-free): the violation holds for every
    /// reaching input, so the reachability witness *is* the counterexample.
    fn feasibility_witness(&mut self, state: &PathState) -> Option<Model> {
        if !state.exact {
            return None;
        }
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        let never = self.ctx.boolean(false);
        bitprecise::find_counterexample(&self.ctx, &assumptions, never)
    }

    /// Record a temporal obligation (use-after-free / no-double-free) decided
    /// structurally from the region's lifetime state. On an **exact** path a
    /// region only reaches `Freed` through an explicit `Dealloc`, so a violating
    /// state there is a *definite* violation for every reaching input — `Refuted`
    /// with the feasibility witness. Off an exact path (a freeing call/loop only
    /// *may* have freed) it degrades to `Unknown`; a safe state is `Proven`.
    fn record_temporal(
        &mut self,
        at: (BlockId, usize),
        prop: SafetyProperty,
        violated: bool,
        state: &PathState,
        desc: &str,
        residual: &str,
    ) {
        let (block, idx) = at;
        if !violated {
            self.record(block, idx, prop, true, desc, residual);
            return;
        }
        match self.feasibility_witness(state) {
            Some(model) => {
                self.record_mem(block, idx, prop, Decision::Refuted(model), desc, residual)
            }
            None => self.record(block, idx, prop, false, desc, residual),
        }
    }

    /// Try to prove `goal` under the current path. Prefers the bit-precise
    /// procedure (exact, no overflow assumption); only when the proof falls back
    /// to the linear-integer model is `linear-no-overflow` recorded — so a goal
    /// decided bit-precisely yields a `PASS` with one fewer assumption.
    fn prove(&mut self, goal: ExprId, state: &PathState) -> bool {
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        match prove_implies_method(&self.ctx, &assumptions, goal) {
            Some(ProofMethod::BitPrecise) => true,
            Some(ProofMethod::Linear) => {
                self.assumptions.insert(LINEAR_NO_OVERFLOW);
                true
            }
            None => false,
        }
    }

    /// Resolve a load by scanning the symbolic store most-recent-first: a
    /// must-aliasing store supplies the value, a may-aliasing store makes the
    /// value ambiguous (fresh unknown), a no-aliasing store is skipped. This is
    /// what preserves a pointer's provenance across a store/load round-trip.
    /// Resolve a load against the store log, reporting both the value and its
    /// [`LoadOrigin`]. A value not pinned by a `Must`-aliasing store is a fresh
    /// unknown (an over-approximation); the caller drops `exact` for it, since a
    /// violating model could assign that unknown a value memory never holds.
    fn load_value(
        &mut self,
        p: &SymPointer,
        asize: u64,
        ty: &Type,
        state: &PathState,
    ) -> (SymValue, LoadOrigin) {
        for k in (0..state.heap.len()).rev() {
            let rec_size = state.heap[k].size;
            let target = state.heap[k].target.clone();
            match self.alias_check(&target, p, rec_size, asize, state) {
                AliasResult::No => continue,
                AliasResult::Must => return (state.heap[k].value.clone(), LoadOrigin::Stored),
                AliasResult::May => return (self.fresh_value(ty), LoadOrigin::Uncertain),
            }
        }
        (self.fresh_value(ty), LoadOrigin::Unwritten)
    }

    /// Does `p` point into a freshly-allocated region (one with no caller
    /// contract)? Such a region's bytes are *uninitialized* until written.
    fn is_fresh_alloc(&self, p: &SymPointer, state: &PathState) -> bool {
        match &p.prov {
            Prov::Region(rid) => state.regions.get(*rid).is_some_and(|r| r.contract.is_none()),
            _ => false,
        }
    }

    /// Record a definite read of uninitialized memory as a `ValidRead`
    /// refutation (UB: reading never-written allocated bytes). Overwrites any
    /// permission-worded predicate from `check_access` so the report names the
    /// real cause.
    fn record_uninit_read(&mut self, block: BlockId, idx: usize, model: Model) {
        let entry = self
            .mem
            .entry((block, idx, SafetyProperty::ValidRead))
            .or_insert(MemAgg {
                all_proven: true,
                refutation: None,
                predicate: String::new(),
                residual: String::new(),
            });
        entry.all_proven = false;
        entry.refutation.get_or_insert(model);
        entry.predicate = "reads initialized memory".to_string();
        entry.residual = "reads uninitialized (never-written) freshly-allocated memory".to_string();
    }

    /// Classify the alias relationship between two accesses `a` (`sizea` bytes)
    /// and `b` (`sizeb` bytes) under the current path condition.
    fn alias_check(
        &mut self,
        a: &SymPointer,
        b: &SymPointer,
        sizea: u64,
        sizeb: u64,
        state: &PathState,
    ) -> AliasResult {
        match (&a.prov, &b.prov) {
            (Prov::Region(r1), Prov::Region(r2)) if r1 == r2 => {
                // Same allocation: decide by offsets.
                let eq = self.ctx.cmp(SCmp::Eq, a.offset, b.offset);
                if sizea >= sizeb && self.prove(eq, state) {
                    return AliasResult::Must;
                }
                let asz = self.ctx.int(PTR_WIDTH, sizea as u128);
                let bsz = self.ctx.int(PTR_WIDTH, sizeb as u128);
                let a_end = self.ctx.bin(BvOp::Add, a.offset, asz);
                let b_end = self.ctx.bin(BvOp::Add, b.offset, bsz);
                let a_before_b = self.ctx.cmp(SCmp::Sle, a_end, b.offset);
                let b_before_a = self.ctx.cmp(SCmp::Sle, b_end, a.offset);
                if self.prove(a_before_b, state) || self.prove(b_before_a, state) {
                    return AliasResult::No;
                }
                AliasResult::May
            }
            // Distinct allocations never alias.
            (Prov::Region(_), Prov::Region(_)) => AliasResult::No,
            // Opaque or null provenance: be conservative.
            _ => AliasResult::May,
        }
    }

    fn record(
        &mut self,
        block: BlockId,
        idx: usize,
        prop: SafetyProperty,
        proven: bool,
        proven_desc: &str,
        residual: &str,
    ) {
        let entry = self.mem.entry((block, idx, prop)).or_insert(MemAgg {
            all_proven: true,
            refutation: None,
            predicate: proven_desc.to_string(),
            residual: residual.to_string(),
        });
        entry.all_proven &= proven;
    }

    /// Record a memory obligation decided as [`Decision`] (carrying a refutation
    /// model when definitely violated).
    fn record_mem(
        &mut self,
        block: BlockId,
        idx: usize,
        prop: SafetyProperty,
        decision: Decision,
        proven_desc: &str,
        residual: &str,
    ) {
        let entry = self.mem.entry((block, idx, prop)).or_insert(MemAgg {
            all_proven: true,
            refutation: None,
            predicate: proven_desc.to_string(),
            residual: residual.to_string(),
        });
        match decision {
            Decision::Proven => {}
            Decision::Unknown => entry.all_proven = false,
            Decision::Refuted(model) => {
                entry.all_proven = false;
                entry.refutation.get_or_insert(model);
            }
        }
    }

    /// Aggregate a scalar `SafetyCheck` decision across paths.
    fn record_scalar(&mut self, block: BlockId, idx: usize, decision: Decision) {
        let entry = self.scalar.entry((block, idx)).or_insert(ScalarAgg {
            all_proven: true,
            refutation: None,
        });
        match decision {
            Decision::Proven => {}
            Decision::Unknown => entry.all_proven = false,
            Decision::Refuted(model) => {
                entry.all_proven = false;
                entry.refutation.get_or_insert(model);
            }
        }
    }

    // --- expression evaluation ---------------------------------------------

    fn eval_value(&mut self, op: &Operand, state: &PathState) -> SymValue {
        match op {
            Operand::Reg(r) => match state.env.get(r) {
                Some(v) => v.clone(),
                None => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            },
            Operand::Const(Const::Int(bv)) => SymValue::Scalar(self.ctx.constant(*bv)),
            Operand::Const(Const::Null) => SymValue::Ptr(SymPointer {
                prov: Prov::Null,
                offset: self.ctx.int(PTR_WIDTH, 0),
                align: 1,
            }),
            Operand::Const(Const::Undef) => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            Operand::Const(Const::Symbol(name)) => {
                SymValue::Scalar(self.ctx.symbol(format!("@{name}"), PTR_WIDTH))
            }
        }
    }

    fn eval_scalar(&mut self, op: &Operand, state: &PathState) -> ExprId {
        let v = self.eval_value(op, state);
        self.scalarize(v)
    }

    /// A symbolic value as a scalar expression: a pointer of null provenance is
    /// `0`, any other pointer a fresh unknown (its numeric address is unknown).
    fn scalarize(&mut self, v: SymValue) -> ExprId {
        match v {
            SymValue::Scalar(e) => e,
            SymValue::Ptr(p) => match p.prov {
                Prov::Null => self.ctx.int(PTR_WIDTH, 0),
                _ => self.fresh_scalar(PTR_WIDTH),
            },
        }
    }

    /// Evaluate a comparison, treating two **same-allocation** pointer operands
    /// as a comparison of their offsets — so `iter != end` within one allocation
    /// becomes the offset relation the pointer-walk bounds reasoning needs.
    /// Pointers of differing or opaque provenance fall back to fresh scalars
    /// (sound: the result is simply unconstrained).
    fn eval_ptr_aware_cmp(
        &mut self,
        op: CmpOp,
        lhs: &Operand,
        rhs: &Operand,
        state: &PathState,
    ) -> ExprId {
        let lv = self.eval_value(lhs, state);
        let rv = self.eval_value(rhs, state);
        if let (SymValue::Ptr(pa), SymValue::Ptr(pb)) = (&lv, &rv) {
            if let (Prov::Region(ra), Prov::Region(rb)) = (&pa.prov, &pb.prov) {
                if ra == rb {
                    return self.ctx.cmp(map_cmpop(op), pa.offset, pb.offset);
                }
            }
        }
        let a = self.scalarize(lv);
        let b = self.scalarize(rv);
        self.ctx.cmp(map_cmpop(op), a, b)
    }

    fn eval_pointer(&mut self, op: &Operand, state: &PathState) -> SymPointer {
        match self.eval_value(op, state) {
            SymValue::Ptr(p) => p,
            SymValue::Scalar(_) => SymPointer {
                prov: Prov::Unknown,
                offset: self.ctx.int(PTR_WIDTH, 0),
                align: 1,
            },
        }
    }

    fn eval_rvalue(&mut self, rv: &RValue, state: &PathState) -> SymValue {
        match rv {
            RValue::Use(op) => self.eval_value(op, state),
            RValue::Bin { op, lhs, rhs } => {
                let a = self.eval_scalar(lhs, state);
                let b = self.eval_scalar(rhs, state);
                SymValue::Scalar(self.ctx.bin(map_binop(*op), a, b))
            }
            RValue::Cmp { op, lhs, rhs } => {
                SymValue::Scalar(self.eval_ptr_aware_cmp(*op, lhs, rhs, state))
            }
            RValue::Cast { op, operand, .. } => match op {
                CastOp::Bitcast => self.eval_value(operand, state),
                CastOp::IntToPtr => SymValue::Ptr(SymPointer {
                    prov: Prov::Unknown,
                    offset: self.ctx.int(PTR_WIDTH, 0),
                    align: 1,
                }),
                CastOp::ZExt | CastOp::SExt => match self.eval_value(operand, state) {
                    SymValue::Scalar(e) => SymValue::Scalar(e),
                    SymValue::Ptr(_) => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
                },
                CastOp::Trunc | CastOp::PtrToInt => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            },
        }
    }

    fn eval_condition(&mut self, cond: &Condition, state: &PathState) -> ExprId {
        match cond {
            Condition::True => self.ctx.boolean(true),
            Condition::Cmp { op, lhs, rhs } => self.eval_ptr_aware_cmp(*op, lhs, rhs, state),
            Condition::And(cs) => {
                let parts = cs.iter().map(|c| self.eval_condition(c, state)).collect();
                self.ctx.and(parts)
            }
            Condition::Or(cs) => {
                let parts = cs.iter().map(|c| self.eval_condition(c, state)).collect();
                self.ctx.or(parts)
            }
            Condition::Not(c) => {
                let inner = self.eval_condition(c, state);
                self.ctx.not(inner)
            }
        }
    }
}

fn type_width(ty: &Type) -> u32 {
    match ty {
        Type::Bool => 1,
        Type::Int { bits } => *bits,
        Type::Ptr { .. } => PTR_WIDTH,
        _ => PTR_WIDTH,
    }
}

/// The facts about the region a pointer points into (copied out so callers hold
/// no borrow on the path state).
#[derive(Clone, Copy)]
struct RegionFacts {
    live: bool,
    size: ExprId,
    perms: Permissions,
    contract: Option<&'static str>,
}

fn region_facts(p: &SymPointer, state: &PathState) -> Option<RegionFacts> {
    let Prov::Region(r) = p.prov else {
        return None;
    };
    let reg = &state.regions[r];
    Some(RegionFacts {
        live: reg.state == LifetimeState::Live,
        size: reg.size,
        perms: reg.perms,
        contract: reg.contract,
    })
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.max(1)
}

fn map_binop(op: BinOp) -> BvOp {
    match op {
        BinOp::Add => BvOp::Add,
        BinOp::Sub => BvOp::Sub,
        BinOp::Mul => BvOp::Mul,
        BinOp::UDiv => BvOp::UDiv,
        BinOp::SDiv => BvOp::SDiv,
        BinOp::URem => BvOp::URem,
        BinOp::SRem => BvOp::SRem,
        BinOp::And => BvOp::And,
        BinOp::Or => BvOp::Or,
        BinOp::Xor => BvOp::Xor,
        BinOp::Shl => BvOp::Shl,
        BinOp::LShr => BvOp::LShr,
        BinOp::AShr => BvOp::AShr,
    }
}

fn map_cmpop(op: CmpOp) -> SCmp {
    match op {
        CmpOp::Eq => SCmp::Eq,
        CmpOp::Ne => SCmp::Ne,
        CmpOp::Ult => SCmp::Ult,
        CmpOp::Ule => SCmp::Ule,
        CmpOp::Ugt => SCmp::Ugt,
        CmpOp::Uge => SCmp::Uge,
        CmpOp::Slt => SCmp::Slt,
        CmpOp::Sle => SCmp::Sle,
        CmpOp::Sgt => SCmp::Sgt,
        CmpOp::Sge => SCmp::Sge,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::{BasicBlock, FuncId};

    /// `guarded(i, len)`: scalar SafetyCheck `i < len` under guard `i < len`.
    fn guarded() -> Function {
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
            value: RValue::Cmp {
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
            note: "guard".into(),
        });
        let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
        Function {
            id: FuncId(0),
            name: "guarded".into(),
            params: vec![(i, Type::int(64)), (len, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2],
            entry: BlockId(0),
        }
    }

    #[test]
    fn scalar_guarded_check_still_proven() {
        let r = discharge_function(&guarded());
        assert_eq!(r.outcome(BlockId(1), 0), Some(SymOutcome::Proven));
    }

    /// `masked(x)`: `j = x | 8; check j < 8` — always false (definite violation).
    fn masked_check() -> Function {
        let x = RegId(0);
        let j = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Assign {
            dst: j,
            ty: Type::int(64),
            value: RValue::Bin { op: BinOp::Or, lhs: Operand::Reg(x), rhs: Operand::int(64, 8) },
        });
        bb0.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(j), rhs: Operand::int(64, 8) },
            note: "x|8 < 8".into(),
        });
        Function {
            id: FuncId(0),
            name: "masked".into(),
            params: vec![(x, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn definite_violation_is_refuted_with_model() {
        let r = discharge_function(&masked_check());
        match r.outcome(BlockId(0), 1) {
            Some(SymOutcome::Refuted(model)) => {
                assert!(model.get("arg0").is_some(), "witness names the input: {model:?}");
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// `uninit()`: `buf = alloc i32*4; v = load buf` — read before any write.
    fn uninit() -> Function {
        let buf = RegId(0);
        let v = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::int(64, 4),
            align: 4,
        });
        bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(buf), align: 4 });
        Function {
            id: FuncId(0),
            name: "uninit".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn uninitialized_read_is_refuted() {
        // The load (block 0, idx 1) reads a freshly-allocated, never-written
        // region: a definite read of uninitialized memory, refuted as ValidRead.
        let r = discharge_function(&uninit());
        let d = r
            .mem_decision(BlockId(0), 1, SafetyProperty::ValidRead)
            .expect("ValidRead obligation for the load");
        assert!(!d.proven, "an uninitialized read must not be proven");
        assert!(d.refutation.is_some(), "it is refuted with a witness: {d:?}");
    }

    /// `init()`: `buf = alloc i32*4; store 7 -> buf; v = load buf` — read after
    /// write, so the load reads an initialized value.
    fn init() -> Function {
        let buf = RegId(0);
        let v = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::int(64, 4),
            align: 4,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(buf),
            value: Operand::int(32, 7),
            align: 4,
        });
        bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(buf), align: 4 });
        Function {
            id: FuncId(0),
            name: "init".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn initialized_read_is_not_flagged() {
        // The store `Must`-aliases the load, so the value is determined and the
        // definedness check does not fire (no refutation).
        let r = discharge_function(&init());
        let d = r
            .mem_decision(BlockId(0), 2, SafetyProperty::ValidRead)
            .expect("ValidRead obligation for the load");
        assert!(d.proven, "a read after write is proven: {d:?}");
        assert!(d.refutation.is_none(), "no refutation for an initialized read: {d:?}");
    }

    /// `bare(x)`: `check x < 8` — satisfiable but not valid, so NOT refuted.
    fn bare_check() -> Function {
        let x = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(x), rhs: Operand::int(64, 8) },
            note: "x < 8".into(),
        });
        Function {
            id: FuncId(0),
            name: "bare".into(),
            params: vec![(x, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn satisfiable_but_invalid_check_stays_unknown() {
        // `x < 8` holds for some inputs and fails for others — never refuted.
        let r = discharge_function(&bare_check());
        assert_eq!(r.outcome(BlockId(0), 0), Some(SymOutcome::Unknown));
    }

    /// `unguarded(i)`: `buf = alloc i32*8; store 0 -> buf+i` — OOB for i >= 8.
    fn unguarded_store() -> Function {
        let i = RegId(0);
        let buf = RegId(1);
        let p = RegId(2);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::int(64, 8),
            align: 4,
        });
        bb0.insts.push(Inst::PtrOffset {
            dst: p,
            base: Operand::Reg(buf),
            index: Operand::Reg(i),
            elem: Type::int(32),
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(p),
            value: Operand::int(32, 0),
            align: 4,
        });
        Function {
            id: FuncId(0),
            name: "unguarded".into(),
            params: vec![(i, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn concrete_size_oob_memory_access_is_refuted() {
        let r = discharge_function(&unguarded_store());
        let d = r
            .mem_decision(BlockId(0), 2, SafetyProperty::InBounds)
            .expect("in-bounds obligation exists");
        assert!(!d.proven, "an unguarded OOB write is not provable");
        let model = d.refutation.as_ref().expect("refuted with a counterexample");
        assert!(model.get("arg0").is_some(), "witness names the index: {model:?}");
    }

    /// `store_buf(i, n)`: alloc n i32; if 0<=i { if i<n { store buf[i] } }.
    fn store_buf() -> Function {
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
            value: RValue::Cmp {
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
            value: RValue::Cmp {
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
            align: 4,
        });

        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

        Function {
            id: FuncId(0),
            name: "store_buf".into(),
            params: vec![(i, Type::int(64)), (n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    #[test]
    fn guarded_store_proves_all_memory_checks() {
        let f = store_buf();
        let r = discharge_function(&f);
        assert!(!r.truncated);
        // The store is at bb2 index 1; all five obligations must be proven.
        for prop in [
            SafetyProperty::NoNullDeref,
            SafetyProperty::NoUseAfterFree,
            SafetyProperty::InBounds,
            SafetyProperty::Alignment,
            SafetyProperty::ValidWrite,
        ] {
            let d = r.mem_decision(BlockId(2), 1, prop).expect("decided");
            assert!(d.proven, "{prop} should be proven, got residual: {}", d.residual);
        }
        // PtrOffset at bb2 index 0: valid pointer arithmetic.
        let arith = r
            .mem_decision(BlockId(2), 0, SafetyProperty::ValidPointerArith)
            .expect("decided");
        assert!(arith.proven, "pointer arithmetic: {}", arith.residual);
    }

    /// A use-after-free: alloc, free, then store through the freed pointer.
    fn use_after_free() -> Function {
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Dealloc {
            region: RegionKind::Heap,
            ptr: Operand::Reg(buf),
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(buf),
            value: Operand::int(8, 0),
            align: 1,
        });
        Function {
            id: FuncId(0),
            name: "uaf".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn use_after_free_is_not_proven() {
        let f = use_after_free();
        let r = discharge_function(&f);
        // The free itself (index 1) is proven (base of a live region).
        let free = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("free");
        assert!(free.proven);
        // The store after free (index 2) must NOT prove temporal safety.
        let uaf = r
            .mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree)
            .expect("uaf");
        assert!(!uaf.proven, "use-after-free must stay unproven");
        // On this exact path the region is definitely freed, so the UAF is
        // refuted with a (here input-free) witness.
        assert!(uaf.refutation.is_some(), "definite use-after-free is refuted");
    }

    /// `double_free()`: `buf = alloc; free buf; free buf` — the second free is a
    /// definite double free.
    fn double_free() -> Function {
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
        bb0.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
        Function {
            id: FuncId(0),
            name: "double_free".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    /// `branch_fixture(K)`: `if i < K { if i >= 1 { check } }`. The inner branch
    /// `i >= 1` is unreachable exactly when `K == 1` (`i < 1 ∧ i >= 1`).
    fn branch_fixture(c_bound: u128, name: &'static str) -> Function {
        let i = RegId(0);
        let c = RegId(1);
        let d = RegId(2);
        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb0.insts.push(Inst::Assign {
            dst: c,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(i), rhs: Operand::int(64, c_bound) },
        });
        let mut bb1 = BasicBlock::new(
            BlockId(1),
            Terminator::CondBr {
                cond: Operand::Reg(d),
                then_blk: BlockId(2),
                then_args: vec![],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb1.insts.push(Inst::Assign {
            dst: d,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Uge, lhs: Operand::Reg(i), rhs: Operand::int(64, 1) },
        });
        let mut bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
        bb2.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(i), rhs: Operand::int(64, 8) },
            note: "inner check".into(),
        });
        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
        Function {
            id: FuncId(0),
            name: name.into(),
            params: vec![(i, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    #[test]
    fn infeasible_branch_is_pruned() {
        // `if i < 1 { if i >= 1 { check } }` — the inner block is unreachable, so
        // its check is never explored (absent from the report).
        let r = discharge_function(&branch_fixture(1, "dead"));
        assert!(r.outcome(BlockId(2), 0).is_none(), "the dead inner check is pruned");
    }

    #[test]
    fn feasible_branch_is_explored() {
        // `if i < 8 { if i >= 1 { check } }` — the inner block is reachable
        // (e.g. i = 5), so its check IS explored.
        let r = discharge_function(&branch_fixture(8, "live"));
        assert!(r.outcome(BlockId(2), 0).is_some(), "the reachable inner check is explored");
    }

    /// `diamond_phi(sel)`: `p = if sel < 1 { 3 } else { 5 }; check p < 8`. The
    /// join block has a PHI (`p`) merged via `ITE`; the check holds on the merged
    /// value (both arms are < 8).
    fn diamond_phi() -> Function {
        let sel = RegId(0);
        let c = RegId(1);
        let p = RegId(2);
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
            value: RValue::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(sel), rhs: Operand::int(64, 1) },
        });
        let bb1 = BasicBlock::new(BlockId(1), Terminator::Br { target: BlockId(3), args: vec![Operand::int(64, 3)] });
        let bb2 = BasicBlock::new(BlockId(2), Terminator::Br { target: BlockId(3), args: vec![Operand::int(64, 5)] });
        let mut bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
        bb3.params = vec![(p, Type::int(64))];
        bb3.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(p), rhs: Operand::int(64, 8) },
            note: "merged p < 8".into(),
        });
        Function {
            id: FuncId(0),
            name: "diamond_phi".into(),
            params: vec![(sel, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    #[test]
    fn merged_phi_value_is_proven_at_the_join() {
        // The join is analysed once with `p = ite(sel<1, 3, 5)`, and the check
        // `p < 8` is proved bit-precisely on the merged value.
        let r = discharge_function(&diamond_phi());
        assert_eq!(r.outcome(BlockId(3), 0), Some(SymOutcome::Proven));
    }

    /// `n` independent diamonds in sequence — `2^n` distinct paths, but only
    /// `4n + 1` blocks. Each diamond `i` branches on bit `i` of `sel`.
    fn wide_diamonds(n: usize) -> Function {
        let sel = RegId(0);
        let final_id = BlockId((4 * n) as u32);
        let mut blocks = Vec::new();
        for i in 0..n {
            let h = BlockId((4 * i) as u32);
            let t = BlockId((4 * i + 1) as u32);
            let e = BlockId((4 * i + 2) as u32);
            let m = BlockId((4 * i + 3) as u32);
            let next = if i + 1 < n { BlockId((4 * (i + 1)) as u32) } else { final_id };
            let tmask = RegId((1 + 2 * i) as u32);
            let creg = RegId((2 + 2 * i) as u32);
            let mut hb = BasicBlock::new(
                h,
                Terminator::CondBr { cond: Operand::Reg(creg), then_blk: t, then_args: vec![], else_blk: e, else_args: vec![] },
            );
            hb.insts.push(Inst::Assign {
                dst: tmask,
                ty: Type::int(64),
                value: RValue::Bin { op: BinOp::And, lhs: Operand::Reg(sel), rhs: Operand::int(64, 1u128 << i) },
            });
            hb.insts.push(Inst::Assign {
                dst: creg,
                ty: Type::Bool,
                value: RValue::Cmp { op: CmpOp::Ne, lhs: Operand::Reg(tmask), rhs: Operand::int(64, 0) },
            });
            blocks.push(hb);
            blocks.push(BasicBlock::new(t, Terminator::Br { target: m, args: vec![] }));
            blocks.push(BasicBlock::new(e, Terminator::Br { target: m, args: vec![] }));
            blocks.push(BasicBlock::new(m, Terminator::Br { target: next, args: vec![] }));
        }
        let mut fb = BasicBlock::new(final_id, Terminator::Return(None));
        fb.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::int(64, 3), rhs: Operand::int(64, 8) },
            note: "final".into(),
        });
        blocks.push(fb);
        Function {
            id: FuncId(0),
            name: "wide".into(),
            params: vec![(sel, Type::int(64))],
            ret_ty: Type::Unit,
            blocks,
            entry: BlockId(0),
        }
    }

    #[test]
    fn wide_cfg_is_processed_once_per_block_not_per_path() {
        // 8 independent diamonds = 256 distinct paths, but only 33 blocks. With a
        // budget far below the path count, merging still verifies — each block is
        // processed once (the old per-path walk would truncate).
        let f = wide_diamonds(8);
        let r = discharge_with(&f, crate::ExecLimits { max_visits: 40 });
        assert!(!r.truncated, "merging keeps visits linear in blocks, not exponential in paths");
        assert_eq!(r.outcome(BlockId(32), 0), Some(SymOutcome::Proven), "final check verified");
    }

    #[test]
    fn double_free_is_refuted() {
        let r = discharge_function(&double_free());
        // First free (index 1) is proven safe.
        let first = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("first free");
        assert!(first.proven);
        // Second free (index 2) is a definite double free — refuted.
        let second = r.mem_decision(BlockId(0), 2, SafetyProperty::NoDoubleFree).expect("second free");
        assert!(!second.proven);
        assert!(second.refutation.is_some(), "double free is refuted with a witness");
    }

    /// A counting loop writing across an allocation:
    ///   bb0: buf = alloc i32*n ; br bb1(0)
    ///   bb1(i): c = i < n ; condbr c -> bb2(i) / bb3
    ///   bb2(j): p = buf + j*4 ; store 0 -> p ; nj = j+1 ; br bb1(nj)
    ///   bb3: return
    fn loop_store() -> Function {
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
            value: RValue::Cmp {
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
            align: 4,
        });
        bb2.insts.push(Inst::Assign {
            dst: nj,
            ty: Type::int(64),
            value: RValue::Bin {
                op: BinOp::Add,
                lhs: Operand::Reg(j),
                rhs: Operand::int(64, 1),
            },
        });

        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

        Function {
            id: FuncId(0),
            name: "loop_store".into(),
            params: vec![(n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    /// Store a pointer into a slot, load it back, dereference it. Without a
    /// heap model the loaded pointer is opaque (deref → Unknown); with the
    /// alias-aware heap, provenance survives the round-trip and the deref proves.
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
            align: 8,
        });
        bb0.insts.push(Inst::Load {
            dst: p,
            ty: Type::ptr(Type::int(8)),
            ptr: Operand::Reg(slot),
            align: 8,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(p),
            value: Operand::int(8, 0),
            align: 1,
        });
        Function {
            id: FuncId(0),
            name: "indirect_store".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn pointer_survives_store_load_roundtrip() {
        let f = indirect_store();
        let r = discharge_function(&f);
        // The final deref (store at index 4): provenance survived the load, so
        // non-null and in-bounds are proven (they would be Unknown if the load
        // had returned an opaque value).
        for prop in [
            SafetyProperty::NoNullDeref,
            SafetyProperty::NoUseAfterFree,
            SafetyProperty::InBounds,
            SafetyProperty::ValidWrite,
        ] {
            let d = r.mem_decision(BlockId(0), 4, prop).expect("decided");
            assert!(d.proven, "{prop} should be proven via heap/alias: {}", d.residual);
        }
    }

    /// Regression (soundness): a `free` inside a loop body must NOT let an
    /// access or the free itself be proved — later iterations are UAF/double-free.
    #[test]
    fn free_inside_loop_is_not_proven() {
        let n = RegId(0);
        let buf = RegId(1);
        let i = RegId(2);
        let c = RegId(3);
        let j = RegId(4);
        let nj = RegId(5);

        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::Br { target: BlockId(1), args: vec![Operand::int(64, 0)] },
        );
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
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
            value: RValue::Cmp { op: CmpOp::Slt, lhs: Operand::Reg(i), rhs: Operand::Reg(n) },
        });
        let mut bb2 = BasicBlock::new(
            BlockId(2),
            Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(nj)] },
        );
        bb2.params = vec![(j, Type::int(64))];
        bb2.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(buf),
            value: Operand::int(8, 0),
            align: 1,
        });
        bb2.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
        bb2.insts.push(Inst::Assign {
            dst: nj,
            ty: Type::int(64),
            value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(j), rhs: Operand::int(64, 1) },
        });
        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
        let f = Function {
            id: FuncId(0),
            name: "loop_free".into(),
            params: vec![(n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        };
        let r = discharge_function(&f);
        let uaf = r.mem_decision(BlockId(2), 0, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(!uaf.proven, "store in a freeing loop must not prove temporal safety");
        let df = r.mem_decision(BlockId(2), 1, SafetyProperty::NoDoubleFree).expect("df");
        assert!(!df.proven, "free in a loop must not prove no-double-free");
    }

    /// Regression (soundness): a call to a freeing function must invalidate
    /// region liveness, so a use after it is not proved.
    #[test]
    fn use_after_freeing_call_is_not_proven() {
        use std::collections::HashMap;
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Call {
            dst: None,
            callee: csolver_ir::Callee::Direct(FuncId(9)),
            args: vec![Operand::Reg(buf)],
            ret_ty: Type::Unit,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(buf),
            value: Operand::int(8, 0),
            align: 1,
        });
        let f = Function {
            id: FuncId(0),
            name: "caller".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let mut summaries = HashMap::new();
        summaries.insert(
            FuncId(9),
            crate::summary::Summary {
                ret: crate::summary::RetSummary::Unknown,
                writes: false,
                frees: true,
            },
        );
        let r = discharge_with_summaries(&f, &summaries);
        let uaf = r.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(!uaf.proven, "use after a freeing call must not prove temporal safety");
    }

    #[test]
    fn loop_body_access_is_proven_via_invariant() {
        let f = loop_store();
        let r = discharge_function(&f);
        assert!(!r.truncated, "loop exploration must terminate");
        // The store at bb2 index 1: in-bounds proved from the interval
        // invariant (i >= 0) plus the loop guard (i < n).
        let inb = r
            .mem_decision(BlockId(2), 1, SafetyProperty::InBounds)
            .expect("in-bounds decided");
        assert!(inb.proven, "loop body access should be in bounds: {}", inb.residual);
        // Pointer arithmetic too.
        let arith = r
            .mem_decision(BlockId(2), 0, SafetyProperty::ValidPointerArith)
            .expect("ptr arith decided");
        assert!(arith.proven, "pointer arithmetic: {}", arith.residual);
    }
}
