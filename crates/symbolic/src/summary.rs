//! Function summaries for interprocedural analysis.
//!
//! A [`Summary`] captures the two things a caller needs to reason about a call
//! without re-analyzing the callee from scratch:
//!
//! * **Effects** — does the callee write to, or free, caller-visible memory?
//!   Computed conservatively and propagated to a fixpoint over the call graph
//!   (so recursion and transitive impurity are handled). A call to a *pure*
//!   function need not invalidate the caller's symbolic heap.
//! * **Return value** — when the result is a parameter pointer offset by an
//!   affine function of the parameters (the ubiquitous wrapper / accessor
//!   shape), the summary records that so the caller can rebuild the result
//!   pointer *with its original provenance*. This is what makes pointer-
//!   returning helpers transparent to the memory-safety proof.
//!
//! Everything here is parameter-relative data (no expressions / no solver); the
//! caller instantiates a summary against its actual arguments.

use csolver_ir::{
    BinOp, BlockId, Callee, Const, DataLayout, FuncId, Function, Inst, Module, Operand, RValue,
    RegId,
};
use std::collections::{BTreeMap, HashMap};

const LAYOUT: DataLayout = DataLayout::LP64;

/// An affine form `constant + Σ coeff_k · param_k` over a function's parameters
/// (identified by their positional index).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Affine {
    /// The constant term.
    pub constant: i128,
    /// `param index -> coefficient` (zero coefficients omitted).
    pub terms: BTreeMap<usize, i128>,
}

impl Affine {
    /// The constant affine form.
    pub fn constant(c: i128) -> Affine {
        Affine {
            constant: c,
            terms: BTreeMap::new(),
        }
    }

    /// The bare parameter `param_k`.
    pub fn param(k: usize) -> Affine {
        let mut terms = BTreeMap::new();
        terms.insert(k, 1);
        Affine {
            constant: 0,
            terms,
        }
    }

    fn normalized(mut self) -> Affine {
        self.terms.retain(|_, c| *c != 0);
        self
    }

    fn add(&self, o: &Affine) -> Option<Affine> {
        let mut out = self.clone();
        out.constant = out.constant.checked_add(o.constant)?;
        for (&k, &c) in &o.terms {
            let e = out.terms.entry(k).or_insert(0);
            *e = e.checked_add(c)?;
        }
        Some(out.normalized())
    }

    fn sub(&self, o: &Affine) -> Option<Affine> {
        self.add(&o.scale(-1)?)
    }

    fn scale(&self, k: i128) -> Option<Affine> {
        let mut out = Affine::constant(self.constant.checked_mul(k)?);
        for (&p, &c) in &self.terms {
            out.terms.insert(p, c.checked_mul(k)?);
        }
        Some(out.normalized())
    }

    fn as_const(&self) -> Option<i128> {
        self.terms.is_empty().then_some(self.constant)
    }
}

/// What a function returns, in parameter-relative terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RetSummary {
    /// Not characterized (the caller must havoc the result).
    Unknown,
    /// A scalar that is an affine function of the parameters.
    Scalar(Affine),
    /// A pointer derived from parameter `arg`, offset by an affine function of
    /// the parameters (provenance is that of `arg`).
    PtrFromArg {
        /// Index of the source pointer parameter.
        arg: usize,
        /// Byte offset added to that parameter's pointer.
        offset: Affine,
    },
}

/// A function's **provenance-transfer** summary: how a call moves provenance labels
/// between its pointer arguments. Derived from the body (the lowered `ProvLabel`/
/// `ProvPropagate` a contract emits, plus callees' own transfers) to a fixpoint — so an
/// *internal wrapper* around a provenance primitive propagates provenance without a
/// hand-written contract (the general-inference goal). Only **definite** parameter
/// aliasing is recorded, so a transfer is never spurious (a false FAIL); a missed one is a
/// sound under-approximation (a false negative).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProvTransfer {
    /// `(dst_arg, src_arg)`: a call unions `src_arg`'s labels into `dst_arg`'s.
    pub transfers: Vec<(usize, usize)>,
    /// `(arg, label)`: a call adds provenance label `label` to `arg`'s region.
    pub labels: Vec<(usize, u32)>,
}

/// A function's interprocedural summary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Summary {
    /// The return-value characterization.
    pub ret: RetSummary,
    /// Whether the function may write to memory.
    pub writes: bool,
    /// Whether the function may free memory.
    pub frees: bool,
    /// The parameter index this function **definitely frees** (`kfree`-style wrapper),
    /// when that can be established with certainty — used to detect a double-free
    /// through *two* freeing-wrapper calls on the same pointer (which the coarse
    /// `frees` havoc alone cannot attribute). `None` when no single parameter is
    /// provably freed on every path. A `Some(k)` only ever *adds* a definite
    /// double-free check; it never affects liveness (so never a false PASS).
    pub frees_arg: Option<usize>,
    /// How a call moves provenance labels between its pointer arguments.
    pub prov: ProvTransfer,
}

impl Summary {
    /// Whether the function is free of caller-visible memory effects.
    pub fn is_pure(&self) -> bool {
        !self.writes && !self.frees
    }
}

/// Abstract value tracked while summarizing a function body.
#[derive(Clone, PartialEq, Eq)]
enum AbsVal {
    PtrArg { arg: usize, off: Affine },
    Scalar(Affine),
    Opaque,
}

impl AbsVal {
    /// The join of two abstract values: equal values pass through, any
    /// disagreement is `Opaque`. This is what makes the return summary a *must*
    /// analysis — a summary is only produced when every path computes the same
    /// parameter-relative value, since a caller will trust it to rebuild the
    /// result exactly (a mere "may" summary would be unsound there).
    fn join(&self, other: &AbsVal) -> AbsVal {
        if self == other {
            self.clone()
        } else {
            AbsVal::Opaque
        }
    }
}

/// Summarize every function in a module (with the call-graph effect fixpoint).
pub fn summarize_module(module: &Module) -> HashMap<FuncId, Summary> {
    let mut map: HashMap<FuncId, Summary> = HashMap::new();
    for f in &module.functions {
        map.insert(f.id, summarize_fn(f));
    }

    // A call in a block that ends `Unreachable` is *diverging* (rustc's panic
    // shape: `call @panic…; unreachable`): control never returns past it, so no
    // caller-side code can observe its effects — the block's own path dies at
    // the terminator, and an unwinding path re-enters only through an `invoke`
    // cleanup edge, whose block does *not* end `Unreachable` and therefore still
    // contaminates. Exempting these calls keeps one panic check from poisoning
    // the effect summary of everything above it.
    let observable = |b: &csolver_ir::BasicBlock| {
        !matches!(b.term, csolver_ir::Terminator::Unreachable)
    };

    // Any non-direct call (external symbol / indirect) may do anything — EXCEPT
    // register-only inline asm (`<inline asm nomem>`), which writes/frees no tracked
    // memory (decided from its constraint string), so it must not poison the summary.
    let opaque = |callee: &Callee| {
        !matches!(callee, Callee::Direct(_))
            && !matches!(callee, Callee::Symbol(n) if n == "<inline asm nomem>")
    };
    for f in &module.functions {
        let opaque_call = f.blocks.iter().filter(|b| observable(b)).flat_map(|b| &b.insts).any(
            |i| matches!(i, Inst::Call { callee, .. } if opaque(callee)),
        );
        if opaque_call {
            if let Some(s) = map.get_mut(&f.id) {
                s.writes = true;
                s.frees = true;
            }
        }
    }

    // Propagate effects through direct calls to a fixpoint.
    loop {
        let mut changed = false;
        for f in &module.functions {
            let mut writes = map.get(&f.id).is_some_and(|s| s.writes);
            let mut frees = map.get(&f.id).is_some_and(|s| s.frees);
            for inst in f.blocks.iter().filter(|b| observable(b)).flat_map(|b| &b.insts) {
                if let Inst::Call { callee: Callee::Direct(g), .. } = inst {
                    if let Some(sg) = map.get(g) {
                        writes |= sg.writes;
                        frees |= sg.frees;
                    }
                }
            }
            if let Some(s) = map.get_mut(&f.id) {
                if writes != s.writes || frees != s.frees {
                    s.writes = writes;
                    s.frees = frees;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Propagate provenance transfers through direct calls to a fixpoint: if `f` calls `g`
    // and `g` transfers/labels one of its parameters, `f` does so on whichever of *its*
    // parameters the corresponding argument aliases. Only definite parameter aliasing
    // (`ptr_param_of`) is used, so a composed transfer is never spurious.
    let param_of: HashMap<FuncId, HashMap<RegId, usize>> =
        module.functions.iter().map(|f| (f.id, ptr_param_of(f))).collect();
    loop {
        let mut changed = false;
        for f in &module.functions {
            let pof = &param_of[&f.id];
            let arg = |op: &Operand| match op {
                Operand::Reg(r) => pof.get(r).copied(),
                _ => None,
            };
            let mut add: ProvTransfer = ProvTransfer::default();
            for inst in f.blocks.iter().filter(|b| observable(b)).flat_map(|b| &b.insts) {
                let Inst::Call { callee: Callee::Direct(g), args, .. } = inst else { continue };
                let Some(sg) = map.get(g) else { continue };
                for &(d, s) in &sg.prov.transfers {
                    if let (Some(pd), Some(ps)) = (args.get(d).and_then(&arg), args.get(s).and_then(&arg)) {
                        add.transfers.push((pd, ps));
                    }
                }
                for &(a, label) in &sg.prov.labels {
                    if let Some(pa) = args.get(a).and_then(&arg) {
                        add.labels.push((pa, label));
                    }
                }
            }
            if let Some(s) = map.get_mut(&f.id) {
                let before = (s.prov.transfers.len(), s.prov.labels.len());
                s.prov.transfers.extend(add.transfers);
                s.prov.labels.extend(add.labels);
                dedup(&mut s.prov);
                if (s.prov.transfers.len(), s.prov.labels.len()) != before {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    map
}

/// Whole-program summaries **without linking**: the same result as
/// `summarize_module(&merge_modules(mods, …))`, computed directly over the
/// separate modules. Call edges are resolved by name across modules exactly as
/// [`csolver_ir::merge_modules`] does (external definition wins; a `Symbol` call
/// to a defined external name becomes a direct edge, an unresolved one stays
/// opaque; `internal`/static names never resolve cross-module), and the same
/// write/free and provenance fixpoints run over that resolved global call graph.
///
/// Functions are keyed by the identical `FuncId`s `merge_modules` assigns
/// (sequential in module-then-function order), so the map equals the linked one
/// key-for-key. This is the analysis core of whole-program scanning that never
/// holds a linked module resident: only per-function *facts* (a base summary,
/// resolved edges, parameter map) are needed past the initial body scan, so the
/// bodies can be dropped/streamed. Splitting extraction from the fixpoint is what
/// makes it memory-bounded; this function keeps the modules in memory (the
/// equivalence oracle), a later streaming variant will drop them.
pub fn summarize_program(mods: &[&Module]) -> HashMap<FuncId, Summary> {
    // Merge-compatible id assignment + external name → id, shared with the linker
    // so the ids and cross-module resolution match `merge_modules` exactly.
    let (name_to_id, remaps) = csolver_ir::merge_id_plan(mods);

    // --- Per-function facts (this is the streamable body scan). ---
    let observable =
        |b: &csolver_ir::BasicBlock| !matches!(b.term, csolver_ir::Terminator::Unreachable);
    let mut map: HashMap<FuncId, Summary> = HashMap::new();
    let mut edges: HashMap<FuncId, Vec<FuncId>> = HashMap::new();
    let mut has_opaque: HashMap<FuncId, bool> = HashMap::new();
    let mut param_of: HashMap<FuncId, HashMap<RegId, usize>> = HashMap::new();
    let mut prov_calls: HashMap<FuncId, Vec<(FuncId, Vec<Operand>)>> = HashMap::new();
    for (mi, m) in mods.iter().enumerate() {
        let remap = &remaps[mi];
        for f in &m.functions {
            let gid = remap[&f.id];
            map.insert(gid, summarize_fn(f));
            param_of.insert(gid, ptr_param_of(f));
            let (mut fedges, mut opaque, mut pcalls) = (Vec::new(), false, Vec::new());
            for b in f.blocks.iter().filter(|b| observable(b)) {
                for inst in &b.insts {
                    let Inst::Call { callee, args, .. } = inst else { continue };
                    // Resolve to a global id and decide opacity exactly as the LINKED
                    // module would (see `merge_modules` + `summarize_module`'s `opaque`).
                    let (resolved, is_opaque): (Option<FuncId>, bool) = match callee {
                        Callee::Direct(old) => (remap.get(old).copied(), false),
                        Callee::Symbol(nm) if nm == "<inline asm nomem>" => (None, false),
                        Callee::Symbol(nm) => {
                            let id = name_to_id.get(nm).copied();
                            (id, id.is_none())
                        }
                        Callee::Indirect(_) => (None, true),
                    };
                    opaque |= is_opaque;
                    if let Some(g) = resolved {
                        fedges.push(g);
                        pcalls.push((g, args.clone()));
                    }
                }
            }
            edges.insert(gid, fedges);
            has_opaque.insert(gid, opaque);
            prov_calls.insert(gid, pcalls);
        }
    }

    // --- The same three steps as `summarize_module`, now over facts only. ---
    for (gid, &op) in &has_opaque {
        if op {
            if let Some(s) = map.get_mut(gid) {
                s.writes = true;
                s.frees = true;
            }
        }
    }
    loop {
        let mut changed = false;
        for (gid, callees) in &edges {
            let (mut writes, mut frees) =
                map.get(gid).map_or((false, false), |s| (s.writes, s.frees));
            for g in callees {
                if let Some(sg) = map.get(g) {
                    writes |= sg.writes;
                    frees |= sg.frees;
                }
            }
            if let Some(s) = map.get_mut(gid) {
                if writes != s.writes || frees != s.frees {
                    s.writes = writes;
                    s.frees = frees;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    loop {
        let mut changed = false;
        for (gid, pcalls) in &prov_calls {
            let pof = &param_of[gid];
            let arg = |op: &Operand| match op {
                Operand::Reg(r) => pof.get(r).copied(),
                _ => None,
            };
            let mut add = ProvTransfer::default();
            for (g, args) in pcalls {
                let Some(sg) = map.get(g) else { continue };
                for &(d, s) in &sg.prov.transfers {
                    if let (Some(pd), Some(ps)) =
                        (args.get(d).and_then(&arg), args.get(s).and_then(&arg))
                    {
                        add.transfers.push((pd, ps));
                    }
                }
                for &(a, label) in &sg.prov.labels {
                    if let Some(pa) = args.get(a).and_then(&arg) {
                        add.labels.push((pa, label));
                    }
                }
            }
            if let Some(s) = map.get_mut(gid) {
                let before = (s.prov.transfers.len(), s.prov.labels.len());
                s.prov.transfers.extend(add.transfers);
                s.prov.labels.extend(add.labels);
                dedup(&mut s.prov);
                if (s.prov.transfers.len(), s.prov.labels.len()) != before {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    map
}

fn summarize_fn(f: &Function) -> Summary {
    // A write/free is *caller-visible* only through memory the caller can also
    // reach: anything but the function's own allocations. A store into a local
    // alloca (rustc's debug IR round-trips every value through one) cannot alias
    // any region the caller tracks — distinct allocations never alias — so it
    // must not force the caller to discard its heap knowledge.
    let local = local_alloc_regs(f);
    let is_local = |op: &Operand| matches!(op, Operand::Reg(r) if local.contains(r));
    let mut writes = false;
    let mut frees = false;
    for i in f.blocks.iter().flat_map(|b| &b.insts) {
        match i {
            Inst::Store { ptr, .. } => writes |= !is_local(ptr),
            // A bulk write is a write (previously missed: a callee memcpy-ing
            // into a parameter looked pure — stale caller heap, false-PASS
            // material). Inline asm is opaque: assume both effects.
            Inst::MemIntrinsic { dst, .. } => writes |= !is_local(dst),
            Inst::Asm { .. } => {
                writes = true;
                frees = true;
            }
            Inst::Dealloc { ptr, .. } => frees |= !is_local(ptr),
            _ => {}
        }
    }

    Summary { ret: ret_of_fn(f), writes, frees, frees_arg: derive_frees_arg(f), prov: prov_transfer_of_fn(f) }
}

/// The parameter a **single-block** function definitely frees: it has exactly one
/// `Dealloc` and that deallocates a bare parameter (a `kfree(p)`-style wrapper). A
/// single block means the free is unconditional (executes on every call), so a call
/// to it definitely frees that argument — the basis for detecting a double-free
/// through two such wrapper calls. Conservative: any other shape (multi-block,
/// several deallocs, inline asm, a non-parameter pointer) yields `None`, so this
/// never over-claims a free (which would risk a false double-free FAIL).
fn derive_frees_arg(f: &Function) -> Option<usize> {
    if f.blocks.len() != 1 {
        return None;
    }
    let params: HashMap<RegId, usize> =
        f.params.iter().enumerate().map(|(i, (r, _))| (*r, i)).collect();
    let mut deallocs = f.blocks[0].insts.iter().filter_map(|i| match i {
        Inst::Dealloc { ptr: Operand::Reg(r), .. } => Some(params.get(r).copied()),
        Inst::Dealloc { .. } | Inst::Asm { .. } => Some(None),
        _ => None,
    });
    match (deallocs.next(), deallocs.next()) {
        (Some(hit), None) => hit,
        _ => None,
    }
}

/// Which pointer parameter (by index) a register **definitely** aliases: the parameter
/// pointers themselves, closed under `PtrOffset` / `Assign(Use|Cast)` (an offset/copy of a
/// parameter pointer stays that parameter's provenance). A register not in the map (a
/// loaded value, a call result, a block parameter) is *not* claimed — sound: we only ever
/// record a provenance transfer between two definite parameter pointers.
fn ptr_param_of(f: &Function) -> HashMap<RegId, usize> {
    let mut map: HashMap<RegId, usize> = HashMap::new();
    for (k, (reg, ty)) in f.params.iter().enumerate() {
        if ty.is_ptr() {
            map.insert(*reg, k);
        }
    }
    loop {
        let mut changed = false;
        let mut relate = |dst: RegId, base: &Operand, map: &mut HashMap<RegId, usize>| {
            if let Operand::Reg(b) = base {
                if let Some(&arg) = map.get(b) {
                    changed |= map.insert(dst, arg).is_none();
                }
            }
        };
        for inst in f.blocks.iter().flat_map(|b| &b.insts) {
            match inst {
                Inst::PtrOffset { dst, base, .. } => relate(*dst, base, &mut map),
                Inst::Assign { dst, value: RValue::Use(op), .. }
                | Inst::Assign { dst, value: RValue::Cast { operand: op, .. }, .. } => {
                    relate(*dst, op, &mut map)
                }
                _ => {}
            }
        }
        if !changed {
            return map;
        }
    }
}

/// Derive a function's provenance-transfer summary from the `ProvLabel`/`ProvPropagate`
/// instructions its body contains (the ones a contract lowered for the recognized calls it
/// makes). Interprocedural composition through direct callees is added by the module
/// fixpoint in [`summarize_module`].
fn prov_transfer_of_fn(f: &Function) -> ProvTransfer {
    let param_of = ptr_param_of(f);
    let arg = |op: &Operand| match op {
        Operand::Reg(r) => param_of.get(r).copied(),
        _ => None,
    };
    let mut prov = ProvTransfer::default();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        match inst {
            Inst::ProvLabel { ptr, label } => {
                if let Some(a) = arg(ptr) {
                    prov.labels.push((a, *label));
                }
            }
            Inst::ProvPropagate { dst, src } => {
                if let (Some(d), Some(s)) = (arg(dst), arg(src)) {
                    prov.transfers.push((d, s));
                }
            }
            _ => {}
        }
    }
    dedup(&mut prov);
    prov
}

fn dedup(prov: &mut ProvTransfer) {
    prov.transfers.sort_unstable();
    prov.transfers.dedup();
    prov.labels.sort_unstable();
    prov.labels.dedup();
}

/// The registers that provably hold pointers into the function's *own*
/// allocations: `Alloc` results, closed under `PtrOffset` / `Assign(Use)` /
/// `Assign(Cast)` to a fixpoint. Conservative in the right direction — a
/// register not in the set (a parameter, a loaded value, a block parameter, a
/// call result) counts as caller-visible.
fn local_alloc_regs(f: &Function) -> std::collections::HashSet<RegId> {
    let mut set = std::collections::HashSet::new();
    loop {
        let mut changed = false;
        for inst in f.blocks.iter().flat_map(|b| &b.insts) {
            let derived = match inst {
                Inst::Alloc { dst, .. } => Some(*dst),
                Inst::PtrOffset { dst, base: Operand::Reg(b), .. } if set.contains(b) => {
                    Some(*dst)
                }
                Inst::Assign { dst, value, .. } => match value {
                    RValue::Use(Operand::Reg(r)) | RValue::Cast { operand: Operand::Reg(r), .. }
                        if set.contains(r) =>
                    {
                        Some(*dst)
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(d) = derived {
                changed |= set.insert(d);
            }
        }
        if !changed {
            return set;
        }
    }
}

/// Characterize the return value across the whole CFG. Instruction results are
/// pure functions of their inputs and are recomputed each pass; the only join
/// points are **block parameters**, whose value is the [`AbsVal::join`] over
/// every incoming branch argument seen so far. Joins are monotone toward
/// `Opaque` (lattice height 2), so the iteration terminates; a defensive pass
/// cap degrades to `Unknown` rather than looping.
///
/// This subsumes the previous single-block analysis and, crucially, covers
/// rustc's guard shape — `entry: cond ? panic-block : ok-block; ok: ret p+off` —
/// where the panic block never returns and thus never joins: the summary comes
/// from the agreeing return sites alone.
fn ret_of_fn(f: &Function) -> RetSummary {
    use csolver_ir::Terminator;

    let mut env: HashMap<RegId, AbsVal> = HashMap::new();
    for (k, (reg, ty)) in f.params.iter().enumerate() {
        let v = if ty.is_ptr() {
            AbsVal::PtrArg { arg: k, off: Affine::constant(0) }
        } else {
            AbsVal::Scalar(Affine::param(k))
        };
        env.insert(*reg, v);
    }

    // `param_join[reg]`: the running join of every branch argument bound to the
    // block parameter `reg`. Function parameters are pre-seeded with their call
    // value so that an edge that rebinds one (a back-edge into the entry block)
    // joins *against the seed* rather than replacing it — replacing would claim
    // the loop value holds on the first entry too.
    let mut param_join: HashMap<RegId, AbsVal> = env.clone();
    let by_id: HashMap<_, _> = f.blocks.iter().map(|b| (b.id, b)).collect();

    for _pass in 0..64 {
        let mut changed = false;
        for b in &f.blocks {
            // Bind this block's parameters from the joined incoming values.
            for (reg, _) in &b.params {
                if let Some(v) = param_join.get(reg) {
                    if env.get(reg) != Some(v) {
                        env.insert(*reg, v.clone());
                        changed = true;
                    }
                }
            }
            for inst in &b.insts {
                let (dst, v) = match inst {
                    Inst::Assign { dst, value, .. } => (*dst, eval_rvalue(value, &env)),
                    Inst::PtrOffset { dst, base, index, elem } => {
                        let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1) as i128;
                        let v = match (eval_operand(base, &env), eval_operand(index, &env)) {
                            (AbsVal::PtrArg { arg, off }, AbsVal::Scalar(ix)) => {
                                match ix.scale(stride).and_then(|t| off.add(&t)) {
                                    Some(o) => AbsVal::PtrArg { arg, off: o },
                                    None => AbsVal::Opaque,
                                }
                            }
                            _ => AbsVal::Opaque,
                        };
                        (*dst, v)
                    }
                    other => match other.defined_reg() {
                        Some(dst) => (dst, AbsVal::Opaque),
                        None => continue,
                    },
                };
                if env.get(&dst) != Some(&v) {
                    env.insert(dst, v);
                    changed = true;
                }
            }
            // Propagate branch arguments into the successors' parameter joins.
            let mut feed = |target: BlockId, args: &[Operand]| {
                let Some(tb) = by_id.get(&target) else { return };
                for ((reg, _), arg) in tb.params.iter().zip(args) {
                    let v = eval_operand(arg, &env);
                    let joined = match param_join.get(reg) {
                        Some(prev) => prev.join(&v),
                        None => v,
                    };
                    if param_join.get(reg) != Some(&joined) {
                        param_join.insert(*reg, joined);
                        changed = true;
                    }
                }
            };
            match &b.term {
                Terminator::Br { target, args } => feed(*target, args),
                Terminator::CondBr { then_blk, then_args, else_blk, else_args, .. } => {
                    feed(*then_blk, then_args);
                    feed(*else_blk, else_args);
                }
                // Switch targets carry no arguments; Return/Unreachable have no
                // successors.
                Terminator::Switch { .. } | Terminator::Return(_) | Terminator::Unreachable => {}
            }
        }
        if !changed {
            // Fixpoint reached: join the value of every returning site.
            let mut ret: Option<AbsVal> = None;
            for b in &f.blocks {
                if let Terminator::Return(Some(op)) = &b.term {
                    let v = eval_operand(op, &env);
                    ret = Some(match ret {
                        Some(prev) => prev.join(&v),
                        None => v,
                    });
                }
            }
            return match ret {
                Some(AbsVal::PtrArg { arg, off }) => RetSummary::PtrFromArg { arg, offset: off },
                Some(AbsVal::Scalar(a)) => RetSummary::Scalar(a),
                _ => RetSummary::Unknown,
            };
        }
    }
    // Pass cap hit (pathological CFG): degrade, never loop or guess.
    RetSummary::Unknown
}

fn eval_rvalue(rv: &RValue, env: &HashMap<RegId, AbsVal>) -> AbsVal {
    match rv {
        RValue::Use(op) => eval_operand(op, env),
        RValue::Bin { op, lhs, rhs } => {
            match (eval_operand(lhs, env), eval_operand(rhs, env)) {
                (AbsVal::Scalar(a), AbsVal::Scalar(b)) => {
                    let r = match op {
                        BinOp::Add => a.add(&b),
                        BinOp::Sub => a.sub(&b),
                        BinOp::Mul => match (a.as_const(), b.as_const()) {
                            (Some(c), _) => b.scale(c),
                            (_, Some(c)) => a.scale(c),
                            _ => None,
                        },
                        _ => None,
                    };
                    r.map(AbsVal::Scalar).unwrap_or(AbsVal::Opaque)
                }
                _ => AbsVal::Opaque,
            }
        }
        _ => AbsVal::Opaque,
    }
}

fn eval_operand(op: &Operand, env: &HashMap<RegId, AbsVal>) -> AbsVal {
    match op {
        Operand::Reg(r) => match env.get(r) {
            Some(v) => v.clone(),
            None => AbsVal::Opaque,
        },
        Operand::Const(Const::Int(bv)) => AbsVal::Scalar(Affine::constant(bv.unsigned() as i128)),
        _ => AbsVal::Opaque,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::{BasicBlock, BlockId, Terminator, Type};

    /// A callee that memcpys into a *parameter* writes caller-visible memory —
    /// before, only `Inst::Store` counted and such a callee looked pure, letting
    /// the caller keep stale heap knowledge across the call (false-PASS
    /// material). A callee that only writes its *own* alloca stays pure: rustc's
    /// debug IR round-trips every local through one, and treating that as a
    /// visible write would havoc the caller on every helper call.
    #[test]
    fn memcpy_to_a_parameter_is_a_visible_write_but_own_allocas_are_not() {
        let p = RegId(0);
        let buf = RegId(1);
        let make = |dst_reg: RegId| {
            let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
            bb0.insts.push(Inst::Alloc {
                dst: buf,
                region: csolver_core::RegionKind::Stack,
                elem: Type::int(32),
                count: Operand::int(64, 1),
                align: 4,
            });
            bb0.insts.push(Inst::MemIntrinsic {
                kind: csolver_ir::MemKind::Set,
                dst: Operand::Reg(dst_reg),
                src: None,
                len: Operand::int(64, 4),
            });
            Function {
                id: FuncId(0),
                name: "m".into(),
                params: vec![(p, Type::ptr(Type::int(32)))],
                ret_ty: Type::Unit,
                blocks: vec![bb0],
                entry: BlockId(0),
            }
        };
        assert!(summarize_fn(&make(p)).writes, "memset to a parameter is a visible write");
        assert!(!summarize_fn(&make(buf)).writes, "memset to an own alloca is not");
    }

    /// The load-bearing losslessness oracle for whole-program-without-linking:
    /// `summarize_program(&[&a, &b])` must equal `summarize_module(&merge(a, b))`
    /// key-for-key — proving that resolving call edges by name across separate
    /// modules and running the fixpoints on facts reproduces the linked result
    /// exactly (cross-module `Symbol` resolve, in-module `Direct` remap, and an
    /// unresolved external staying opaque).
    #[test]
    fn summarize_program_equals_summarize_of_the_linked_module() {
        use csolver_ir::merge_modules;
        let p = RegId(0);
        let one_block = |insts: Vec<Inst>| {
            let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
            bb.insts = insts;
            vec![bb]
        };
        let func = |id: u32, name: &str, params: Vec<(RegId, Type)>, insts: Vec<Inst>| Function {
            id: FuncId(id),
            name: name.into(),
            params,
            ret_ty: Type::Unit,
            blocks: one_block(insts),
            entry: BlockId(0),
        };
        let store_p = || Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(p),
            value: Operand::int(32, 0),
            align: 4,
        };
        let call = |callee: Callee, args: Vec<Operand>| Inst::Call {
            dst: None,
            callee,
            args,
            ret_ty: Type::Unit,
            ret_ref: None,
        };
        let pp = || vec![(p, Type::ptr(Type::int(32)))];

        // Module B: a real writer, and an in-module Direct wrapper around it.
        let mut b = Module::new("b");
        b.functions.push(func(0, "writer", pp(), vec![store_p()]));
        b.functions.push(func(
            1,
            "b_wrapper",
            pp(),
            vec![call(Callee::Direct(FuncId(0)), vec![Operand::Reg(p)])],
        ));
        // Module A: a cross-module Symbol wrapper (resolves to B::writer → writes),
        // and a call to an unresolved external (stays opaque → writes+frees).
        let mut a = Module::new("a");
        a.functions.push(func(
            0,
            "a_wrapper",
            pp(),
            vec![call(Callee::Symbol("writer".into()), vec![Operand::Reg(p)])],
        ));
        a.functions.push(func(
            1,
            "a_opaque",
            vec![],
            vec![call(Callee::Symbol("some_undefined_ext".into()), vec![])],
        ));

        let linked = merge_modules(vec![a.clone(), b.clone()], "linked");
        let want = summarize_module(&linked);
        let got = summarize_program(&[&a, &b]);
        assert_eq!(got, want, "link-free summaries must equal the linked summaries");

        // Spot-check the intended effects survived (guards against both being wrong).
        assert!(want[&FuncId(0)].writes, "a_wrapper inherits B::writer's write");
        assert!(want[&FuncId(1)].writes && want[&FuncId(1)].frees, "a_opaque is fully havoc'd");
        assert!(want[&FuncId(2)].writes, "writer writes");
        assert!(want[&FuncId(3)].writes, "b_wrapper inherits via Direct");
    }

    /// Randomised losslessness guard: over many random multi-module call graphs
    /// (stores, frees, and cross-module `Symbol` calls — some to defined names,
    /// some unresolved/opaque), the link-free summaries must always equal the
    /// linked ones. Exercises the transitive write/free fixpoint on arbitrary
    /// graphs, which hand-built cases cannot cover exhaustively.
    #[test]
    fn summarize_program_matches_linked_on_random_programs() {
        use csolver_ir::merge_modules;
        let p = RegId(0);
        let mut state: u64 = 0x00C0_FFEE_1234_5678;
        let mut rng = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let call = |callee: Callee| Inst::Call {
            dst: None,
            callee,
            args: vec![Operand::Reg(p)],
            ret_ty: Type::Unit,
            ret_ref: None,
        };
        for _ in 0..400 {
            let n_mods = 2 + (rng() % 3) as usize; // 2..=4 modules
            let per = 2 + (rng() % 4) as usize; // 2..=5 functions each
            let total = n_mods * per;
            let name = |gi: usize| format!("f{gi}");
            let mut modules = Vec::new();
            let mut gi = 0usize;
            for _ in 0..n_mods {
                let mut m = Module::new("m");
                for local in 0..per {
                    let mut insts = Vec::new();
                    if rng() & 1 == 0 {
                        insts.push(Inst::Store {
                            ty: Type::int(32),
                            ptr: Operand::Reg(p),
                            value: Operand::int(32, 0),
                            align: 4,
                        });
                    }
                    if rng() % 4 == 0 {
                        insts.push(Inst::Dealloc {
                            region: csolver_core::RegionKind::Heap,
                            ptr: Operand::Reg(p),
                        });
                    }
                    for _ in 0..(rng() % 3) {
                        let callee = if rng() % 5 == 0 {
                            Callee::Symbol("undefined_ext".into()) // opaque
                        } else {
                            Callee::Symbol(name((rng() as usize) % total))
                        };
                        insts.push(call(callee));
                    }
                    m.functions.push(Function {
                        id: FuncId(local as u32),
                        name: name(gi),
                        params: vec![(p, Type::ptr(Type::int(32)))],
                        ret_ty: Type::Unit,
                        blocks: {
                            let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
                            bb.insts = insts;
                            vec![bb]
                        },
                        entry: BlockId(0),
                    });
                    gi += 1;
                }
                modules.push(m);
            }
            let refs: Vec<&Module> = modules.iter().collect();
            let got = summarize_program(&refs);
            let want = summarize_module(&merge_modules(modules.clone(), "linked"));
            assert_eq!(got, want, "link-free != linked on a random program");
        }
    }

    /// A call in an `Unreachable`-terminated block (rustc's `call @panic…;
    /// unreachable` shape) never returns control, so its effects are
    /// unobservable by any caller — it must not contaminate the effect summary.
    /// The same call in a *returning* block must.
    #[test]
    fn diverging_calls_do_not_contaminate_the_effect_summary() {
        let make = |term: Terminator| {
            let mut bb0 = BasicBlock::new(BlockId(0), term);
            bb0.insts.push(Inst::Call {
                dst: None,
                callee: Callee::Symbol("core::panicking::panic".into()),
                args: vec![],
                ret_ty: Type::Unit,
                ret_ref: None,
            });
            let f = Function {
                id: FuncId(0),
                name: "p".into(),
                params: vec![],
                ret_ty: Type::Unit,
                blocks: vec![bb0],
                entry: BlockId(0),
            };
            let mut m = Module::new("m");
            m.functions.push(f);
            m
        };
        let diverging = summarize_module(&make(Terminator::Unreachable));
        assert!(diverging[&FuncId(0)].is_pure(), "a diverging call's effects are unobservable");
        let returning = summarize_module(&make(Terminator::Return(None)));
        assert!(!returning[&FuncId(0)].is_pure(), "a returning opaque call must contaminate");
    }

    #[test]
    fn pointer_wrapper_summary() {
        // fn first(b: *i32) -> *i32 { b + 0 }
        let b = RegId(0);
        let q = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(q))));
        bb0.insts.push(Inst::PtrOffset {
            dst: q,
            base: Operand::Reg(b),
            index: Operand::int(64, 0),
            elem: Type::int(32),
        });
        let f = Function {
            id: FuncId(0),
            name: "first".into(),
            params: vec![(b, Type::ptr(Type::int(32)))],
            ret_ty: Type::ptr(Type::int(32)),
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let s = summarize_fn(&f);
        assert!(s.is_pure());
        assert_eq!(
            s.ret,
            RetSummary::PtrFromArg { arg: 0, offset: Affine::constant(0) }
        );
    }

    /// rustc's guard shape: `entry: cond ? panic : ok; ok: ret p+4`. The panic
    /// block never returns, so the summary must come from the agreeing return
    /// site — multi-block functions were previously always `Unknown`.
    #[test]
    fn guarded_pointer_wrapper_summary() {
        let p = RegId(0);
        let c = RegId(1);
        let q = RegId(2);
        let mut entry = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(2),
                else_args: vec![],
            },
        );
        entry.insts.push(Inst::Call {
            dst: Some(c),
            callee: Callee::Symbol("check".into()),
            args: vec![],
            ret_ty: Type::Bool,
            ret_ref: None,
        });
        let panic_blk = BasicBlock::new(BlockId(1), Terminator::Unreachable);
        let mut ok = BasicBlock::new(BlockId(2), Terminator::Return(Some(Operand::Reg(q))));
        ok.insts.push(Inst::PtrOffset {
            dst: q,
            base: Operand::Reg(p),
            index: Operand::int(64, 1),
            elem: Type::int(32),
        });
        let f = Function {
            id: FuncId(0),
            name: "guarded".into(),
            params: vec![(p, Type::ptr(Type::int(32)))],
            ret_ty: Type::ptr(Type::int(32)),
            blocks: vec![entry, panic_blk, ok],
            entry: BlockId(0),
        };
        assert_eq!(
            summarize_fn(&f).ret,
            RetSummary::PtrFromArg { arg: 0, offset: Affine::constant(4) },
            "the non-returning panic block must not defeat the summary"
        );
    }

    /// Disagreeing return sites (`ret p` vs `ret p+4`) must yield `Unknown` —
    /// the caller trusts a summary to rebuild the result *exactly*, so a "may"
    /// summary would be unsound. Likewise a loop-varying pointer: the back-edge
    /// join makes the block parameter `Opaque`.
    #[test]
    fn disagreeing_and_loop_varying_returns_are_unknown() {
        let p = RegId(0);
        let c = RegId(1);
        let q = RegId(2);
        // fn f(p, c) { if c { return p } else { return p+4 } }
        let mut entry = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(2),
                else_args: vec![],
            },
        );
        entry.insts.push(Inst::PtrOffset {
            dst: q,
            base: Operand::Reg(p),
            index: Operand::int(64, 1),
            elem: Type::int(32),
        });
        let a = BasicBlock::new(BlockId(1), Terminator::Return(Some(Operand::Reg(p))));
        let b = BasicBlock::new(BlockId(2), Terminator::Return(Some(Operand::Reg(q))));
        let f = Function {
            id: FuncId(0),
            name: "diverging_returns".into(),
            params: vec![(p, Type::ptr(Type::int(32))), (c, Type::Bool)],
            ret_ty: Type::ptr(Type::int(32)),
            blocks: vec![entry, a, b],
            entry: BlockId(0),
        };
        assert_eq!(summarize_fn(&f).ret, RetSummary::Unknown);

        // fn g(p) { loop { p = p+4; if done { return p } } } — the block param
        // joins p (entry) with p+4k (back-edge) → Opaque → Unknown.
        let cur = RegId(3);
        let next = RegId(4);
        let done = RegId(5);
        let entry = BasicBlock::new(
            BlockId(0),
            Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(p)] },
        );
        let mut head = BasicBlock::new(
            BlockId(1),
            Terminator::CondBr {
                cond: Operand::Reg(done),
                then_blk: BlockId(2),
                then_args: vec![],
                else_blk: BlockId(1),
                else_args: vec![Operand::Reg(next)],
            },
        );
        head.params.push((cur, Type::ptr(Type::int(32))));
        head.insts.push(Inst::PtrOffset {
            dst: next,
            base: Operand::Reg(cur),
            index: Operand::int(64, 1),
            elem: Type::int(32),
        });
        head.insts.push(Inst::Call {
            dst: Some(done),
            callee: Callee::Symbol("check".into()),
            args: vec![],
            ret_ty: Type::Bool,
            ret_ref: None,
        });
        let exit = BasicBlock::new(BlockId(2), Terminator::Return(Some(Operand::Reg(next))));
        let g = Function {
            id: FuncId(1),
            name: "loop_advance".into(),
            params: vec![(p, Type::ptr(Type::int(32)))],
            ret_ty: Type::ptr(Type::int(32)),
            blocks: vec![entry, head, exit],
            entry: BlockId(0),
        };
        assert_eq!(summarize_fn(&g).ret, RetSummary::Unknown);
    }

    #[test]
    fn index_wrapper_summary() {
        // fn at(b: *i32, i: i64) -> *i32 { b + i }   => ret = arg0 + 4*param1
        let b = RegId(0);
        let i = RegId(1);
        let q = RegId(2);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(q))));
        bb0.insts.push(Inst::PtrOffset {
            dst: q,
            base: Operand::Reg(b),
            index: Operand::Reg(i),
            elem: Type::int(32),
        });
        let f = Function {
            id: FuncId(0),
            name: "at".into(),
            params: vec![(b, Type::ptr(Type::int(32))), (i, Type::int(64))],
            ret_ty: Type::ptr(Type::int(32)),
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let s = summarize_fn(&f);
        match s.ret {
            RetSummary::PtrFromArg { arg: 0, offset } => {
                assert_eq!(offset.constant, 0);
                assert_eq!(offset.terms.get(&1), Some(&4)); // i * sizeof(i32)
            }
            other => panic!("expected PtrFromArg, got {other:?}"),
        }
    }
}
