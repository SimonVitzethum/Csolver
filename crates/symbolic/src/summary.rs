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

use csolver_ir::{BinOp, Callee, Const, DataLayout, FuncId, Function, Inst, Module, Operand, RValue, RegId};
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

/// A function's interprocedural summary.
#[derive(Debug, Clone)]
pub struct Summary {
    /// The return-value characterization.
    pub ret: RetSummary,
    /// Whether the function may write to memory.
    pub writes: bool,
    /// Whether the function may free memory.
    pub frees: bool,
}

impl Summary {
    /// Whether the function is free of caller-visible memory effects.
    pub fn is_pure(&self) -> bool {
        !self.writes && !self.frees
    }
}

/// Abstract value tracked while summarizing a function body.
#[derive(Clone)]
enum AbsVal {
    PtrArg { arg: usize, off: Affine },
    Scalar(Affine),
    Opaque,
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

    // Any non-direct call (external symbol / indirect) may do anything.
    for f in &module.functions {
        let opaque_call = f.blocks.iter().filter(|b| observable(b)).flat_map(|b| &b.insts).any(
            |i| matches!(i, Inst::Call { callee, .. } if !matches!(callee, Callee::Direct(_))),
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

    // Return characterization only for single-block functions (the common
    // wrapper/accessor shape); anything more is conservatively Unknown.
    let ret = if f.blocks.len() == 1 {
        ret_of_block(f)
    } else {
        RetSummary::Unknown
    };

    Summary { ret, writes, frees }
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

fn ret_of_block(f: &Function) -> RetSummary {
    let block = &f.blocks[0];
    let mut env: HashMap<RegId, AbsVal> = HashMap::new();
    for (k, (reg, ty)) in f.params.iter().enumerate() {
        let v = if ty.is_ptr() {
            AbsVal::PtrArg { arg: k, off: Affine::constant(0) }
        } else {
            AbsVal::Scalar(Affine::param(k))
        };
        env.insert(*reg, v);
    }

    for inst in &block.insts {
        match inst {
            Inst::Assign { dst, value, .. } => {
                let v = eval_rvalue(value, &env);
                env.insert(*dst, v);
            }
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
                env.insert(*dst, v);
            }
            other => {
                if let Some(dst) = other.defined_reg() {
                    env.insert(dst, AbsVal::Opaque);
                }
            }
        }
    }

    match &block.term {
        csolver_ir::Terminator::Return(Some(op)) => match eval_operand(op, &env) {
            AbsVal::PtrArg { arg, off } => RetSummary::PtrFromArg { arg, offset: off },
            AbsVal::Scalar(a) => RetSummary::Scalar(a),
            AbsVal::Opaque => RetSummary::Unknown,
        },
        _ => RetSummary::Unknown,
    }
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
