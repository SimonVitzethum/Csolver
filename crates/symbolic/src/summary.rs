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

    // Any non-direct call (external symbol / indirect) may do anything.
    for f in &module.functions {
        let opaque_call = f.blocks.iter().flat_map(|b| &b.insts).any(|i| {
            matches!(i, Inst::Call { callee, .. } if !matches!(callee, Callee::Direct(_)))
        });
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
            for inst in f.blocks.iter().flat_map(|b| &b.insts) {
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
    let writes = f
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .any(|i| matches!(i, Inst::Store { .. }));
    let frees = f
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .any(|i| matches!(i, Inst::Dealloc { .. }));

    // Return characterization only for single-block functions (the common
    // wrapper/accessor shape); anything more is conservatively Unknown.
    let ret = if f.blocks.len() == 1 {
        ret_of_block(f)
    } else {
        RetSummary::Unknown
    };

    Summary { ret, writes, frees }
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
