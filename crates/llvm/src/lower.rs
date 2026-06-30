//! Lowering the parsed LLVM-IR AST into MSIR.
//!
//! The one structural transformation is **PHI elimination**: each block's
//! leading `phi` nodes become the block's MSIR parameters, and every branch
//! into that block is given the matching incoming values as arguments. This is
//! exactly the block-argument SSA form MSIR uses.

use crate::parser::{
    LBin, LBlock, LCast, LFunc, LInst, LModule, LPred, LTerm, LType, LValue,
};
use csolver_core::{BitVector, Error, RegionKind, Result};
use csolver_ir::{
    BasicBlock, BinOp, BlockId, Callee, CastOp, CmpOp, Const, DataLayout, FuncId, Function, Inst,
    MemKind, Module, Operand, PtrContract, RValue, RegId, SizeSpec, Terminator, Type,
};
use std::collections::HashMap;

const LAYOUT: DataLayout = DataLayout::LP64;

/// Lower a parsed module into MSIR.
pub fn lower_module(m: &LModule, name: &str) -> Result<Module> {
    let func_ids: HashMap<String, FuncId> = m
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.clone(), FuncId(i as u32)))
        .collect();

    let mut module = Module::new(name);
    // Functions the parser already gave up on.
    module.unanalyzed = m.unanalyzed.clone();
    for (i, f) in m.funcs.iter().enumerate() {
        let fid = FuncId(i as u32);
        match lower_function(f, fid, &func_ids) {
            Ok((func, contracts)) => {
                for (idx, c) in contracts {
                    module.param_contracts.insert((fid, idx), c);
                }
                module.functions.push(func);
            }
            // Per-function lowering recovery: record and move on.
            Err(e) => module.unanalyzed.push((f.name.clone(), e.to_string())),
        }
    }
    Ok(module)
}

struct Ctx<'a> {
    regs: HashMap<String, RegId>,
    next_reg: u32,
    blocks: HashMap<String, BlockId>,
    func: &'a LFunc,
    func_ids: &'a HashMap<String, FuncId>,
}

impl Ctx<'_> {
    fn define(&mut self, name: &str) -> RegId {
        if name.is_empty() {
            return self.fresh();
        }
        if let Some(r) = self.regs.get(name) {
            return *r;
        }
        let r = RegId(self.next_reg);
        self.next_reg += 1;
        self.regs.insert(name.to_string(), r);
        r
    }

    fn fresh(&mut self) -> RegId {
        let r = RegId(self.next_reg);
        self.next_reg += 1;
        r
    }

    fn reg(&self, name: &str) -> Result<RegId> {
        self.regs
            .get(name)
            .copied()
            .ok_or_else(|| Error::parse(format!("use of undefined value %{name}")))
    }

    fn block(&self, label: &str) -> Result<BlockId> {
        self.blocks
            .get(label)
            .copied()
            .ok_or_else(|| Error::parse(format!("branch to unknown block %{label}")))
    }

    fn operand(&self, v: &LValue, width: u32) -> Result<Operand> {
        Ok(match v {
            LValue::Local(name) => Operand::Reg(self.reg(name)?),
            LValue::Int(n) => Operand::int(width.max(1), *n as u128),
            LValue::Null => Operand::Const(Const::Null),
            LValue::Undef => Operand::Const(Const::Undef),
            LValue::Global(name) => Operand::Const(Const::Symbol(name.clone())),
        })
    }
}

#[allow(clippy::type_complexity)]
fn lower_function(
    f: &LFunc,
    id: FuncId,
    func_ids: &HashMap<String, FuncId>,
) -> Result<(Function, Vec<(u32, PtrContract)>)> {
    let mut ctx = Ctx {
        regs: HashMap::new(),
        next_reg: 0,
        blocks: HashMap::new(),
        func: f,
        func_ids,
    };

    // Pre-pass: assign block ids and register ids for every defined value
    // (parameters, phi results, instruction results) so forward references in
    // phis / loops resolve.
    for (i, b) in f.blocks.iter().enumerate() {
        ctx.blocks.insert(b.label.clone(), BlockId(i as u32));
    }
    let params: Vec<(RegId, Type)> = f
        .params
        .iter()
        .map(|p| (ctx.define(&p.name), lower_type(&p.ty)))
        .collect();

    // Pointer parameters with a `dereferenceable(N)` contract — or the `(ptr,
    // usize len)` slice ABI — become known live regions during analysis.
    let mut contracts = Vec::new();
    for (idx, p) in f.params.iter().enumerate() {
        if !matches!(p.ty, LType::Ptr) {
            continue;
        }
        let common = |size| {
            (
                idx as u32,
                PtrContract {
                    size,
                    align: p.align.unwrap_or(1),
                    readable: !p.writeonly,
                    writable: !p.readonly,
                },
            )
        };
        if let Some(n) = p.deref {
            contracts.push(common(SizeSpec::Bytes(n)));
        } else if let Some((len_param, elem_size)) = detect_slice(f, idx) {
            contracts.push(common(SizeSpec::ParamElements { len_param, elem_size }));
        }
    }
    for b in &f.blocks {
        for phi in &b.phis {
            ctx.define(&phi.dst);
        }
        for inst in &b.insts {
            if let Some(dst) = inst_dst(inst) {
                ctx.define(dst);
            }
        }
    }

    // Lower blocks.
    let mut blocks = Vec::with_capacity(f.blocks.len());
    for (i, b) in f.blocks.iter().enumerate() {
        blocks.push(lower_block(&ctx, b, BlockId(i as u32))?);
    }

    let function = Function {
        id,
        name: f.name.clone(),
        params,
        ret_ty: lower_type(&f.ret),
        blocks,
        entry: BlockId(0),
    };
    Ok((function, contracts))
}

/// Detect a Rust slice parameter: a `ptr` (with an `align` attribute, as `rustc`
/// emits for reference pointers) immediately followed by an integer length
/// parameter, with the element size taken from a `getelementptr` on it. Returns
/// `(length parameter index, element size)`.
fn detect_slice(f: &LFunc, idx: usize) -> Option<(u32, u64)> {
    let p = &f.params[idx];
    p.align?; // a slice/ref pointer carries an alignment
    if p.name.is_empty() {
        return None;
    }
    let len = f.params.get(idx + 1)?;
    if !matches!(len.ty, LType::Int(_)) {
        return None;
    }
    let elem_size = slice_elem_size(f, &p.name)?;
    Some(((idx + 1) as u32, elem_size))
}

/// The byte size of the element type of the first `getelementptr` on `ptr_name`.
fn slice_elem_size(f: &LFunc, ptr_name: &str) -> Option<u64> {
    for b in &f.blocks {
        for inst in &b.insts {
            if let LInst::Gep { base: LValue::Local(name), elem, .. } = inst {
                if name == ptr_name {
                    return lower_type(elem).size_bytes(&LAYOUT);
                }
            }
        }
    }
    None
}

fn lower_block(ctx: &Ctx, b: &LBlock, id: BlockId) -> Result<BasicBlock> {
    let block_params: Vec<(RegId, Type)> = b
        .phis
        .iter()
        .map(|phi| Ok((ctx.reg(&phi.dst)?, lower_type(&phi.ty))))
        .collect::<Result<_>>()?;

    let mut insts = Vec::new();
    for inst in &b.insts {
        insts.push(lower_inst(ctx, inst)?);
    }

    let term = lower_term(ctx, &b.label, &b.term)?;

    Ok(BasicBlock {
        id,
        params: block_params,
        insts,
        inst_spans: Vec::new(),
        term,
    })
}

fn lower_inst(ctx: &Ctx, inst: &LInst) -> Result<Inst> {
    Ok(match inst {
        LInst::Alloca { dst, ty, align } => Inst::Alloc {
            dst: ctx.reg(dst)?,
            region: RegionKind::Stack,
            elem: lower_type(ty),
            count: Operand::int(64, 1),
            align: align_or(*align, ty),
        },
        LInst::Load { dst, ty, ptr, align } => Inst::Load {
            dst: ctx.reg(dst)?,
            ty: lower_type(ty),
            ptr: ctx.operand(ptr, 64)?,
            align: align_or(*align, ty),
        },
        LInst::Store { ty, val, ptr, align } => Inst::Store {
            ty: lower_type(ty),
            ptr: ctx.operand(ptr, 64)?,
            value: ctx.operand(val, type_width(ty))?,
            align: align_or(*align, ty),
        },
        LInst::Gep { dst, elem, base, index } => Inst::PtrOffset {
            dst: ctx.reg(dst)?,
            base: ctx.operand(base, 64)?,
            index: ctx.operand(index, 64)?,
            elem: lower_type(elem),
        },
        LInst::Bin { dst, op, ty, a, b } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: lower_type(ty),
            value: RValue::Bin {
                op: lower_bin(*op),
                lhs: ctx.operand(a, type_width(ty))?,
                rhs: ctx.operand(b, type_width(ty))?,
            },
        },
        LInst::Icmp { dst, pred, ty, a, b } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: Type::Bool,
            value: RValue::Cmp {
                op: lower_pred(*pred),
                lhs: ctx.operand(a, type_width(ty))?,
                rhs: ctx.operand(b, type_width(ty))?,
            },
        },
        LInst::Cast { dst, op, val, to } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: lower_type(to),
            value: RValue::Cast {
                op: lower_cast(*op),
                operand: ctx.operand(val, 64)?,
                to: lower_type(to),
            },
        },
        LInst::Call { dst, ret, callee, args } => {
            let dst = dst.as_deref().map(|d| ctx.reg(d)).transpose()?;
            if is_noop_intrinsic(callee) {
                // Modelled as a no-op (does not touch caller-visible memory).
                Inst::Intrinsic { dst, name: callee.clone(), args: Vec::new() }
            } else if let Some(kind) = mem_kind(callee) {
                // `llvm.memcpy/memmove/memset(dst, src|val, len, isvolatile)`.
                if args.len() >= 3 {
                    let dst_op = ctx.operand(&args[0], 64)?;
                    let len = ctx.operand(&args[2], 64)?;
                    let src = if matches!(kind, MemKind::Copy | MemKind::Move) {
                        Some(ctx.operand(&args[1], 64)?)
                    } else {
                        None
                    };
                    Inst::MemIntrinsic { kind, dst: dst_op, src, len }
                } else {
                    // Malformed — treat as an opaque (conservative) call.
                    Inst::Call {
                        dst: None,
                        callee: Callee::Symbol(callee.clone()),
                        args: Vec::new(),
                        ret_ty: Type::Unit,
                    }
                }
            } else {
                let callee = match ctx.func_ids.get(callee) {
                    Some(id) => Callee::Direct(*id),
                    None => Callee::Symbol(callee.clone()),
                };
                let args = args
                    .iter()
                    .map(|a| ctx.operand(a, 64))
                    .collect::<Result<_>>()?;
                Inst::Call { dst, callee, args, ret_ty: lower_type(ret) }
            }
        }
    })
}

fn lower_term(ctx: &Ctx, from: &str, term: &LTerm) -> Result<Terminator> {
    Ok(match term {
        LTerm::Ret(v) => match v {
            Some(v) => Terminator::Return(Some(ctx.operand(v, 64)?)),
            None => Terminator::Return(None),
        },
        LTerm::Br(target) => Terminator::Br {
            target: ctx.block(target)?,
            args: branch_args(ctx, from, target)?,
        },
        LTerm::CondBr(cond, t, f) => Terminator::CondBr {
            cond: ctx.operand(cond, 1)?,
            then_blk: ctx.block(t)?,
            then_args: branch_args(ctx, from, t)?,
            else_blk: ctx.block(f)?,
            else_args: branch_args(ctx, from, f)?,
        },
        LTerm::Switch { value, width, default, cases } => {
            // MSIR `Switch` carries no per-target arguments. A case/default
            // target that has phis referencing this block therefore receives
            // fresh (havoc'd) parameters in the engine — a sound
            // over-approximation, precise for the common discriminant dispatch
            // whose arms have no such phis.
            let cases = cases
                .iter()
                .map(|(cv, dest)| Ok((BitVector::new(*width, *cv as u128), ctx.block(dest)?)))
                .collect::<Result<Vec<_>>>()?;
            Terminator::Switch {
                value: ctx.operand(value, *width)?,
                cases,
                default: ctx.block(default)?,
            }
        }
        LTerm::Unreachable => Terminator::Unreachable,
    })
}

/// The arguments to pass along the edge `from -> to`: each of `to`'s phi
/// incoming values for predecessor `from`, in phi order.
fn branch_args(ctx: &Ctx, from: &str, to: &str) -> Result<Vec<Operand>> {
    let target = ctx
        .func
        .blocks
        .iter()
        .find(|b| b.label == to)
        .ok_or_else(|| Error::parse(format!("unknown block %{to}")))?;
    let mut args = Vec::with_capacity(target.phis.len());
    for phi in &target.phis {
        let (val, _) = phi
            .incomings
            .iter()
            .find(|(_, pred)| pred == from)
            .ok_or_else(|| {
                Error::parse(format!(
                    "phi %{} has no incoming value for predecessor %{from}",
                    phi.dst
                ))
            })?;
        args.push(ctx.operand(val, type_width(&phi.ty))?);
    }
    Ok(args)
}

fn inst_dst(inst: &LInst) -> Option<&str> {
    match inst {
        LInst::Alloca { dst, .. }
        | LInst::Load { dst, .. }
        | LInst::Gep { dst, .. }
        | LInst::Bin { dst, .. }
        | LInst::Icmp { dst, .. }
        | LInst::Cast { dst, .. } => Some(dst),
        LInst::Call { dst, .. } => dst.as_deref(),
        LInst::Store { .. } => None,
    }
}

fn lower_type(ty: &LType) -> Type {
    match ty {
        LType::Void => Type::Unit,
        LType::Int(bits) => Type::int(*bits),
        LType::Ptr => Type::ptr(Type::Unit),
        // A vector is modelled by its byte footprint, like an array of the same
        // element count — enough for the access-size memory-safety reasoning.
        LType::Array(elem, n) | LType::Vector(elem, n) => Type::Array {
            elem: Box::new(lower_type(elem)),
            len: *n,
        },
    }
}

/// Memory-effect-free intrinsics that are modelled as no-ops (they must not
/// invalidate the symbolic heap or region lifetimes the way an opaque call
/// does).
/// Recognize the bulk-memory intrinsics.
fn mem_kind(name: &str) -> Option<MemKind> {
    if name.starts_with("llvm.memcpy") {
        Some(MemKind::Copy)
    } else if name.starts_with("llvm.memmove") {
        Some(MemKind::Move)
    } else if name.starts_with("llvm.memset") {
        Some(MemKind::Set)
    } else {
        None
    }
}

fn is_noop_intrinsic(name: &str) -> bool {
    name.starts_with("llvm.lifetime.")
        || name.starts_with("llvm.dbg.")
        || name.starts_with("llvm.invariant.")
        || name.starts_with("llvm.expect")
        || name == "llvm.assume"
}

fn type_width(ty: &LType) -> u32 {
    match ty {
        LType::Int(bits) => *bits,
        _ => 64,
    }
}

fn align_or(given: u32, ty: &LType) -> u32 {
    if given > 0 {
        given
    } else {
        lower_type(ty).align_bytes(&LAYOUT).unwrap_or(1) as u32
    }
}

fn lower_bin(op: LBin) -> BinOp {
    match op {
        LBin::Add => BinOp::Add,
        LBin::Sub => BinOp::Sub,
        LBin::Mul => BinOp::Mul,
        LBin::UDiv => BinOp::UDiv,
        LBin::SDiv => BinOp::SDiv,
        LBin::URem => BinOp::URem,
        LBin::SRem => BinOp::SRem,
        LBin::And => BinOp::And,
        LBin::Or => BinOp::Or,
        LBin::Xor => BinOp::Xor,
        LBin::Shl => BinOp::Shl,
        LBin::LShr => BinOp::LShr,
        LBin::AShr => BinOp::AShr,
    }
}

fn lower_pred(p: LPred) -> CmpOp {
    match p {
        LPred::Eq => CmpOp::Eq,
        LPred::Ne => CmpOp::Ne,
        LPred::Ult => CmpOp::Ult,
        LPred::Ule => CmpOp::Ule,
        LPred::Ugt => CmpOp::Ugt,
        LPred::Uge => CmpOp::Uge,
        LPred::Slt => CmpOp::Slt,
        LPred::Sle => CmpOp::Sle,
        LPred::Sgt => CmpOp::Sgt,
        LPred::Sge => CmpOp::Sge,
    }
}

fn lower_cast(c: LCast) -> CastOp {
    match c {
        LCast::Trunc => CastOp::Trunc,
        LCast::ZExt => CastOp::ZExt,
        LCast::SExt => CastOp::SExt,
        LCast::PtrToInt => CastOp::PtrToInt,
        LCast::IntToPtr => CastOp::IntToPtr,
        LCast::Bitcast => CastOp::Bitcast,
    }
}
