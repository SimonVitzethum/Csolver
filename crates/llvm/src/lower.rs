//! Lowering the parsed LLVM-IR AST into MSIR.
//!
//! The one structural transformation is **PHI elimination**: each block's
//! leading `phi` nodes become the block's MSIR parameters, and every branch
//! into that block is given the matching incoming values as arguments. This is
//! exactly the block-argument SSA form MSIR uses.

use crate::parser::{
    LBin, LBlock, LCast, LFunc, LInst, LModule, LPred, LTerm, LType, LValue,
};
use csolver_contracts::{ApiContract, Contracts, Effect, Fill, SizeExpr};
use csolver_core::{BitVector, Error, RegionKind, Result};
use csolver_ir::{
    BasicBlock, BinOp, BlockId, Callee, CastOp, CmpOp, Const, DataLayout, FuncId, Function, Inst,
    MemKind, Module, Operand, PtrContract, RValue, RegId, SizeSpec, Terminator, Type,
};
use std::sync::OnceLock;
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
    // Sizable global definitions become known regions for the analysis; a
    // definition whose size cannot be computed is simply not recorded (its
    // symbol stays an opaque scalar).
    for g in &m.globals {
        // Packed structs have no padding: the exact size is the field sum.
        let size = if g.packed {
            let LType::Struct(fields) = &g.ty else { continue };
            fields.iter().try_fold(0u64, |acc, f| {
                lower_type(f).size_bytes(&LAYOUT).and_then(|s| acc.checked_add(s))
            })
        } else {
            lower_type(&g.ty).size_bytes(&LAYOUT)
        };
        if let Some(size) = size.filter(|s| *s > 0) {
            module.globals.insert(
                g.name.clone(),
                csolver_ir::GlobalDef { size, align: g.align.max(1), writable: g.writable },
            );
        }
        // Symbol-pointer fields whose target is a function *defined in this
        // module* become a devirtualisation table for the global. Fields naming
        // an undefined/external symbol are dropped (they stay opaque — sound).
        let resolved: Vec<(u64, FuncId)> = g
            .fn_ptrs
            .iter()
            .filter_map(|(off, name)| func_ids.get(name).map(|fid| (*off, *fid)))
            .collect();
        if !resolved.is_empty() {
            module.global_fn_ptrs.insert(g.name.clone(), resolved);
        }
    }
    for (i, f) in m.funcs.iter().enumerate() {
        let fid = FuncId(i as u32);
        match lower_function(f, fid, &func_ids, &m.debuginfo) {
            Ok((func, contracts, raw_ptr_hints)) => {
                for (idx, c) in contracts {
                    module.param_contracts.insert((fid, idx), c);
                }
                for (idx, hint) in raw_ptr_hints {
                    module.raw_ptr_hints.insert((fid, idx), hint);
                }
                if f.internal {
                    module.internal.insert(fid);
                }
                module.functions.push(func);
            }
            // Per-function lowering recovery: record and move on.
            Err(e) => module.unanalyzed.push((f.name.clone(), e.to_string())),
        }
    }
    // The provenance lattice (label id → granted capability ids) that the emitted
    // `ProvLabel`/`CapRequire` instructions reference; same for every module.
    module.prov_grants = prov_interner().grants.clone();
    Ok(module)
}

struct Ctx<'a> {
    regs: HashMap<String, RegId>,
    next_reg: u32,
    blocks: HashMap<String, BlockId>,
    func: &'a LFunc,
    func_ids: &'a HashMap<String, FuncId>,
    /// Checked-arithmetic tuples: the result reg of an
    /// `llvm.{s,u}{add,sub,mul}.with.overflow` call → its `(op, a, b)`, so a later
    /// `extractvalue`'s field 0 recovers the arithmetic (field 1 is the overflow
    /// flag, which only feeds the panic branch and stays opaque).
    checked_arith: HashMap<String, (BinOp, LValue, LValue)>,
    /// From debug info: the *result* local of a `load ptr` that reads a reference
    /// *field* of a DWARF-typed struct (`load ptr, gep(&mut StructT, offset)`
    /// where the member at `offset` is a `&T`). Such a loaded pointer is a valid
    /// reference — `lower_block` materialises it with a `RefWitness`.
    field_ref_loads: HashMap<String, (u64, u32, bool, bool)>,
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
            // A folded constant gep keeps its base symbol and byte offset, so
            // an access through it is checked against the global's region. An
            // uncomputable stride degrades to an opaque symbol (never a guess).
            LValue::GlobalOff { name, elem, index } => {
                match lower_type(elem).size_bytes(&LAYOUT) {
                    Some(stride) => {
                        let off = (stride as i128).saturating_mul(*index);
                        match i64::try_from(off) {
                            Ok(off) => Operand::Const(Const::SymbolOffset(name.clone(), off)),
                            Err(_) => Operand::Const(Const::Symbol(name.clone())),
                        }
                    }
                    None => Operand::Const(Const::Symbol(name.clone())),
                }
            }
        })
    }
}

#[allow(clippy::type_complexity)]
fn lower_function(
    f: &LFunc,
    id: FuncId,
    func_ids: &HashMap<String, FuncId>,
    debuginfo: &crate::debuginfo::DebugInfo,
) -> Result<(Function, Vec<(u32, PtrContract)>, Vec<(u32, (u64, u32))>)> {
    let mut ctx = Ctx {
        regs: HashMap::new(),
        next_reg: 0,
        blocks: HashMap::new(),
        func: f,
        func_ids,
        checked_arith: checked_arith_map(f),
        field_ref_loads: dwarf_field_loads(f, debuginfo),
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
    let mut raw_ptr_hints: Vec<(u32, (u64, u32))> = Vec::new();
    for (idx, p) in f.params.iter().enumerate() {
        if !matches!(p.ty, LType::Ptr) {
            continue;
        }
        let common = |size| {
            (
                idx as u32,
                PtrContract {
                    assumption: None,
                    refutable: true,
                    size,
                    align: p.align.unwrap_or(1),
                    readable: !p.writeonly,
                    writable: !p.readonly,
                    sentinel: None,
                },
            )
        };
        // `sret(T)`/`byval(T)` guarantee a caller-provided buffer of `sizeof(T)`
        // bytes — semantically a `dereferenceable`. Checking it *before* the
        // slice heuristic matters: an sret pointer followed by an integer
        // parameter is *not* a `(ptr, len)` slice, and mispairing it sized the
        // region by an arbitrary value — a false FAIL on every sret store.
        let abi_size = p.abi_buf.as_ref().and_then(|t| lower_type(t).size_bytes(&LAYOUT));
        if let Some(n) = p.deref.or(abi_size) {
            contracts.push(common(SizeSpec::Bytes(n)));
        } else if p.abi_buf.is_none() {
            // The slice heuristic; else fall back to debug info.
            if let Some((len_param, elem_size)) = detect_slice(f, idx) {
                contracts.push(common(SizeSpec::ParamElements { len_param, elem_size }));
            } else if let Some(c) = f
                .dbg
                .and_then(|sp| debuginfo.param_ref(sp, idx as u32 + 1))
            {
                // Debug info recovered a *reference* pointee (`&T`/`&mut T`, C++
                // `T&`) that the opaque `ptr` erased: a live region of the
                // pointee's size, resting on `debuginfo` as its trust basis. Raw
                // pointers get no contract (see `crate::debuginfo`). The `&mut`
                // write access is intersected with any `readonly` attribute.
                contracts.push((
                    idx as u32,
                    PtrContract {
                        assumption: Some("debuginfo"),
                        refutable: true,
                        size: SizeSpec::Bytes(c.size),
                        align: p.align.unwrap_or(1),
                        readable: !p.writeonly,
                        writable: c.writable && !p.readonly,
                        sentinel: None,
                    },
                ));
            } else if let Some((size, align)) = f
                .dbg
                .and_then(|sp| debuginfo.param_raw_ptr(sp, idx as u32 + 1))
                .or_else(|| infer_raw_ptr_pointee(f, &p.name))
            {
                // A raw pointer (`T*`) of known pointee size gets no contract by
                // itself (it may dangle) — but record the size as a *hint*, applied
                // only under the opt-in `assume_valid_params`. The size comes from
                // debug info, or (kernel IR is built without it) is inferred from how
                // the parameter is used: `gep %struct.T, ptr %p, 0, …` reveals that
                // `%p` points at a `%struct.T`.
                raw_ptr_hints.push((idx as u32, (size, align)));
            }
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
        // `invoke` is a terminator that also *defines* a value (`%r = invoke …`);
        // register it here too, else the normal successor's use is undefined.
        if let LTerm::Invoke { dst: Some(dst), .. } | LTerm::CallBr { dst: Some(dst), .. } = &b.term {
            ctx.define(dst);
        }
    }

    // Lower blocks. (`&mut ctx`: `invoke` needs a fresh register for its
    // unconstrained unwind-branch condition.)
    let mut blocks = Vec::with_capacity(f.blocks.len());
    for (i, b) in f.blocks.iter().enumerate() {
        blocks.push(lower_block(&mut ctx, b, BlockId(i as u32))?);
    }

    // Entry seeds (whole-object cross-syscall provenance): a `seed arg_k <label>` contract
    // on THIS function labels the parameter's object at entry (an `Inst::ProvLabel` prepended
    // to the entry block), so a sink can be told its object may carry the provenance a sibling
    // syscall operation left on it. The in-place gate keeps this from false-FAILing the safe
    // path. Applied at the *definition* (not at call sites — see `emit_contract`).
    let seeds = entry_seed_insts(&f.name, &params);
    if !seeds.is_empty() {
        if let Some(entry) = blocks.first_mut() {
            let mut s = seeds;
            s.append(&mut entry.insts);
            entry.insts = s;
        }
    }

    let function = Function {
        id,
        name: f.name.clone(),
        params,
        ret_ty: lower_type(&f.ret),
        blocks,
        entry: BlockId(0),
    };
    Ok((function, contracts, raw_ptr_hints))
}

/// A per-function pre-pass over debug info: the *result* locals of `load ptr`
/// instructions that read a **reference field** of a DWARF-typed struct
/// parameter, mapped to the field's `(pointee size, writable)`. The connecting
/// dataflow is intra-block and mechanical (exactly what rustc emits):
///
/// ```text
/// store ptr %self, %self.dbg.spill        ; the debug spill …
/// %r = load ptr, %self.dbg.spill          ; … reloaded (keeps %self's struct)
/// %f = getelementptr i8, ptr %r, i64 OFF  ; a byte offset into the struct
/// %fld = load ptr, ptr %f                 ; the field pointer — a valid ref
/// ```
///
/// Only the `&T`/`&mut T` fields are recorded (via `member_ref`); a raw-pointer
/// field is left opaque, so the recovery is sound (it grants exactly the
/// reference validity the type system guarantees).
fn dwarf_field_loads(
    f: &LFunc,
    di: &crate::debuginfo::DebugInfo,
) -> HashMap<String, (u64, u32, bool, bool)> {
    let mut out = HashMap::new();
    let Some(sp) = f.dbg else { return out };

    // `local -> DWARF struct type id it points to (at offset 0)`. Seed the
    // reference parameters whose pointee is a struct.
    let mut struct_of: HashMap<String, u32> = HashMap::new();
   
    for (i, p) in f.params.iter().enumerate() {
        if !p.name.is_empty() {
            // Seed from any pointer param (raw included) — a raw pointer's fields are
            // recovered only as `assumed`, honoured under `assume_valid_params`.
            if let Some(s) = di.param_pointee_any(sp, i as u32 + 1) {
                struct_of.insert(p.name.clone(), s);
            }
        }
    }

    // The single lowering pass follows spill round-trips and field geps in
    // program order (rustc emits the spill store/reload adjacent, so one pass
    // over the flattened instruction stream suffices).
    // `slot -> source local` for `store ptr %src, %slot`.
    let mut spill_src: HashMap<String, String> = HashMap::new();
    // `gep-result local -> (struct id, byte offset)`.
    let mut field_at: HashMap<String, (u32, u64)> = HashMap::new();

    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        match inst {
            LInst::Store { val: LValue::Local(src), ptr: LValue::Local(slot), .. } => {
                spill_src.insert(slot.clone(), src.clone());
            }
            LInst::Load { dst, ptr: LValue::Local(slot), .. } => {
                // A reload of a spilled struct pointer inherits the struct.
                if let Some(s) = spill_src.get(slot).and_then(|src| struct_of.get(src)).copied() {
                    struct_of.insert(dst.clone(), s);
                }
                // A load of a recorded reference field: record its result. A valid
                // reference (`&T`/`T&`) is unconditional; a raw pointer field is
                // recovered only under the `assume_valid_params` opt-in (`assumed`).
                if let Some(&(struct_id, off)) = field_at.get(slot) {
                    if let Some(c) = di.member_ref(struct_id, off) {
                        out.insert(dst.clone(), (c.size, c.align, c.writable, false));
                    } else if let Some((size, align)) = di.member_raw_ptr(struct_id, off) {
                        out.insert(dst.clone(), (size, align, true, true));
                    }
                }
            }
            // `gep i8, ptr %base, i64 OFF` — a byte offset into a struct.
            LInst::Gep {
                dst,
                elem,
                base: LValue::Local(base),
                index: LValue::Int(off),
            } if matches!(elem, LType::Int(8)) && *off >= 0 => {
                if let Some(&s) = struct_of.get(base) {
                    field_at.insert(dst.clone(), (s, *off as u64));
                }
            }
            // `gep %struct.T, ptr %base, 0, K` — the typed struct-field form modern
            // opaque-pointer IR (`-O2`) emits. Record the field's byte offset.
            LInst::GepChain { dst, agg_ty, base: LValue::Local(base), indices } => {
                if let Some(&s) = struct_of.get(base) {
                    if matches!(indices.first(), Some(LValue::Int(0))) {
                        if let Some(off) = gepchain_const_offset(&lower_type(agg_ty), &indices[1..]) {
                            field_at.insert(dst.clone(), (s, off));
                        }
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// The constant byte offset of an all-constant `GepChain` navigation path into
/// `agg` (struct field / constant array index). `None` on a variable step.
fn gepchain_const_offset(agg: &Type, path: &[LValue]) -> Option<u64> {
    let mut ty = agg;
    let mut offset = 0u64;
    for step in path {
        let LValue::Int(k) = step else { return None };
        let k = u64::try_from(*k).ok()?;
        match ty {
            Type::Struct { fields, .. } => {
                offset = offset.checked_add(struct_field_offset(ty, k as u32)?)?;
                ty = fields.get(k as usize)?;
            }
            Type::Array { elem, .. } => {
                offset = offset.checked_add(k.checked_mul(elem.size_bytes(&LAYOUT)?)?)?;
                ty = elem;
            }
            _ => return None,
        }
    }
    Some(offset)
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
    // The candidate must not be a *dereferenced* index of the pointer. If some
    // `gep ptr, cand` result is loaded/stored, `cand` is an index argument
    // (`fn(&[T; N], i)`) mistaken for a slice length — pairing it would size the
    // region by the access index and refute *every* access (a false FAIL; the MIR
    // frontend, having the array type, proves these PASS). A real slice's length
    // *bounds* the index: it may form the one-past-end pointer (`gep ptr, len`),
    // but that pointer is only *compared* (`icmp %next, %end`), never dereferenced.
    if pointer_indexed_and_dereferenced_by(f, &p.name, &len.name) {
        return None;
    }
    // Beyond the negative check, pairing needs *positive* evidence that the
    // integer is a length: it indexes the pointer (the one-past-end pattern) or
    // bounds a value that does (`icmp x, len` + `gep ptr, x`; see
    // `used_as_length`). An adjacent-but-unrelated integer parameter — an index
    // (`fn(&[T; N], i)`), a plain scalar (`fn(&mut State, skipped: u64)`), or a
    // compared-but-never-indexing mask (hashbrown's `bucket_mask`) — must not
    // size the pointee: that both refutes real in-bounds accesses (a false
    // FAIL) and, worse, could *prove* an out-of-bounds access against the
    // phantom size (a false PASS, since the [slice-abi] contract is trusted).
    if !used_as_length(f, &p.name, &len.name) {
        return None;
    }
    let elem_size = slice_elem_size(f, &p.name)?;
    Some(((idx + 1) as u32, elem_size))
}

/// Whether some `getelementptr ptr_name, cand` has its result loaded or stored —
/// the signature of a dereferenced index argument, distinct from a slice length
/// (which may index the pointer to form a one-past-end bound but is only compared).
fn pointer_indexed_and_dereferenced_by(f: &LFunc, ptr_name: &str, cand: &str) -> bool {
    if cand.is_empty() {
        return false;
    }
    f.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
        matches!(inst,
            LInst::Gep { dst, base: LValue::Local(base), index: LValue::Local(ix), .. }
            if base == ptr_name && ix == cand && is_dereferenced(f, dst))
    })
}

/// Positive evidence that `cand` acts as a length for `ptr_name`: it is the
/// index of a `getelementptr` on the pointer (forming the one-past-end bound) or
/// an operand of some comparison (a bounds check). Mere adjacency in the
/// parameter list is not enough to trust the `(ptr, len)` slice ABI.
fn used_as_length(f: &LFunc, ptr_name: &str, cand: &str) -> bool {
    if cand.is_empty() {
        return false;
    }
    let geps_ptr = |name: &str| {
        f.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
            matches!(inst,
                LInst::Gep { base: LValue::Local(base), index: LValue::Local(ix), .. }
                if base == ptr_name && ix == name)
        })
    };
    // The one-past-end pattern: the length itself indexes the pointer.
    if geps_ptr(cand) {
        return true;
    }
    // The bounds-checked-index pattern: a value compared against `cand` must
    // itself index the pointer. A comparison *alone* is not evidence —
    // hashbrown's `(ptr %self, i64 %bucket_mask)` compares the mask against a
    // loaded field without ever indexing `self` by it; pairing there sized the
    // struct by the mask and refuted a real field access (a false FAIL).
    f.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
        let LInst::Icmp { a, b, .. } = inst else { return false };
        let other = match (a, b) {
            (LValue::Local(n), LValue::Local(o)) if n == cand => o,
            (LValue::Local(o), LValue::Local(n)) if n == cand => o,
            _ => return false,
        };
        geps_ptr(other)
    })
}

/// Whether local `name` is used as the address of any `load`/`store`.
fn is_dereferenced(f: &LFunc, name: &str) -> bool {
    f.blocks.iter().flat_map(|b| &b.insts).any(|inst| match inst {
        LInst::Load { ptr: LValue::Local(p), .. } | LInst::Store { ptr: LValue::Local(p), .. } => {
            p == name
        }
        _ => false,
    })
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

fn lower_block(ctx: &mut Ctx, b: &LBlock, id: BlockId) -> Result<BasicBlock> {
    let block_params: Vec<(RegId, Type)> = b
        .phis
        .iter()
        .map(|phi| Ok((ctx.reg(&phi.dst)?, lower_type(&phi.ty))))
        .collect::<Result<_>>()?;

    let mut insts = Vec::new();
    for inst in &b.insts {
        // An atomic RMW is, at this abstraction, a load (the returned old
        // value — kept only for `atomicrmw`; cmpxchg's tuple stays opaque) plus
        // a store of an unknown value. Both accesses carry their full memory
        // obligations; an opaque placeholder would silently drop them (an
        // unchecked OOB atomicrmw would be a false PASS one level up).
        if let LInst::AtomicRmw { dst, ty, ptr, tuple } = inst {
            let msir_ty = lower_type(ty);
            let align = msir_ty.align_bytes(&LAYOUT).unwrap_or(1) as u32;
            let old_dst = if *tuple { ctx.fresh() } else { ctx.reg(dst)? };
            insts.push(Inst::Load {
                dst: old_dst,
                ty: msir_ty.clone(),
                ptr: ctx.operand(ptr, 64)?,
                align,
            });
            insts.push(Inst::Store {
                ty: msir_ty,
                ptr: ctx.operand(ptr, 64)?,
                value: Operand::Const(Const::Undef),
                align,
            });
            if *tuple {
                insts.push(Inst::Assign {
                    dst: ctx.reg(dst)?,
                    ty: Type::int(64),
                    value: RValue::Use(Operand::Const(Const::Undef)),
                });
            }
            continue;
        }
        // A struct-field gep expands to a two-step chain: element stride, then
        // the exact padded field offset (needs a fresh intermediate register,
        // hence handled here rather than in the single-instruction lowering).
        if let LInst::GepField { dst, struct_ty, base, index, field } = inst {
            let s_ty = lower_type(struct_ty);
            let off = struct_field_offset(&s_ty, *field).ok_or_else(|| {
                Error::unsupported("struct-field gep with an unsizable field offset")
            })?;
            let tmp = ctx.fresh();
            insts.push(Inst::PtrOffset {
                dst: tmp,
                base: ctx.operand(base, 64)?,
                index: ctx.operand(index, 64)?,
                elem: s_ty,
            });
            insts.push(Inst::PtrOffset {
                dst: ctx.reg(dst)?,
                base: Operand::Reg(tmp),
                index: Operand::int(64, off as u128),
                elem: Type::int(8),
            });
            continue;
        }
        // A multi-level gep: walk the aggregate type through the index list,
        // emitting a PtrOffset chain — the leading index strides by `sizeof(agg)`,
        // a struct field or a constant array index folds into a byte offset, and a
        // *variable* array index emits its own scaled PtrOffset.
        if let LInst::GepChain { dst, agg_ty, base, indices } = inst {
            let out = lower_gep_chain(ctx, dst, lower_type(agg_ty), base, indices)?;
            insts.extend(out);
            continue;
        }
                // A `load ptr` that reads a *reference field* of a DWARF-typed struct
        // (see `dwarf_field_loads`): keep the load (it checks the field access),
        // then materialise its result as a valid reference — the loaded pointer
        // is a `&T`/`&mut T` by the field's declared type, so accesses through it
        // prove. Without this the loaded field pointer has lost provenance.
        if let LInst::Load { dst, ptr, align_meta, .. } = inst {
            if let Some(&(size, align, writable, assumed)) = ctx.field_ref_loads.get(dst) {
                // The field address the pointer was loaded from — so the executor can give
                // two loads of the *same* field the same materialised region.
                let src = ctx.operand(ptr, 64).ok();
                insts.push(lower_inst(ctx, inst)?);
                insts.push(Inst::RefWitness {
                    dst: ctx.reg(dst)?,
                    size: Some(size),
                    // The DWARF pointee type gives a natural alignment; an `!align`
                    // metadatum on the load is a stronger, explicit guarantee — take
                    // the larger so an aligned access through the field proves.
                    align: align.max(align_meta.unwrap_or(0)),
                    writable,
                    // A raw-pointer field is only valid under `assume_valid_params`.
                    assumed,
                    src,
                });
                continue;
            }
        }
        // A recognized library/kernel API (allocator, deallocator, user-copy, …) is
        // lowered from its **external effect contract** (crates/contracts/data/*.contract)
        // instead of a hardcoded table: an `Alloc`/`Dealloc`/`MemIntrinsic` that models the
        // API's memory effect. This keeps the path *exact* (an `Inst::Call` would taint it,
        // disabling refutation) and lets a new API be covered by writing one contract block.
        if let LInst::Call { dst, callee, args, ret } = inst {
            if let Some(contract) = contracts().lookup(callee) {
                if emit_contract(ctx, &mut insts, contract, dst.as_deref(), args, ret)? {
                    continue;
                }
            }
        }
        insts.push(lower_inst(ctx, inst)?);
    }

    let term = match &b.term {
        // `invoke`: emit the call, then branch to *both* the normal and the
        // unwind-cleanup successor via an unconstrained condition (a fresh,
        // never-defined register), so the cleanup path — which may run `Drop`
        // code — is analysed, not dropped. Modelling only the normal edge would be
        // a false-PASS hole.
        LTerm::Invoke { dst, ret, callee, args, ok, cleanup } => {
            let call_dst = dst.as_deref().map(|d| ctx.reg(d)).transpose()?;
            let callee_ir = match ctx.func_ids.get(callee) {
                Some(id) => Callee::Direct(*id),
                None => Callee::Symbol(callee.clone()),
            };
            let call_args = args
                .iter()
                .map(|a| ctx.operand(a, 64))
                .collect::<Result<Vec<_>>>()?;
            insts.push(Inst::Call {
                dst: call_dst,
                callee: callee_ir,
                args: call_args,
                ret_ty: lower_type(ret),
                ret_ref: None,
            });
            let then_args = branch_args(ctx, &b.label, ok)?;
            let else_args = branch_args(ctx, &b.label, cleanup)?;
            let then_blk = ctx.block(ok)?;
            let else_blk = ctx.block(cleanup)?;
            let cond = ctx.fresh();
            Terminator::CondBr {
                cond: Operand::Reg(cond),
                then_blk,
                then_args,
                else_blk,
                else_args,
            }
        }
        // `callbr` (inline-asm goto): the asm may clobber memory and control may
        // continue at the fallthrough or any listed label. Emit the asm as an opaque
        // (memory-havoc) call, then a Switch to *every* target on a fresh scrutinee,
        // so all successors are analysed (dropping any would be a false-PASS hole).
        LTerm::CallBr { dst, targets } => {
            let call_dst = dst.as_deref().map(|d| ctx.reg(d)).transpose()?;
            insts.push(Inst::Call {
                dst: call_dst,
                callee: Callee::Symbol("<inline asm>".into()),
                args: Vec::new(),
                ret_ty: Type::int(64),
                ret_ref: None,
            });
            let blk = |name: &str| ctx.block(name);
            let default = blk(&targets[0])?;
            let cases = targets[1..]
                .iter()
                .enumerate()
                .map(|(i, t)| Ok((BitVector::new(64, i as u128), blk(t)?)))
                .collect::<Result<Vec<_>>>()?;
            Terminator::Switch { value: Operand::Reg(ctx.fresh()), cases, default }
        }
        _ => lower_term(ctx, &b.label, &b.term)?,
    };

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
        LInst::Load { dst, ty, ptr, align, .. } => Inst::Load {
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
        // Expanded to instruction chains in `lower_block`; unreachable here.
        LInst::GepField { .. } | LInst::GepChain { .. } | LInst::AtomicRmw { .. } => {
            return Err(Error::unsupported("multi-instruction lowering outside lower_block"))
        }
        LInst::Opaque { dst } => Inst::Assign {
            dst: ctx.reg(dst)?,
            ty: Type::int(64),
            value: RValue::Use(Operand::Const(Const::Undef)),
        },
        LInst::ExtractValue { dst, agg, index } => {
            let dst_reg = ctx.reg(dst)?;
            // Field 0 of a checked-arith tuple is the arithmetic result; anything
            // else (the overflow flag, or a non-checked aggregate) stays opaque —
            // sound, and the flag only guards the panic branch.
            let checked = match agg {
                LValue::Local(name) if *index == 0 => ctx.checked_arith.get(name),
                _ => None,
            };
            match checked {
                Some((op, a, b)) => Inst::Assign {
                    dst: dst_reg,
                    ty: Type::int(64),
                    value: RValue::Bin {
                        op: *op,
                        lhs: ctx.operand(a, 64)?,
                        rhs: ctx.operand(b, 64)?,
                    },
                },
                None => Inst::Assign {
                    dst: dst_reg,
                    ty: Type::int(64),
                    value: RValue::Use(Operand::Const(Const::Undef)),
                },
            }
        }
        LInst::Call { dst, ret, callee, args } => {
            let dst = dst.as_deref().map(|d| ctx.reg(d)).transpose()?;
            if let (Some(_), Some(d)) = (overflow_intrinsic_op(callee), dst) {
                // A checked-arithmetic intrinsic is pure arithmetic; its tuple
                // result is recovered field-wise at `extractvalue`, so the tuple
                // register itself is never read — an opaque placeholder.
                Inst::Assign {
                    dst: d,
                    ty: Type::int(64),
                    value: RValue::Use(Operand::Const(Const::Undef)),
                }
            } else if is_noop_intrinsic(callee) {
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
                        ret_ref: None,
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
                Inst::Call { dst, callee, args, ret_ty: lower_type(ret), ret_ref: None }
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
        // Handled in `lower_block` (they need to append the call instruction);
        // defensive and sound if ever reached directly.
        LTerm::Invoke { .. } | LTerm::CallBr { .. } => Terminator::Unreachable,
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

/// Infer the pointee `(size, align)` of a raw pointer parameter from its **use**,
/// when debug info is absent (kernel IR is built without it). A single-element gep
/// `gep %struct.T, ptr %param, 0, …` reveals that `%param` points at a `%struct.T`;
/// take the largest such aggregate (a union is accessed through its biggest member).
/// Only sees a use directly on the parameter (sound at `-O1`+, where the parameter is
/// not spilled to an alloca — kernel IR is `-O2`). Returns `None` if never so used.
fn infer_raw_ptr_pointee(f: &LFunc, param_name: &str) -> Option<(u64, u32)> {
    let mut best: Option<(u64, u32)> = None;
    for b in &f.blocks {
        for inst in &b.insts {
            // A struct/array field navigation whose leading index is 0 (one element)
            // and whose base is exactly this parameter.
            let LInst::GepChain { agg_ty, base, indices, .. } = inst else { continue };
            if !matches!(base, LValue::Local(n) if n == param_name) {
                continue;
            }
            if !matches!(indices.first(), Some(LValue::Int(0))) {
                continue;
            }
            let ty = lower_type(agg_ty);
            if let (Some(size), Some(align)) = (ty.size_bytes(&LAYOUT), ty.align_bytes(&LAYOUT)) {
                if size > 0 && best.is_none_or(|(bs, _)| size > bs) {
                    best = Some((size, align as u32));
                }
            }
        }
    }
    best
}

/// Lower a multi-level `getelementptr` into a `PtrOffset` chain by walking the
/// aggregate type through the index list. The leading index strides by
/// `sizeof(agg)`; a struct field or a *constant* array index folds into a running
/// byte offset; a *variable* array index emits its own scaled `PtrOffset`. The
/// running offset (possibly zero) is folded into `dst` at the end. A step that does
/// not fit the current type (a field index into a scalar, a variable struct field)
/// is refused, never mis-offset.
fn lower_gep_chain(
    ctx: &mut Ctx,
    dst: &str,
    agg: Type,
    base: &LValue,
    indices: &[LValue],
) -> Result<Vec<Inst>> {
    let const_idx = |v: &LValue| match v {
        LValue::Int(k) if *k >= 0 => u64::try_from(*k).ok(),
        _ => None,
    };
    let mut insts = Vec::new();
    // Leading index: pointer arithmetic over the whole aggregate.
    let mut cur = ctx.fresh();
    insts.push(Inst::PtrOffset {
        dst: cur,
        base: ctx.operand(base, 64)?,
        index: ctx.operand(&indices[0], 64)?,
        elem: agg.clone(),
    });
    let mut ty = agg;
    let mut acc: u64 = 0; // accumulated constant byte offset not yet emitted
    for idx in &indices[1..] {
        match ty {
            Type::Struct { ref fields, .. } => {
                let k = const_idx(idx)
                    .ok_or_else(|| Error::unsupported("variable struct-field gep index"))?;
                acc = acc
                    .checked_add(struct_field_offset(&ty, k as u32).ok_or_else(|| {
                        Error::unsupported("struct-field gep with an unsizable offset")
                    })?)
                    .ok_or_else(|| Error::unsupported("gep offset overflow"))?;
                ty = fields
                    .get(k as usize)
                    .cloned()
                    .ok_or_else(|| Error::unsupported("struct-field gep index out of range"))?;
            }
            Type::Array { elem, .. } => {
                match const_idx(idx) {
                    Some(k) => {
                        let sz = elem
                            .size_bytes(&LAYOUT)
                            .ok_or_else(|| Error::unsupported("array gep with an unsizable elem"))?;
                        acc = acc
                            .checked_add(k.saturating_mul(sz))
                            .ok_or_else(|| Error::unsupported("gep offset overflow"))?;
                    }
                    None => {
                        // Flush the pending constant offset, then a scaled step.
                        if acc > 0 {
                            let n = ctx.fresh();
                            insts.push(Inst::PtrOffset {
                                dst: n,
                                base: Operand::Reg(cur),
                                index: Operand::int(64, acc as u128),
                                elem: Type::int(8),
                            });
                            cur = n;
                            acc = 0;
                        }
                        let n = ctx.fresh();
                        insts.push(Inst::PtrOffset {
                            dst: n,
                            base: Operand::Reg(cur),
                            index: ctx.operand(idx, 64)?,
                            elem: (*elem).clone(),
                        });
                        cur = n;
                    }
                }
                ty = *elem;
            }
            _ => return Err(Error::unsupported("gep navigation into a non-aggregate")),
        }
    }
    // Fold the remaining constant offset (possibly zero) into the destination.
    insts.push(Inst::PtrOffset {
        dst: ctx.reg(dst)?,
        base: Operand::Reg(cur),
        index: Operand::int(64, acc as u128),
        elem: Type::int(8),
    });
    Ok(insts)
}

/// The padded byte offset of `field` inside struct type `s` (LP64 layout) —
/// the same alignment rule the IR's own `Type::Struct` sizing uses.
fn struct_field_offset(s: &Type, field: u32) -> Option<u64> {
    let Type::Struct { fields, packed } = s else { return None };
    let mut offset: u64 = 0;
    for (i, f) in fields.iter().enumerate() {
        let align = if *packed { 1 } else { f.align_bytes(&LAYOUT)?.max(1) };
        offset = offset.checked_add(align - 1)? / align * align;
        if i as u32 == field {
            return Some(offset);
        }
        offset = offset.checked_add(f.size_bytes(&LAYOUT)?)?;
    }
    None
}

fn inst_dst(inst: &LInst) -> Option<&str> {
    match inst {
        LInst::Alloca { dst, .. }
        | LInst::Load { dst, .. }
        | LInst::Gep { dst, .. }
        | LInst::Bin { dst, .. }
        | LInst::Icmp { dst, .. }
        | LInst::ExtractValue { dst, .. }
        | LInst::Opaque { dst, .. }
        | LInst::GepField { dst, .. }
        | LInst::GepChain { dst, .. }
        | LInst::AtomicRmw { dst, .. }
        | LInst::Cast { dst, .. } => Some(dst),
        LInst::Call { dst, .. } => dst.as_deref(),
        LInst::Store { .. } => None,
    }
}

fn lower_type(ty: &LType) -> Type {
    match ty {
        LType::Void => Type::Unit,
        // Compiler-annotation operands: zero-sized, never memory.
        LType::Metadata => Type::Unit,
        LType::Int(bits) => Type::int(*bits),
        LType::Ptr => Type::ptr(Type::Unit),
        // A vector is modelled by its byte footprint, like an array of the same
        // element count — enough for the access-size memory-safety reasoning.
        LType::Array(elem, n) | LType::Vector(elem, n) => Type::Array {
            elem: Box::new(lower_type(elem)),
            len: *n,
        },
        // A struct lowers structurally, so the IR layout machinery computes the
        // exact padded size/alignment — a `gep %"T", ptr, i64 N` strides by
        // `sizeof(T)`, and an under-sized placeholder would misplace every
        // subsequent access.
        LType::Struct(fields) => {
            Type::Struct { fields: fields.iter().map(lower_type).collect(), packed: false }
        }
        LType::PackedStruct(fields) => {
            Type::Struct { fields: fields.iter().map(lower_type).collect(), packed: true }
        }
        // Unreachable: the parser resolves every named reference or fails the
        // function. A total function is cheaper to keep correct than a panic; a
        // zero-size type can never *prove* an access in-bounds.
        LType::Named(_) => Type::Opaque { bytes: 0, align: 1 },
    }
}

/// The `(op, a, b)` of every checked-arithmetic tuple in `f`, keyed by the
/// intrinsic call's result register — so a later `extractvalue`, field 0, recovers
/// the arithmetic (field 1, the overflow flag, stays opaque).
fn checked_arith_map(f: &LFunc) -> HashMap<String, (BinOp, LValue, LValue)> {
    let mut m = HashMap::new();
    for b in &f.blocks {
        for inst in &b.insts {
            if let LInst::Call { dst: Some(dst), callee, args, .. } = inst {
                if let (Some(op), [a, b]) = (overflow_intrinsic_op(callee), args.as_slice()) {
                    m.insert(dst.clone(), (op, a.clone(), b.clone()));
                }
            }
        }
    }
    m
}

/// Map `llvm.{s,u}{add,sub,mul}.with.overflow.iN` to its arithmetic op (signed vs
/// unsigned is the same bitvector operation for memory-safety reasoning).
fn overflow_intrinsic_op(callee: &str) -> Option<BinOp> {
    let kind = callee.strip_prefix("llvm.")?;
    if !kind.contains(".with.overflow.") {
        return None;
    }
    Some(match kind.split('.').next()? {
        "sadd" | "uadd" => BinOp::Add,
        "ssub" | "usub" => BinOp::Sub,
        "smul" | "umul" => BinOp::Mul,
        _ => return None,
    })
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

/// The API effect contracts, parsed once from the embedded default files (allocators,
/// deallocators, user-copies). Recognized calls are lowered from these instead of a
/// hardcoded table; see [`csolver_contracts`] and `crates/contracts/data/*.contract`.
fn contracts() -> &'static Contracts {
    static CONTRACTS: OnceLock<Contracts> = OnceLock::new();
    CONTRACTS.get_or_init(Contracts::defaults)
}

/// Interns provenance label and capability names (a shared namespace) to stable `u32`
/// ids, and precomputes the id-keyed grant relation, so the emitted `ProvLabel`/
/// `CapRequire` instructions and `Module::prov_grants` speak in ids. Built once from the
/// global contracts (deterministic: names sorted before assigning ids).
struct ProvInterner {
    ids: HashMap<String, u32>,
    grants: HashMap<u32, std::collections::HashSet<u32>>,
}

impl ProvInterner {
    fn id(&self, name: &str) -> Option<u32> {
        self.ids.get(name).copied()
    }
}

/// The entry-seed `ProvLabel`s for a function definition: from any `seed arg_k <label>`
/// effects in this function's own contract (`Effect::Seed`), a `ProvLabel` on the named
/// parameter. Empty for a function with no seed contract (the sound default).
fn entry_seed_insts(name: &str, params: &[(RegId, Type)]) -> Vec<Inst> {
    let Some(contract) = contracts().lookup(name) else { return Vec::new() };
    let mut seeds = Vec::new();
    for effect in &contract.effects {
        if let Effect::Seed { arg, label } = effect {
            if let (Some((reg, _)), Some(id)) = (params.get(*arg), prov_interner().id(label)) {
                seeds.push(Inst::ProvLabel { ptr: Operand::Reg(*reg), label: id });
            }
        }
    }
    seeds
}

fn prov_interner() -> &'static ProvInterner {
    static INTERNER: OnceLock<ProvInterner> = OnceLock::new();
    INTERNER.get_or_init(|| {
        let c = contracts();
        // Collect every label/capability name: the lattice keys (labels) and values
        // (capabilities), plus any name mentioned by a `label`/`require` effect.
        let mut names: Vec<&str> = Vec::new();
        for (label, caps) in c.lattice() {
            names.push(label);
            names.extend(caps.iter().map(String::as_str));
        }
        for contract in c.iter() {
            for effect in &contract.effects {
                match effect {
                    Effect::Label { label, .. } => names.push(label),
                    Effect::Require { cap, .. } => names.push(cap),
                    _ => {}
                }
            }
        }
        names.sort_unstable();
        names.dedup();
        let ids: HashMap<String, u32> =
            names.iter().enumerate().map(|(i, n)| (n.to_string(), i as u32)).collect();
        let grants = c
            .lattice()
            .iter()
            .filter_map(|(label, caps)| {
                let lid = *ids.get(label)?;
                let cset = caps.iter().filter_map(|c| ids.get(c).copied()).collect();
                Some((lid, cset))
            })
            .collect();
        ProvInterner { ids, grants }
    })
}

/// Lower a recognized API call from its `contract` into the modelling MSIR instructions.
/// Returns `true` if the call was handled (and should not fall through to a generic call).
fn emit_contract(
    ctx: &mut Ctx,
    insts: &mut Vec<Inst>,
    contract: &ApiContract,
    dst: Option<&str>,
    args: &[LValue],
    ret: &LType,
) -> Result<bool> {
    let mut handled = false;
    let mut result_bound = false;
    for effect in &contract.effects {
        match effect {
            // A fresh heap region (byte-granular, `elem = i8`) whose result pointer is
            // the call value — only meaningful when that result is actually used.
            Effect::Alloc { size, align } => {
                let Some(dst) = dst else { continue };
                let Some(count) = size_operand(ctx, insts, size, args)? else { continue };
                insts.push(Inst::Alloc {
                    dst: ctx.reg(dst)?,
                    region: RegionKind::Heap,
                    elem: Type::int(8),
                    count,
                    align: *align,
                });
                handled = true;
                result_bound = true;
            }
            Effect::Free { ptr } => {
                if let Some(a) = args.get(*ptr) {
                    insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: ctx.operand(a, 64)? });
                    handled = true;
                }
            }
            // A bulk write of `len` bytes to the argument buffer — carries the in-bounds
            // obligation (refutable via `check_mem_intrinsic`). `fill=user` taints the
            // region so a value read back is a genuine adversarial input.
            Effect::Write { ptr, len, fill } => {
                if let Some(a) = args.get(*ptr) {
                    let Some(len) = size_operand(ctx, insts, len, args)? else { continue };
                    let kind = match fill {
                        Fill::User => MemKind::UserFill,
                        Fill::Undef => MemKind::Set,
                    };
                    insts.push(Inst::MemIntrinsic { kind, dst: ctx.operand(a, 64)?, src: None, len });
                    handled = true;
                }
            }
            // A bulk read is modelled as a bounded `Set` of the buffer: it carries the
            // same in-bounds obligation (the read must stay within the region), no taint.
            Effect::Read { ptr, len } => {
                if let Some(a) = args.get(*ptr) {
                    let Some(len) = size_operand(ctx, insts, len, args)? else { continue };
                    insts.push(Inst::MemIntrinsic {
                        kind: MemKind::Set,
                        dst: ctx.operand(a, 64)?,
                        src: None,
                        len,
                    });
                    handled = true;
                }
            }
            // Provenance labelling / capability requirements (the Copy-Fail write-to-a-
            // read-only-page class): the label/cap names are interned to ids the executor
            // resolves against `Module::prov_grants`. These do NOT mark the call handled —
            // an otherwise-unmodelled call still falls through to a generic (opaque) call,
            // it just also carries the provenance effect.
            Effect::Label { ptr, label } => {
                if let (Some(a), Some(id)) = (args.get(*ptr), prov_interner().id(label)) {
                    insts.push(Inst::ProvLabel { ptr: ctx.operand(a, 64)?, label: id });
                }
            }
            Effect::Require { ptr, cap } => {
                if let (Some(a), Some(id)) = (args.get(*ptr), prov_interner().id(cap)) {
                    insts.push(Inst::CapRequire { ptr: ctx.operand(a, 64)?, cap: id });
                }
            }
            Effect::Propagate { dst, src } => {
                if let (Some(d), Some(s)) = (args.get(*dst), args.get(*src)) {
                    insts.push(Inst::ProvPropagate {
                        dst: ctx.operand(d, 64)?,
                        src: ctx.operand(s, 64)?,
                    });
                }
            }
            Effect::RequireIfAlias { a, b, cap } => {
                if let (Some(pa), Some(pb), Some(id)) =
                    (args.get(*a), args.get(*b), prov_interner().id(cap))
                {
                    insts.push(Inst::CapRequireIfAlias {
                        a: ctx.operand(pa, 64)?,
                        b: ctx.operand(pb, 64)?,
                        cap: id,
                    });
                }
            }
            // A `seed` is applied at the seeded function's OWN entry (see `entry_seeds`), not
            // at call sites — a no-op here.
            Effect::Seed { .. } => {}
            // Read the two field pointers back from the object (via read-your-writes of the
            // prior field stores — the inlined `req->src = …; req->dst = …`) and apply the
            // in-place-alias capability check to them. A dedicated inst so the executor reads
            // the fields *internally* (no `ValidRead`/`InBounds` obligation on the analyzer's
            // own field reads — those would spuriously FAIL on a small/opaque object).
            Effect::RequireIfAliasFields { arg, off_a, off_b, cap } => {
                if let (Some(a), Some(id)) = (args.get(*arg), prov_interner().id(cap)) {
                    insts.push(Inst::CapRequireIfAliasFields {
                        obj: ctx.operand(a, 64)?,
                        off_a: *off_a,
                        off_b: *off_b,
                        cap: id,
                    });
                }
            }
        }
    }
    // A recognized non-allocating call still yields a result the caller may use
    // (e.g. `copy_from_user`'s bytes-not-copied) — bind it to an opaque value.
    if handled && !result_bound {
        if let Some(dst) = dst {
            insts.push(Inst::Assign {
                dst: ctx.reg(dst)?,
                ty: lower_type(ret),
                value: RValue::Use(Operand::Const(Const::Undef)),
            });
        }
    }
    Ok(handled)
}

/// Evaluate a contract [`SizeExpr`] to a byte-length operand, or `None` if it references
/// an argument the call does not have (then the effect is skipped — a sound fallthrough).
fn size_operand(
    ctx: &mut Ctx,
    insts: &mut Vec<Inst>,
    size: &SizeExpr,
    args: &[LValue],
) -> Result<Option<Operand>> {
    Ok(match size {
        SizeExpr::Arg(i) => match args.get(*i) {
            Some(a) => Some(ctx.operand(a, 64)?),
            None => None,
        },
        SizeExpr::Const(n) => Some(Operand::int(64, *n as u128)),
        SizeExpr::Product(a, b) => match (args.get(*a), args.get(*b)) {
            (Some(x), Some(y)) => {
                let lhs = ctx.operand(x, 64)?;
                let rhs = ctx.operand(y, 64)?;
                let tmp = ctx.fresh();
                insts.push(Inst::Assign {
                    dst: tmp,
                    ty: Type::int(64),
                    value: RValue::Bin { op: BinOp::Mul, lhs, rhs },
                });
                Some(Operand::Reg(tmp))
            }
            _ => None,
        },
    })
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
