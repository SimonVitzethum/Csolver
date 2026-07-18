//! Lowering the parsed LLVM-IR AST into MSIR.
//!
//! The one structural transformation is **PHI elimination**: each block's
//! leading `phi` nodes become the block's MSIR parameters, and every branch
//! into that block is given the matching incoming values as arguments. This is
//! exactly the block-argument SSA form MSIR uses.

use crate::parser::{
    LBin, LBlock, LCast, LFunc, LInst, LModule, LOrdering, LPred, LTerm, LType, LValue,
};
use csolver_contracts::{ApiContract, Effect, Fill, ReadSink, SizeExpr, RET_ARG};
use csolver_core::{BitVector, Error, RegionKind, Result};
use csolver_ir::{
    BasicBlock, BinOp, BlockId, Callee, CastOp, CmpOp, Const, DataLayout, FuncId, Function, Inst,
    MemKind, Module, Operand, PtrContract, PtrHint, RValue, RegId, SizeSpec, Terminator, Type,
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
        // A `dereferenceable(N)` a call site asserts on this bare global is an
        // authoritative byte-size bound (clang derives it from the operand's type), so it
        // corrects a size our own type-layout computation gets wrong — e.g. a 1-byte
        // packed-struct discrepancy that would otherwise refute an exactly-sized `memcpy`
        // into the global. Sound: it only ever *raises* the size (`max`), never shrinks it.
        let hint = m.deref_hints.get(&g.name).copied();
        let size = match (size.filter(|s| *s > 0), hint) {
            (Some(s), Some(h)) => Some(s.max(h)),
            (Some(s), None) => Some(s),
            (None, Some(h)) => Some(h),
            (None, None) => None,
        };
        if let Some(size) = size {
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
            Ok((func, contracts, raw_ptr_hints, reg_ptr_hints)) => {
                for (idx, c) in contracts {
                    module.param_contracts.insert((fid, idx), c);
                }
                for (idx, hint) in raw_ptr_hints {
                    module.raw_ptr_hints.insert((fid, idx), hint);
                }
                for (reg, hint) in reg_ptr_hints {
                    module.reg_ptr_hints.insert((fid, reg), hint);
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
    module.prov_grants = prov_interner().grants().clone();
    collect_mmio_handlers(m, &func_ids, &mut module);
    Ok(module)
}

/// Record every **MMIO dispatch handler** in the module (see `Module::mmio_handlers`): the
/// `.read`/`.write` function of a `MemoryRegionOps` registered via
/// `memory_region_init_io(mr, owner, ops, opaque, name, size)`. The 3rd argument names the ops
/// global (whose field-0 / field-8 pointers are the read / write handlers) and the 6th is the
/// region byte size (recorded when constant). Precise by construction — only a global actually
/// passed as the `ops` operand is treated as a `MemoryRegionOps`, so no unrelated function is
/// ever constrained (which would be a false PASS).
fn collect_mmio_handlers(m: &LModule, _func_ids: &HashMap<String, FuncId>, module: &mut Module) {
    // The MMIO-registration functions and where each puts the `ops` global and the region size
    // in its argument list. `memory_region_init_io(mr, owner, ops, opaque, name, size)` is the
    // core one; `register_init_block{8,32,64}(owner, rae, num, ri, ops, name, size)` is QEMU's
    // register-array wrapper (which forwards to `memory_region_init_io`) — recognising it too is
    // what catches `register_read_memory`, whose ops global lives in the device file while the
    // handler itself is defined in `hw/core/register.c`.
    let reg_site = |callee: &str| -> Option<(usize, usize)> {
        match callee {
            "memory_region_init_io" => Some((2, 5)),
            // register_init_block{8,32,64}(owner, rae, num, regs_info, regs, ops, debug, size):
            // the ops global is argument 5 and the region byte size argument 7.
            "register_init_block8" | "register_init_block32" | "register_init_block64" => {
                Some((5, 7))
            }
            _ => None,
        }
    };
    // ops-global name → region size (`None` if the init call passed a non-constant size).
    let mut ops_size: HashMap<&str, Option<u64>> = HashMap::new();
    for f in &m.funcs {
        for inst in f.blocks.iter().flat_map(|b| &b.insts) {
            let LInst::Call { callee, args, .. } = inst else { continue };
            let Some((ops_idx, size_idx)) = reg_site(callee) else { continue };
            let Some(LValue::Global(ops)) = args.get(ops_idx) else { continue };
            let size = match args.get(size_idx) {
                Some(LValue::Int(n)) if *n >= 0 => Some(*n as u64),
                _ => None,
            };
            // A later call with a constant size wins over an earlier `None` for the same ops.
            let e = ops_size.entry(ops.as_str()).or_insert(None);
            if e.is_none() {
                *e = size;
            }
        }
    }
    if ops_size.is_empty() {
        return;
    }
    // `MemoryRegionOps` field byte offsets → the access-size parameter index of the handler
    // stored there. `.read`/`.write` (offsets 0/8) are `(opaque, addr, size)` — size is
    // parameter 2. `.read_with_attrs`/`.write_with_attrs` (offsets 16/24) insert a data
    // pointer/value at parameter 2, so their `size` is parameter 3.
    let size_param_of = |off: u64| match off {
        0 | 8 => Some(2u32),
        16 | 24 => Some(3u32),
        _ => None,
    };
    for g in &m.globals {
        let Some(&region_size) = ops_size.get(g.name.as_str()) else { continue };
        for (off, target) in &g.fn_ptrs {
            // Record by handler *name* (not FuncId): the handler may be defined in another file
            // (`register_read_memory`), so it is resolved against the analysed function by name.
            if let Some(size_param) = size_param_of(*off) {
                module
                    .mmio_handlers
                    .insert(target.clone(), csolver_ir::MmioHandler { region_size, size_param });
            }
        }
    }
}

pub(crate) struct Ctx<'a> {
    pub(crate) regs: HashMap<String, RegId>,
    pub(crate) next_reg: u32,
    pub(crate) blocks: HashMap<String, BlockId>,
    pub(crate) func: &'a LFunc,
    pub(crate) func_ids: &'a HashMap<String, FuncId>,
    /// Checked-arithmetic tuples: the result reg of an
    /// `llvm.{s,u}{add,sub,mul}.with.overflow` call → its `(op, a, b)`, so a later
    /// `extractvalue`'s field 0 recovers the arithmetic (field 1 is the overflow
    /// flag, which only feeds the panic branch and stays opaque).
    pub(crate) checked_arith: HashMap<String, (BinOp, LValue, LValue)>,
    /// From debug info: the *result* local of a `load ptr` that reads a reference
    /// *field* of a DWARF-typed struct (`load ptr, gep(&mut StructT, offset)`
    /// where the member at `offset` is a `&T`). Such a loaded pointer is a valid
    /// reference — `lower_block` materialises it with a `RefWitness`.
    pub(crate) field_ref_loads: HashMap<String, (u64, u32, bool, bool)>,
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
            // A scalar wider than the 128-bit concrete value domain (kernel crypto /
            // SIMD big-integers such as `i256`/`i512`) cannot be represented as a
            // `BitVector`; model such a constant as an opaque unknown rather than
            // crashing. Sound: the analysis then treats it as unconstrained (top), so
            // it can only lose precision, never yield a false PASS.
            LValue::Int(_) if width > 128 => Operand::Const(Const::Undef),
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
) -> Result<(Function, Vec<(u32, PtrContract)>, Vec<(u32, (u64, u32))>, Vec<(RegId, PtrHint)>)> {
    let mut ctx = Ctx {
        regs: HashMap::new(),
        next_reg: 0,
        blocks: HashMap::new(),
        func: f,
        func_ids,
        checked_arith: checked_arith_map(f),
        field_ref_loads: {
            // DWARF member-provenance (distinguishes valid-ref from raw, unconditional where
            // the type says `&T`), then the type-directed gep recovery for the loads DWARF did
            // not reach (a base pointer rooted in a call/global/`current`, not a parameter —
            // the dominant real-kernel case). DWARF wins on a conflict (it is the more precise
            // source); the gep recovery only fills loads DWARF left uncovered.
            let mut m = dwarf_field_loads(f, debuginfo);
            for (dst, rec) in typed_gep_field_loads(f, debuginfo) {
                m.entry(dst).or_insert(rec);
            }
            m
        },
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
            } else if let Some((len_param, elem_size)) = detect_c_buffer(f, idx) {
                // A C `(buf, len)` pair: the body indexes `buf` by something `len` bounds.
                // C guarantees no such pairing (unlike Rust's slice ABI), so this rests on its
                // own assumption id and is honoured only under `--assume-param-buffer-len`;
                // with the flag off the executor drops the contract and the parameter stays
                // uncontracted, exactly as before.
                contracts.push((
                    idx as u32,
                    PtrContract {
                        assumption: Some("param-buffer-len"),
                        refutable: true,
                        size: SizeSpec::ParamElements { len_param, elem_size },
                        align: p.align.unwrap_or(1),
                        readable: !p.writeonly,
                        writable: !p.readonly,
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
            } else if p.nonnull {
                // Last resort: a `nonnull` pointer parameter with no recoverable size (Zig
                // `*T`, and any -O0 frontend that asserts non-null but not `dereferenceable`).
                // A `SizeSpec::NonNull` contract makes it a non-null *opaque* pointer — only
                // `NoNullDeref` is discharged through it, bounds/liveness stay UNKNOWN (a
                // `nonnull` pointer may still dangle). Language-independent and always sound.
                contracts.push((
                    idx as u32,
                    PtrContract {
                        assumption: None,
                        refutable: false,
                        size: SizeSpec::NonNull,
                        align: p.align.unwrap_or(1),
                        readable: !p.writeonly,
                        writable: !p.readonly,
                        sentinel: None,
                    },
                ));
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

    let mut function = Function {
        id,
        name: f.name.clone(),
        params,
        ret_ty: lower_type(&f.ret),
        blocks,
        entry: BlockId(0),
    };
    inject_leak_and_secret_checks(&mut function);
    // Pointee size of each register that is used as a TYPED struct-gep base: `gep %struct.T,
    // ptr %r` proves `%r` designates a `%struct.T`. Carried on the module so a loop-carried
    // pointer (a moving iterator) can be given that size when it is havoc'd at the loop header
    // (see `Module::reg_ptr_hints`, `--assume-valid-loop-ptrs`); without it its region would be
    // unsized and every `in_bounds` through the iterator would stay UNKNOWN.
    // Two independent sources, because neither alone survives every optimisation level:
    //  * the **typed gep** (`gep %struct.T, ptr %r`) — authoritative where it survives (real
    //    kernel `-O2` IR keeps it for nested structs), but clang canonicalises a simple
    //    `gep %struct.T, ptr %p, 0, k` into a byte `gep i8, ptr %p, off`, erasing the type;
    //  * the **`#dbg_value` → `!DILocalVariable` → declared type** chain, which survives that
    //    canonicalisation and is what recovers `struct node *it` at `-O1`/`-O2`.
    // The gep wins on a conflict (it reflects the access the code actually performs).
    // Each hint carries the pointee's byte size and, where debug info records it, the pointee
    // type's declared alignment (`PtrHint`) — an over-aligned kernel struct then keeps its real
    // alignment instead of one guessed from the size.
    // Alignment has three sources, in decreasing authority: the pointee type's *declared*
    // alignment from debug info; the alignment clang **asserts** on the accesses through the
    // pointer (the only record left in real kernel IR, which carries no debug info at all); and,
    // failing both, one derived from the size (`PtrHint::region_align`).
    // A *declared* alignment is authoritative and used as-is (it can legitimately be lower than
    // the size suggests: `struct { int; int; }` is size 8, align 4). An *asserted* one is only a
    // lower bound — clang annotates each access with the alignment of the type being accessed, so
    // a struct read byte-wise carries `align 1` and says nothing about the struct's own
    // alignment. It therefore may only ever *raise* the size-derived alignment, never lower it.
    let asserted = asserted_base_aligns(f);
    let tails = struct_tail_extents(f);
    let derived = |size: u64| 1u32 << size.trailing_zeros().min(4);
    let mut reg_ptr_hints: HashMap<RegId, PtrHint> = HashMap::new();
    for (local, var) in &f.dbg_values {
        if let (Some(&r), Some((size, declared))) =
            (ctx.regs.get(local), debuginfo.local_pointee_bytes(*var))
        {
            if size > 0 {
                let align = if declared > 0 {
                    declared
                } else {
                    asserted.get(local.as_str()).map_or(0, |&a| a.max(derived(size)))
                };
                let tail = tails.get(local.as_str()).copied().unwrap_or(0);
                reg_ptr_hints.insert(r, PtrHint { size, align, tail });
            }
        }
    }
    // Rust slice references (`&[T]`/`&mut [T]`): a `from_raw_parts(ptr, N)` slice erases to a
    // bare pointer at `-O`, but the element type survives as the local's DWARF type and the
    // length `N` as a fat-pointer fragment (`dbg_slice_lens`). Join them by `!V` to size the
    // backing region `N * sizeof(T)`. Applied via `PtrHint`, so it only takes effect under
    // `--assume-valid-params` — the region's *validity* is the (unsafe) caller's contract,
    // same as any raw-pointer parameter; the length itself is exact from the source.
    let slice_lens: HashMap<u32, u64> = f.dbg_slice_lens.iter().copied().collect();
    for (local, var) in &f.dbg_values {
        if let (Some(&r), Some((elem, align, _writable)), Some(&len)) =
            (ctx.regs.get(local), debuginfo.slice_local_elem(*var), slice_lens.get(var))
        {
            if let Some(size) = len.checked_mul(elem).filter(|&s| s > 0) {
                // A slice hint never shrinks a region already recovered by a more specific rule.
                reg_ptr_hints.entry(r).or_insert(PtrHint { size, align, tail: 0 });
            }
        }
    }
    for (local, (size, struct_name)) in typed_gep_pointee_sizes(f) {
        if let Some(&r) = ctx.regs.get(local) {
            let align = struct_name
                .and_then(|n| debuginfo.composite_align_by_llvm_name(n))
                .or_else(|| asserted.get(local).map(|&a| a.max(derived(size))))
                .unwrap_or(0);
            let tail = tails.get(local).copied().unwrap_or(0);
            reg_ptr_hints.insert(r, PtrHint { size, align, tail });
        }
    }
    let reg_ptr_hints: Vec<(RegId, PtrHint)> = reg_ptr_hints.into_iter().collect();
    Ok((function, contracts, raw_ptr_hints, reg_ptr_hints))
}


// --- module split (mechanical refactor) ---
mod asmops;
mod block;
mod contract;
mod gep;
mod slices;
use asmops::*;
use block::*;
use contract::*;
use gep::*;
use slices::*;
