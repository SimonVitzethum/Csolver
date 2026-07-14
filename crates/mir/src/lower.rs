//! Lower a parsed MIR body into MSIR.
//!
//! The translation is deliberately conservative: a reference parameter of known
//! pointee size (`&[T; N]`, `&T`, `&mut T`) becomes a contracted region; the
//! bounds-check `assert` becomes a `CondBr` whose success edge carries the guard
//! (and whose failure edge goes to an `unreachable` panic block), so the checked
//! index `s[i]` is *proved* in bounds exactly because rustc inserted the check.
//! Anything outside the modelled subset (a `call`, an unmodelled rvalue/place)
//! is surfaced — the function is recorded unanalyzed rather than mis-lowered.

use crate::parser::{BinKind, MBlock, MConst, MStmt, MTerm, MType, MirBody, Operand, Place, RefKind, Rvalue};
use csolver_core::{Error, Result};
use crate::parser::CalleeSpec;
use csolver_ir::{
    BasicBlock, BinOp, BlockId, Callee, CmpOp, Const, DataLayout, FuncId, Function, Inst, MemKind,
    Module, Operand as IrOp, PtrContract, RValue, RefResult, RegId, SizeSpec, Terminator,
    Type,
};
use csolver_core::RegionKind;
use std::collections::HashMap;

const LAYOUT: DataLayout = DataLayout::LP64;

/// Lower every parsed MIR body into one MSIR module (per-function recovery).
pub(crate) fn lower_module(bodies: &[MirBody], failed: &[(String, String)], name: &str) -> Module {
    let func_ids: HashMap<String, FuncId> =
        bodies.iter().enumerate().map(|(i, b)| (b.name.clone(), FuncId(i as u32))).collect();
    let mut module = Module::new(name);
    // Functions the parser could not parse are reported `UNKNOWN`, not dropped.
    for (fname, reason) in failed {
        module.unanalyzed.push((fname.clone(), reason.clone()));
    }
    for (i, body) in bodies.iter().enumerate() {
        let fid = FuncId(i as u32);
        match lower_function(body, fid, &func_ids) {
            Ok((func, contracts)) => {
                for (idx, c) in contracts {
                    module.param_contracts.insert((fid, idx), c);
                }
                // A closure has an unnameable type: nothing outside its defining
                // crate item can call it, so it has internal linkage in effect.
                // Its parameter contracts are caller-established *preconditions*
                // (the guard lives at the call site), which licenses treating
                // them as prove-only (see `PtrContract::refutable`).
                if body.name.contains("{closure") {
                    module.internal.insert(fid);
                }
                module.functions.push(func);
            }
            Err(e) => module.unanalyzed.push((body.name.clone(), e.to_string())),
        }
    }
    module
}

pub(crate) struct Ctx {
    pub(crate) local_types: HashMap<u32, MType>,
    pub(crate) next_temp: u32,
    pub(crate) panic_id: u32,
    pub(crate) panic_used: bool,
    /// For a slice parameter `_k: &[T]`, the synthetic length parameter's
    /// register (so `Len((*_k))` resolves to it).
    pub(crate) slice_len: HashMap<u32, RegId>,
    /// Module function names → ids, for resolving direct calls.
    pub(crate) func_ids: HashMap<String, FuncId>,
    /// Set when a memory access cannot be lowered to a real pointer: the whole
    /// function is then rejected (reported `UNKNOWN`) rather than silently
    /// dropping the access — which would be an unsound vacuous `PASS`.
    pub(crate) lowering_failed: bool,
    /// For a checked-arithmetic tuple local `_k = AddWithOverflow(a, b)`, the
    /// arithmetic result `a + b` (its field `.0`), so `move (_k.0)` recovers it.
    pub(crate) checked_arith: HashMap<u32, IrOp>,
    /// Distinct field *paths* (`[0, 1]` for `((*p).0).1`) → a stable unique id, so
    /// a nested field gets its own FieldPtr `field` key (and thus its own disjoint
    /// synthetic offset) that never collides with a sibling or a top-level field.
    pub(crate) field_path_ids: HashMap<Vec<u32>, u32>,
    /// For an **address-taken stack local** (`_2 = &_x`) of statically-known size, the register
    /// holding its stack-region pointer — allocated once and reused, so every `&_x` yields the
    /// same region and `StorageDead(_x)` can end its lifetime (use-after-scope). Absent for a
    /// local of unknown size (kept opaque, as before — no perturbation).
    pub(crate) local_regions: HashMap<u32, RegId>,
}

/// FieldPtr `field` ids at or above this are *nested* field paths; below are plain
/// (single-level) field indices. The gap keeps the two namespaces disjoint so no
/// nested field can alias a top-level one.
const NESTED_FIELD_BASE: u32 = 1_000_000;

/// Lower one MIR body into an MSIR function plus its parameter contracts.
fn lower_function(
    body: &MirBody,
    id: FuncId,
    func_ids: &HashMap<String, FuncId>,
) -> Result<(Function, Vec<(u32, PtrContract)>)> {
    let local_types: HashMap<u32, MType> = body
        .params
        .iter()
        .chain(body.locals.iter())
        .map(|(l, t)| (*l, t.clone()))
        .collect();

    // Temporaries (for `PtrOffset` results, loaded operands) get registers above
    // every MIR local so they never collide.
    let max_local = body
        .params
        .iter()
        .map(|(l, _)| *l)
        .chain(body.blocks.iter().flat_map(block_locals))
        .max()
        .unwrap_or(0);
    let panic_id = body.blocks.iter().map(|b| b.id as u32).max().unwrap_or(0) + 1;

    let mut ctx = Ctx {
        local_types,
        next_temp: max_local + 1,
        panic_id,
        panic_used: false,
        slice_len: HashMap::new(),
        func_ids: func_ids.clone(),
        lowering_failed: false,
        checked_arith: HashMap::new(),
        field_path_ids: HashMap::new(),
        local_regions: HashMap::new(),
    };

    // Parameters and their contracts (by position). A reference parameter
    // becomes a pointer; a *sized* reference (`&[T; N]`, `&T`) gets a `Bytes`
    // contract directly, while a *slice* `&[T]` (whose length lives in the fat
    // pointer, not a separate MIR local) gets a synthetic `usize` length
    // parameter appended at the end and a `ParamElements` contract referring to
    // it — exactly the slice ABI the analysis already models.
    let mut params = Vec::new();
    let mut contracts = Vec::new();
    let mut pending_slices: Vec<(u32, u32, u64, bool)> = Vec::new();
    // Locals of `&mut T` *reference* parameters (NOT raw `*mut T`, which may legitimately
    // alias) — each gets an entry retag marker so it is a **protected root borrow** for the
    // whole function (opt-in aliasing model): the parameter borrow participates in the
    // borrow-stack, so a reborrow that invalidates it followed by a use through the parameter
    // is caught. A no-op unless `--aliasing-model` is on.
    let mut mut_ref_locals: Vec<u32> = Vec::new();
    for (idx, (local, mty)) in body.params.iter().enumerate() {
        if matches!(mty, MType::Ref(_, true)) {
            mut_ref_locals.push(*local);
        }
        match mty {
            MType::Ref(inner, mutable) | MType::Ptr(inner, mutable) => {
                params.push((RegId(*local), Type::ptr(mtype_to_ir(inner))));
                if let MType::Slice(elem) = inner.as_ref() {
                    let stride = mtype_to_ir(elem).stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                    pending_slices.push((idx as u32, *local, stride, *mutable));
                } else if let Some(size) = pointee_size(inner) {
                    contracts.push((
                        idx as u32,
                        PtrContract {
                            assumption: None,
                            refutable: true,
                            size: SizeSpec::Bytes(size),
                            align: pointee_align(inner),
                            readable: true,
                            writable: *mutable,
                            sentinel: None,
                        },
                    ));
                } else if matches!(inner.as_ref(), MType::Other) {
                    // An aggregate of statically-unknown layout (`&Struct`): an
                    // opaque-size region, so a field access through it is modelled
                    // (proved in bounds by construction, not by a byte offset).
                    contracts.push((
                        idx as u32,
                        PtrContract {
                            assumption: None,
                            refutable: true,
                            size: SizeSpec::Opaque,
                            align: 1,
                            readable: true,
                            writable: *mutable,
                            sentinel: None,
                        },
                    ));
                }
            }
            other => params.push((RegId(*local), mtype_to_ir(other))),
        }
    }
    for (ptr_pos, local, stride, mutable) in pending_slices {
        let len_pos = params.len() as u32;
        let len_reg = ctx.fresh();
        params.push((len_reg, Type::int(64)));
        ctx.slice_len.insert(local, len_reg);
        contracts.push((
            ptr_pos,
            PtrContract {
                assumption: None,
                refutable: true,
                size: SizeSpec::ParamElements { len_param: len_pos, elem_size: stride },
                align: stride as u32,
                readable: true,
                writable: mutable,
                sentinel: None,
            },
        ));
    }

    let mut blocks = Vec::new();
    for b in &body.blocks {
        blocks.push(ctx.lower_block(b)?);
    }
    // Prepend a protector retag for each `&mut` reference parameter to the entry block: the
    // parameter is its own root borrow (parent = itself → a root reborrow of the untracked owner).
    if let Some(entry) = blocks.first_mut() {
        for &local in mut_ref_locals.iter().rev() {
            entry.insts.insert(
                0,
                Inst::Intrinsic {
                    dst: None,
                    name: "csolver.retag.mut".into(),
                    args: vec![IrOp::Reg(RegId(local)), IrOp::Reg(RegId(local))],
                },
            );
        }
    }
    if ctx.lowering_failed {
        return Err(Error::unsupported("a memory access could not be lowered to a known pointer"));
    }
    if ctx.panic_used {
        // A diverging panic landing pad: an aborting check never returns, so the
        // continuation is unreachable for the purpose of memory safety.
        blocks.push(BasicBlock::new(BlockId(panic_id), Terminator::Unreachable));
    }

    let function = Function {
        id,
        name: body.name.clone(),
        params,
        ret_ty: mtype_to_ir(&body.ret),
        blocks,
        entry: BlockId(0),
    };
    Ok((function, contracts))
}


// --- module split (mechanical refactor) ---
mod helpers;
mod place;
mod stmt;
pub(crate) use helpers::*;
