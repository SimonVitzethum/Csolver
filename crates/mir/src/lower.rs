//! Lower a parsed MIR body into MSIR.
//!
//! The translation is deliberately conservative: a reference parameter of known
//! pointee size (`&[T; N]`, `&T`, `&mut T`) becomes a contracted region; the
//! bounds-check `assert` becomes a `CondBr` whose success edge carries the guard
//! (and whose failure edge goes to an `unreachable` panic block), so the checked
//! index `s[i]` is *proved* in bounds exactly because rustc inserted the check.
//! Anything outside the modelled subset (a `call`, an unmodelled rvalue/place)
//! is surfaced — the function is recorded unanalyzed rather than mis-lowered.

use crate::parser::{BinKind, MBlock, MConst, MStmt, MTerm, MType, MirBody, Operand, Place, Rvalue};
use csolver_core::{Error, Result};
use crate::parser::CalleeSpec;
use csolver_ir::{
    BasicBlock, BinOp, BlockId, Callee, CmpOp, Const, DataLayout, FuncId, Function, Inst, Module,
    Operand as IrOp, PtrContract, RValue, RefResult, RegId, SizeSpec, Terminator, Type,
};
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

struct Ctx {
    local_types: HashMap<u32, MType>,
    next_temp: u32,
    panic_id: u32,
    panic_used: bool,
    /// For a slice parameter `_k: &[T]`, the synthetic length parameter's
    /// register (so `Len((*_k))` resolves to it).
    slice_len: HashMap<u32, RegId>,
    /// Module function names → ids, for resolving direct calls.
    func_ids: HashMap<String, FuncId>,
    /// Set when a memory access cannot be lowered to a real pointer: the whole
    /// function is then rejected (reported `UNKNOWN`) rather than silently
    /// dropping the access — which would be an unsound vacuous `PASS`.
    lowering_failed: bool,
    /// For a checked-arithmetic tuple local `_k = AddWithOverflow(a, b)`, the
    /// arithmetic result `a + b` (its field `.0`), so `move (_k.0)` recovers it.
    checked_arith: HashMap<u32, IrOp>,
    /// Distinct field *paths* (`[0, 1]` for `((*p).0).1`) → a stable unique id, so
    /// a nested field gets its own FieldPtr `field` key (and thus its own disjoint
    /// synthetic offset) that never collides with a sibling or a top-level field.
    field_path_ids: HashMap<Vec<u32>, u32>,
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
    for (idx, (local, mty)) in body.params.iter().enumerate() {
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

impl Ctx {
    fn fresh(&mut self) -> RegId {
        let r = RegId(self.next_temp);
        self.next_temp += 1;
        r
    }

    /// A stable FieldPtr `field` id for a field path. A single-level path keeps its
    /// plain field index (so top-level field handling and round-trips are
    /// unchanged); a nested path gets a fresh id in the reserved high namespace, so
    /// each distinct path has its own disjoint synthetic offset.
    fn field_path_id(&mut self, path: &[u32]) -> u32 {
        if let [f] = path {
            return *f;
        }
        if let Some(&id) = self.field_path_ids.get(path) {
            return id;
        }
        let id = NESTED_FIELD_BASE + self.field_path_ids.len() as u32;
        self.field_path_ids.insert(path.to_vec(), id);
        id
    }

    fn lower_block(&mut self, b: &MBlock) -> Result<BasicBlock> {
        let mut insts = Vec::new();
        // Every instruction a statement emits inherits that statement's source
        // location (one MIR statement → possibly several MSIR insts, e.g. a
        // PtrOffset + a Load), so an obligation points back at the right line.
        let mut inst_spans: Vec<Option<String>> = Vec::new();
        for (s, span) in b.stmts.iter().zip(b.stmt_spans.iter()) {
            self.lower_stmt(s, &mut insts)?;
            inst_spans.resize(insts.len(), span.clone());
        }
        let term = self.lower_term(&b.term, &mut insts)?;
        inst_spans.resize(insts.len(), b.term_span.clone());
        let mut block = BasicBlock::new(BlockId(b.id as u32), term);
        block.insts = insts;
        block.inst_spans = inst_spans;
        Ok(block)
    }

    fn lower_stmt(&mut self, s: &MStmt, out: &mut Vec<Inst>) -> Result<()> {
        let MStmt::Assign(place, rv) = s else {
            return Ok(()); // Nop
        };
        match place {
            // Register destination: `_d = rvalue`.
            Place::Local(d) => {
                self.lower_rvalue_into(RegId(*d), rv, out)?;
                // A slice's length flows through pointer copies/borrows, so a
                // later `PtrMetadata`/`Len` of the copy still resolves to it
                // (rustc takes `_4 = &raw const (*_1); _5 = PtrMetadata(_4)`).
                self.propagate_slice_len(*d, rv);
                Ok(())
            }
            // Memory destination: `(*_p)[..] = …` / `*_p = …` / `(*_p).f = …`.
            // A *by-value* field write (`_3.0 = …`) is an opaque aggregate update
            // with no memory effect, so it is skipped soundly.
            Place::Deref(_) | Place::Index(_, _) | Place::ConstIndex(_, _) | Place::Field(_, _, _) => {
                if !is_memory_place(place) {
                    return Ok(());
                }
                let Rvalue::Use(op) = rv else {
                    // A non-`Use` store (e.g. a binop result written straight to
                    // memory) is rare in MIR; not modelled — skip soundly (the
                    // location keeps an unknown value).
                    return Ok(());
                };
                if let Some((ptr, elem)) = self.place_access(place, out) {
                    let value = self.operand_value(op, out);
                    out.push(Inst::Store {
                        ty: elem.clone(),
                        ptr: IrOp::Reg(ptr),
                        value,
                        align: elem.align_bytes(&LAYOUT).unwrap_or(1) as u32,
                    });
                }
                Ok(())
            }
        }
    }

    /// Lower an rvalue, writing its value into register `dst`.
    fn lower_rvalue_into(&mut self, dst: RegId, rv: &Rvalue, out: &mut Vec<Inst>) -> Result<()> {
        match rv {
            Rvalue::Use(op) => {
                // A memory operand (`copy (*_1)[_2]`) is a load.
                if let Operand::Copy(p) | Operand::Move(p) = op {
                    if is_memory_place(p) {
                        if let Some((ptr, elem)) = self.place_access(p, out) {
                            out.push(Inst::Load {
                                dst,
                                ty: elem.clone(),
                                ptr: IrOp::Reg(ptr),
                                align: elem.align_bytes(&LAYOUT).unwrap_or(1) as u32,
                            });
                        } else {
                            out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                        }
                        return Ok(());
                    }
                }
                let v = self.operand_value(op, out);
                out.push(assign(dst, RValue::Use(v)));
                Ok(())
            }
            Rvalue::Bin(kind, a, b) => {
                let av = self.operand_value(a, out);
                let bv = self.operand_value(b, out);
                let value = match bin_rvalue(*kind, av, bv) {
                    Some(rv) => rv,
                    None => RValue::Use(IrOp::Const(Const::Undef)),
                };
                out.push(assign(dst, value));
                Ok(())
            }
            // Checked arithmetic produces a `(result, overflow)` tuple. Compute
            // the result into a fresh register and remember it as the tuple's
            // `.0`, so a later `move (_k.0)` recovers the actual value (e.g. the
            // `n - 1` of a checked subtraction) — the `.1` overflow flag stays
            // opaque (it only feeds the overflow `assert`).
            Rvalue::CheckedBin(kind, a, b) => {
                let av = self.operand_value(a, out);
                let bv = self.operand_value(b, out);
                if let Some(rv) = bin_rvalue(*kind, av, bv) {
                    let tmp = self.fresh();
                    out.push(assign(tmp, rv));
                    self.checked_arith.insert(dst.0, IrOp::Reg(tmp));
                }
                Ok(())
            }
            Rvalue::Len(place) => {
                // `Len(&[T; N])` is the constant `N`; `Len(&[T])` is the slice's
                // synthetic length parameter.
                let value = if let Some(n) = self.array_len(place) {
                    IrOp::int(64, n as u128)
                } else if let Some(len) = place_base_local(place).and_then(|l| self.slice_len.get(&l))
                {
                    IrOp::Reg(*len)
                } else {
                    IrOp::Const(Const::Undef)
                };
                out.push(assign(dst, RValue::Use(value)));
                Ok(())
            }
            Rvalue::Ref(place) => {
                // `&(*_p)[i]` is the element address; `&(*_p)` is the pointer
                // itself; other refs (a stack local's address) are opaque.
                match place {
                    // `&(*_p)[i]` is the element address; `&((*_p).f)` /
                    // `&(((*_p) as V).f)` is a struct/enum-variant field address —
                    // both lower to the access pointer.
                    Place::Index(_, _) | Place::ConstIndex(_, _) => {
                        if let Some((ptr, _)) = self.place_access(place, out) {
                            out.push(assign(dst, RValue::Use(IrOp::Reg(ptr))));
                        } else {
                            out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                        }
                    }
                    Place::Field(_, _, _) if is_memory_place(place) => {
                        if let Some((ptr, _)) = self.place_access(place, out) {
                            out.push(assign(dst, RValue::Use(IrOp::Reg(ptr))));
                        } else {
                            out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                        }
                    }
                    Place::Deref(inner) => {
                        if let Place::Local(p) = inner.as_ref() {
                            out.push(assign(dst, RValue::Use(IrOp::Reg(RegId(*p)))));
                        } else {
                            out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                        }
                    }
                    _ => out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef)))),
                }
                Ok(())
            }
            // A cast keeps the value (width changes are abstracted); an unmodelled
            // rvalue yields a fresh unknown.
            Rvalue::Cast(op) => {
                let v = self.operand_value(op, out);
                out.push(assign(dst, RValue::Use(v)));
                Ok(())
            }
            Rvalue::Discriminant(place) => {
                // The discriminant value is opaque (so a following `switchInt`
                // soundly explores every arm), but reading it through a pointer is
                // a real memory access: emit a one-byte read at the base of the
                // enum so an invalid enum reference is caught (in bounds by
                // construction, like a field). A by-value enum needs no access.
                if is_memory_place(place) {
                    if let Some(p) = place_base_local(place) {
                        let ptr = self.fresh();
                        out.push(Inst::FieldPtr {
                            dst: ptr,
                            base: IrOp::Reg(RegId(p)),
                            field: 0,
                            size: 1,
                            align: 1,
                        });
                        let val = self.fresh();
                        out.push(Inst::Load {
                            dst: val,
                            ty: Type::int(8),
                            ptr: IrOp::Reg(ptr),
                            align: 1,
                        });
                    }
                }
                out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                Ok(())
            }
            Rvalue::Other => {
                out.push(assign(dst, RValue::Use(IrOp::Const(Const::Undef))));
                Ok(())
            }
        }
    }

    /// The terminator after a call/drop, given its normal-return and
    /// unwind-cleanup targets. Both present → a two-way branch on a *fresh
    /// unconstrained* condition, so both the normal successor and the cleanup
    /// block are explored (the cleanup runs on the panic path; its memory ops —
    /// drops and writes — must be checked, not silently left undecided). The
    /// cleanup edge sees the post-call state (the call's conservative havoc), a
    /// sound over-approximation of the partially-unwound state. Mirrors the LLVM
    /// `invoke` lowering.
    fn call_edges(&mut self, target: Option<usize>, unwind: Option<usize>) -> Terminator {
        match (target, unwind) {
            (Some(t), Some(u)) => Terminator::CondBr {
                cond: IrOp::Reg(self.fresh()),
                then_blk: BlockId(t as u32),
                then_args: vec![],
                else_blk: BlockId(u as u32),
                else_args: vec![],
            },
            (Some(t), None) => Terminator::Br { target: BlockId(t as u32), args: vec![] },
            (None, Some(u)) => Terminator::Br { target: BlockId(u as u32), args: vec![] },
            (None, None) => Terminator::Unreachable,
        }
    }

    fn lower_term(&mut self, t: &MTerm, out: &mut Vec<Inst>) -> Result<Terminator> {
        Ok(match t {
            MTerm::Return => Terminator::Return(None),
            MTerm::Goto(n) => Terminator::Br { target: BlockId(*n as u32), args: vec![] },
            MTerm::Unreachable => Terminator::Unreachable,
            MTerm::Assert { cond, expected, target } => {
                self.panic_used = true;
                let c = self.operand_value(cond, out);
                let cont = BlockId(*target as u32);
                let panic = BlockId(self.panic_id);
                let (then_blk, else_blk) = if *expected { (cont, panic) } else { (panic, cont) };
                Terminator::CondBr {
                    cond: c,
                    then_blk,
                    then_args: vec![],
                    else_blk,
                    else_args: vec![],
                }
            }
            MTerm::Call { dst, callee, args, target, unwind } => {
                // A call is an MSIR *instruction* followed by an edge to the
                // return block (or divergence if the call cannot return). The
                // verifier applies a known function's summary or havocs an
                // unknown/external one — both sound.
                let ir_dst = match dst {
                    Place::Local(d) => Some(RegId(*d)),
                    _ => None,
                };
                let ir_callee = match callee {
                    CalleeSpec::Named(n) if !n.is_empty() => match self.func_ids.get(n) {
                        Some(fid) => Callee::Direct(*fid),
                        None => Callee::Symbol(n.clone()),
                    },
                    CalleeSpec::Named(_) => Callee::Symbol(String::new()),
                    CalleeSpec::Indirect(local) => Callee::Indirect(IrOp::Reg(RegId(*local))),
                };
                let ir_args = args.iter().map(|a| self.operand_value(a, out)).collect();
                // The result type is the destination local's declared type — so a
                // call returning a reference (`Index::index` → `&T`, an internal fn
                // returning `&_`) yields a *pointer*, not a scalar the engine would
                // have to treat as an opaque address. A non-`Local` dst keeps the
                // scalar default (its value is unused for memory reasoning).
                let ret_ty = match dst {
                    Place::Local(d) => {
                        self.local_types.get(d).map(mtype_to_ir).unwrap_or_else(|| Type::int(64))
                    }
                    _ => Type::int(64),
                };
                // A call returning `&T`/`&mut T` yields a *valid reference* by
                // Rust's type invariant (the callee — even external — cannot
                // return a dangling reference in safe code). Absent a precise
                // summary, the engine materialises it as a valid-reference
                // region instead of an opaque pointer. Raw pointers are excluded
                // (not guaranteed valid).
                let ret_ref = match dst {
                    Place::Local(d) => match self.local_types.get(d) {
                        Some(MType::Ref(inner, mutable)) => Some(RefResult {
                            size: pointee_size(inner),
                            writable: *mutable,
                        }),
                        _ => None,
                    },
                    _ => None,
                };
                out.push(Inst::Call {
                    dst: ir_dst,
                    callee: ir_callee,
                    args: ir_args,
                    ret_ty,
                    ret_ref,
                });
                self.call_edges(*target, *unwind)
            }
            MTerm::SwitchInt(op, cases, otherwise) => {
                let value = self.operand_value(op, out);
                // A two-way `[0: f, otherwise: t]` is a boolean branch.
                if let [(0, false_bb)] = cases[..] {
                    Terminator::CondBr {
                        cond: value,
                        then_blk: BlockId(*otherwise as u32),
                        then_args: vec![],
                        else_blk: BlockId(false_bb as u32),
                        else_args: vec![],
                    }
                } else {
                    let cases = cases
                        .iter()
                        .map(|(v, bb)| {
                            (csolver_core::BitVector::new(64, *v as u128), BlockId(*bb as u32))
                        })
                        .collect();
                    Terminator::Switch { value, cases, default: BlockId(*otherwise as u32) }
                }
            }
            MTerm::Drop { target, unwind } => {
                // A drop runs the value's destructor, which may free what the value
                // owns (a `Vec`/`Box` buffer, or a raw pointer a custom `Drop`
                // frees). Model it as a freeing call: an unknown `Symbol` callee,
                // which the verifier treats as possibly-freeing — it invalidates
                // every owned region's liveness and the heap, so a later use of a
                // freed owned region is not a false PASS. Borrowed (contracted)
                // regions survive, since a destructor cannot free a borrow. Then
                // branch to the return block.
                out.push(Inst::Call {
                    dst: None,
                    callee: Callee::Symbol("drop".into()),
                    args: vec![],
                    ret_ty: Type::Unit,
                    ret_ref: None,
                });
                self.call_edges(*target, *unwind)
            }
            MTerm::Unsupported => {
                return Err(Error::unsupported("MIR terminator outside the modelled subset"))
            }
        })
    }

    /// Materialise an operand as an MSIR scalar operand (loading a memory place
    /// into a fresh register if needed).
    /// If `p` is a *by-value* field projection whose innermost ascribed type is
    /// a reference (`&T`/`&mut T` — e.g. `(_6 as Some).0` of type `&u8`,
    /// extracted from an aggregate the analysis cannot see into), materialise it
    /// as a valid reference: Rust guarantees the value is a live, correctly-sized
    /// reference regardless of where the aggregate came from. Returns the
    /// pointer register, or `None` (the caller falls back to `undef`) for a
    /// non-reference field or a raw-pointer field (`*const T` is not guaranteed
    /// valid). A slice/unsized pointee has unknown size → an opaque region.
    fn ref_witness_for(&mut self, p: &Place, out: &mut Vec<Inst>) -> Option<IrOp> {
        if is_memory_place(p) {
            return None; // a field *through a pointer* is a real load, not this.
        }
        let Place::Field(_, _, Some(MType::Ref(inner, mutable))) = p else {
            return None;
        };
        let (size, align) = match pointee_size(inner) {
            Some(n) => (Some(n), pointee_align(inner)),
            None => (None, 1),
        };
        let dst = self.fresh();
        out.push(Inst::RefWitness { dst, size, align, writable: *mutable });
        Some(IrOp::Reg(dst))
    }

    fn operand_value(&mut self, op: &Operand, out: &mut Vec<Inst>) -> IrOp {
        match op {
            Operand::Const(MConst::Int(n)) => IrOp::int(64, *n as u128),
            Operand::Const(MConst::Bool(b)) => IrOp::int(1, *b as u128),
            Operand::Copy(p) | Operand::Move(p) => match p {
                Place::Local(n) => IrOp::Reg(RegId(*n)),
                // Field `.0` of a checked-arithmetic tuple (a by-value local) is
                // its result value. A field *through a pointer* (`(*_1).0`) is a
                // memory place and is loaded by the arm below instead.
                Place::Field(inner, 0, _) if matches!(inner.as_ref(), Place::Local(_)) => {
                    match inner.as_ref() {
                        Place::Local(k) => self.checked_arith.get(k).cloned().unwrap_or_else(|| {
                            // `.0` of a by-value fat pointer (`&[T]`) is its data
                            // pointer — which CSolver already models as the region
                            // pointer held in `_k`. Read it back (keeping the
                            // contracted region's provenance) instead of dropping it
                            // to undef.
                            if self.is_fat_ref(*k) {
                                IrOp::Reg(RegId(*k))
                            } else {
                                self.ref_witness_for(p, out)
                                    .unwrap_or(IrOp::Const(Const::Undef))
                            }
                        }),
                        _ => IrOp::Const(Const::Undef),
                    }
                }
                _ if is_memory_place(p) => {
                    if let Some((ptr, elem)) = self.place_access(p, out) {
                        let dst = self.fresh();
                        out.push(Inst::Load {
                            dst,
                            ty: elem.clone(),
                            ptr: IrOp::Reg(ptr),
                            align: elem.align_bytes(&LAYOUT).unwrap_or(1) as u32,
                        });
                        IrOp::Reg(dst)
                    } else {
                        IrOp::Const(Const::Undef)
                    }
                }
                _ => self.ref_witness_for(p, out).unwrap_or(IrOp::Const(Const::Undef)),
            },
        }
    }

    /// Emit the pointer to a memory `place` and return `(pointer reg, elem type)`.
    /// Resolve the base pointer and element type for an index projection
    /// `base[..]` — shared by the runtime-`Index` and constant-`ConstIndex`
    /// arms. `base` is either `*_p` (the array/slice behind a pointer) or an
    /// outer index/field yielding a pointer-to-array.
    fn index_base(&mut self, base: &Place, out: &mut Vec<Inst>) -> Option<(IrOp, Type)> {
        match base {
            Place::Deref(inner) => match inner.as_ref() {
                Place::Local(p) => {
                    Some((IrOp::Reg(RegId(*p)), self.index_elem(*p).unwrap_or_else(|| Type::int(8))))
                }
                _ => {
                    self.lowering_failed = true;
                    None
                }
            },
            Place::Index(_, _) | Place::ConstIndex(_, _) | Place::Field(_, _, _) => {
                let (inner_ptr, inner_ty) = self.place_access(base, out)?;
                match array_elem(&inner_ty) {
                    Some(elem) => Some((IrOp::Reg(inner_ptr), elem)),
                    None => {
                        self.lowering_failed = true;
                        None
                    }
                }
            }
            _ => {
                self.lowering_failed = true;
                None
            }
        }
    }

    fn place_access(&mut self, place: &Place, out: &mut Vec<Inst>) -> Option<(RegId, Type)> {
        match place {
            // `base[i]`: a pointer to element 0 of the array/slice `base` denotes,
            // offset by `i` (stride = element size). `base` is either `*_p` (the
            // slice/array behind a pointer) or an *outer* index, so nested indices
            // `(*_p)[i][j]` chain — the inner index yields a pointer to an inner
            // array, which this level indexes again. The strides come from the
            // array element types, which are unambiguous (no struct-layout needed).
            Place::Index(base, idx) => {
                let (base_ptr, elem) = self.index_base(base, out)?;
                let dst = self.fresh();
                out.push(Inst::PtrOffset {
                    dst,
                    base: base_ptr,
                    index: IrOp::Reg(RegId(*idx)),
                    elem: elem.clone(),
                });
                Some((dst, elem))
            }
            // `base[N of M]` — a constant element index (same base resolution as
            // `Index`, but the offset is the compile-time constant `N`).
            Place::ConstIndex(base, n) => {
                let (base_ptr, elem) = self.index_base(base, out)?;
                let dst = self.fresh();
                out.push(Inst::PtrOffset {
                    dst,
                    base: base_ptr,
                    index: IrOp::int(64, *n as u128),
                    elem: elem.clone(),
                });
                Some((dst, elem))
            }
            // `*_p`: the pointer is `_p`; the access is at offset 0.
            Place::Deref(inner) => match inner.as_ref() {
                Place::Local(p) => {
                    let elem = self.deref_elem(*p).unwrap_or_else(|| Type::int(8));
                    Some((RegId(*p), elem))
                }
                _ => {
                    self.lowering_failed = true;
                    None
                }
            },
            // `(*_p).f`: a field of the struct behind pointer `_p`. The field's
            // type (from the MIR ascription) gives its size and alignment; the
            // engine proves the access in bounds by construction, so no struct
            // byte-layout is needed (it is absent from MIR anyway).
            // `(*p).f` and nested `((*p).f0).f1` both denote a field that lies
            // within the referent of `p` by construction. Walk the whole field
            // path down to a `Deref(Local p)` base and emit one FieldPtr keyed on a
            // unique id for that path, so a nested field gets its own disjoint
            // synthetic offset — in bounds and aligned by construction, and never
            // aliasing a sibling or top-level field. The innermost field's type
            // ascription gives its size and alignment.
            Place::Field(_, _, fty) => {
                if let Some((p, path)) = deref_field_path(place) {
                    let elem = fty.as_ref().map(mtype_to_ir).unwrap_or_else(|| Type::int(8));
                    let size = elem.size_bytes(&LAYOUT).unwrap_or(1).max(1);
                    let align = elem.align_bytes(&LAYOUT).unwrap_or(1).max(1);
                    let id = self.field_path_id(&path);
                    let dst = self.fresh();
                    out.push(Inst::FieldPtr {
                        dst,
                        base: IrOp::Reg(RegId(p)),
                        field: id,
                        size,
                        align,
                    });
                    Some((dst, elem))
                } else {
                    self.lowering_failed = true;
                    None
                }
            }
            _ => {
                self.lowering_failed = true;
                None
            }
        }
    }

    /// Carry a slice's synthetic length to `dst` when the rvalue copies or
    /// borrows a slice pointer (`dst = move _p`, `dst = &(*_p)`, a pointer cast).
    fn propagate_slice_len(&mut self, dst: u32, rv: &Rvalue) {
        let src = match rv {
            Rvalue::Use(Operand::Copy(Place::Local(p)) | Operand::Move(Place::Local(p)))
            | Rvalue::Cast(Operand::Copy(Place::Local(p)) | Operand::Move(Place::Local(p))) => Some(*p),
            Rvalue::Ref(Place::Deref(inner)) => match inner.as_ref() {
                Place::Local(p) => Some(*p),
                _ => None,
            },
            _ => None,
        };
        if let Some(len) = src.and_then(|p| self.slice_len.get(&p).copied()) {
            self.slice_len.insert(dst, len);
        }
    }

    /// The element type for indexing through local `p` (an `&[T; N]`/`&[T]`).
    fn index_elem(&self, p: u32) -> Option<Type> {
        match self.local_types.get(&p)? {
            MType::Ref(inner, _) | MType::Ptr(inner, _) => match inner.as_ref() {
                MType::Array(e, _) | MType::Slice(e) => Some(mtype_to_ir(e)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether local `p` is a fat-pointer reference (`&[T]`/`&mut [T]`) — so its
    /// `.0` projection is a data pointer into a contracted region, not opaque.
    fn is_fat_ref(&self, p: u32) -> bool {
        matches!(
            self.local_types.get(&p),
            Some(MType::Ref(inner, _) | MType::Ptr(inner, _)) if matches!(inner.as_ref(), MType::Slice(_))
        )
    }

    /// The pointee type for dereferencing local `p` (an `&T`/`*T`).
    fn deref_elem(&self, p: u32) -> Option<Type> {
        match self.local_types.get(&p)? {
            MType::Ref(inner, _) | MType::Ptr(inner, _) => Some(mtype_to_ir(inner)),
            _ => None,
        }
    }

    /// The constant length `N` of the array `place` refers to (`&[T; N]`).
    fn array_len(&self, place: &Place) -> Option<u64> {
        let local = match place {
            Place::Deref(inner) => match inner.as_ref() {
                Place::Local(p) => *p,
                _ => return None,
            },
            Place::Local(p) => *p,
            _ => return None,
        };
        match self.local_types.get(&local)? {
            MType::Ref(inner, _) | MType::Ptr(inner, _) => match inner.as_ref() {
                MType::Array(_, n) => Some(*n),
                _ => None,
            },
            MType::Array(_, n) => Some(*n),
            _ => None,
        }
    }
}

fn assign(dst: RegId, value: RValue) -> Inst {
    Inst::Assign { dst, ty: Type::int(64), value }
}

/// Map a MIR binary op to an MSIR rvalue (`None` ⇒ unmodelled, opaque result).
/// Comparisons are unsigned — the index/length bounds checks that motivate the
/// MIR frontend are over `usize`.
fn bin_rvalue(kind: BinKind, lhs: IrOp, rhs: IrOp) -> Option<RValue> {
    let cmp = |op| Some(RValue::Cmp { op, lhs: lhs.clone(), rhs: rhs.clone() });
    let bin = |op| Some(RValue::Bin { op, lhs: lhs.clone(), rhs: rhs.clone() });
    match kind {
        BinKind::Lt => cmp(CmpOp::Ult),
        BinKind::Le => cmp(CmpOp::Ule),
        BinKind::Gt => cmp(CmpOp::Ugt),
        BinKind::Ge => cmp(CmpOp::Uge),
        BinKind::Eq => cmp(CmpOp::Eq),
        BinKind::Ne => cmp(CmpOp::Ne),
        BinKind::Add => bin(BinOp::Add),
        BinKind::Sub => bin(BinOp::Sub),
        BinKind::Mul => bin(BinOp::Mul),
        BinKind::BitAnd => bin(BinOp::And),
        BinKind::BitOr => bin(BinOp::Or),
        BinKind::BitXor => bin(BinOp::Xor),
        BinKind::Other => None,
    }
}

/// Whether a place denotes a memory access — its projection chain reaches a
/// deref or index. A field of a plain local (`_11.0`, a tuple value) is *not*
/// memory; a field reached through a pointer (`(*_1).0`) *is* (and, lacking
/// struct layout, is rejected rather than silently dropped).
fn is_memory_place(p: &Place) -> bool {
    match p {
        Place::Local(_) => false,
        Place::Deref(_) => true,
        // An index/field is a memory access only if its base ultimately derefs a
        // pointer: `(*_p)[i]` and `(*_p).f[i]` are memory, but indexing a by-value
        // local array (`_l[i]`, `_l.0[i]`) is a bounds-checked stack value, not a
        // heap access — modelled opaquely, with no memory obligation.
        Place::ConstIndex(base, _) | Place::Index(base, _) | Place::Field(base, _, _) => {
            is_memory_place(base)
        }
    }
}

/// The local a place is rooted at, peeling every projection.
fn place_base_local(p: &Place) -> Option<u32> {
    match p {
        Place::Local(n) => Some(*n),
        Place::Deref(inner)
        | Place::Field(inner, _, _)
        | Place::Index(inner, _)
        | Place::ConstIndex(inner, _) => place_base_local(inner),
    }
}

/// The locals a block mentions (params plus any `_N` in index/assign positions),
/// used only to size the temporary-register counter.
fn block_locals(b: &MBlock) -> Vec<u32> {
    let mut out = Vec::new();
    let visit_place = |p: &Place, out: &mut Vec<u32>| {
        let mut cur = p;
        loop {
            match cur {
                Place::Local(n) => {
                    out.push(*n);
                    break;
                }
                Place::Deref(inner) | Place::Field(inner, _, _) | Place::ConstIndex(inner, _) => {
                    cur = inner
                }
                Place::Index(inner, idx) => {
                    out.push(*idx);
                    cur = inner;
                }
            }
        }
    };
    for s in &b.stmts {
        if let MStmt::Assign(p, _) = s {
            visit_place(p, &mut out);
        }
    }
    out
}

/// Convert a MIR type to an MSIR type.
/// Walk a (possibly nested) field place down to a `(*_p)` base, returning the
/// pointer local and the field path, outer-to-inner (`[0, 1]` for `((*p).0).1`).
/// `None` if the base is not a deref of a local — a field of a by-value local, or
/// through an index, has no single pointer to offset from.
fn deref_field_path(place: &Place) -> Option<(u32, Vec<u32>)> {
    let mut fields = Vec::new();
    let mut cur = place;
    loop {
        match cur {
            Place::Field(base, f, _) => {
                fields.push(*f);
                cur = base;
            }
            Place::Deref(inner) => {
                return match inner.as_ref() {
                    Place::Local(p) => {
                        fields.reverse();
                        Some((*p, fields))
                    }
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// The element type of an array `Type`, for chaining a nested index.
fn array_elem(ty: &Type) -> Option<Type> {
    match ty {
        Type::Array { elem, .. } => Some((**elem).clone()),
        _ => None,
    }
}

fn mtype_to_ir(mty: &MType) -> Type {
    match mty {
        MType::Int { width, .. } => Type::int(*width),
        MType::Bool => Type::Bool,
        MType::Unit | MType::Other => Type::Unit,
        MType::Ref(inner, _) | MType::Ptr(inner, _) => Type::ptr(mtype_to_ir(inner)),
        MType::Array(elem, n) => Type::Array { elem: Box::new(mtype_to_ir(elem)), len: *n },
        // A bare slice is never a value type here; only its element is used.
        MType::Slice(elem) => mtype_to_ir(elem),
    }
}

/// The byte size of a reference's pointee, when statically known.
fn pointee_size(pointee: &MType) -> Option<u64> {
    mtype_to_ir(pointee).size_bytes(&LAYOUT).filter(|&s| s > 0)
}

fn pointee_align(pointee: &MType) -> u32 {
    mtype_to_ir(pointee).align_bytes(&LAYOUT).unwrap_or(1) as u32
}
