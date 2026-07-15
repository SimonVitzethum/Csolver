//! Blocks, terminators, functions and modules.

use crate::id::{BlockId, FuncId, RegId};
use crate::inst::{Callee, Inst, Operand};
use crate::ty::{DataLayout, Type};
use csolver_core::BitVector;
use std::collections::HashMap;

/// How a [`BasicBlock`] transfers control. Branch targets carry argument lists
/// that bind the destination block's parameters (the block-argument SSA form).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    /// Return, optionally with a value.
    Return(Option<Operand>),
    /// Unconditional branch.
    Br {
        /// Target block.
        target: BlockId,
        /// Arguments binding the target's parameters.
        args: Vec<Operand>,
    },
    /// Two-way conditional branch on an `i1`.
    CondBr {
        /// The boolean condition.
        cond: Operand,
        /// Taken-if-true block.
        then_blk: BlockId,
        /// Arguments for the true target.
        then_args: Vec<Operand>,
        /// Taken-if-false block.
        else_blk: BlockId,
        /// Arguments for the false target.
        else_args: Vec<Operand>,
    },
    /// Multi-way branch on an integer value.
    Switch {
        /// The scrutinee.
        value: Operand,
        /// `(case value, target)` pairs (targets take no arguments here).
        cases: Vec<(BitVector, BlockId)>,
        /// The default target.
        default: BlockId,
    },
    /// Control cannot reach here. If it provably can, that is itself a bug the
    /// verifier reports.
    Unreachable,
}

impl Terminator {
    /// The successor blocks of this terminator, in a stable order.
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Terminator::Return(_) | Terminator::Unreachable => Vec::new(),
            Terminator::Br { target, .. } => vec![*target],
            Terminator::CondBr {
                then_blk, else_blk, ..
            } => vec![*then_blk, *else_blk],
            Terminator::Switch { cases, default, .. } => {
                let mut v: Vec<BlockId> = cases.iter().map(|(_, b)| *b).collect();
                v.push(*default);
                v
            }
        }
    }
}

/// A basic block: parameters, a straight-line instruction sequence, and a
/// terminator. There are no intra-block branches by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    /// This block's id.
    pub id: BlockId,
    /// SSA parameters bound by incoming branch arguments (PHI replacement).
    pub params: Vec<(RegId, Type)>,
    /// The body.
    pub insts: Vec<Inst>,
    /// Optional source location (`FILE:LINE:COL`) per instruction, parallel to
    /// `insts` when populated (the MIR frontend with span info); empty otherwise.
    /// A frontend-agnostic carrier: the verifier renders it on each obligation, so
    /// a later DWARF populator (for ELF) feeds the same field. Empty ⇒ no source
    /// pointer, the sound default.
    pub inst_spans: Vec<Option<String>>,
    /// The control-flow exit.
    pub term: Terminator,
}

impl BasicBlock {
    /// A new, empty block ending in `term`.
    pub fn new(id: BlockId, term: Terminator) -> Self {
        BasicBlock {
            id,
            params: Vec::new(),
            insts: Vec::new(),
            inst_spans: Vec::new(),
            term,
        }
    }

    /// The successor blocks (delegates to the terminator).
    pub fn successors(&self) -> Vec<BlockId> {
        self.term.successors()
    }
}

/// A function: a CFG of basic blocks with a designated entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    /// This function's id.
    pub id: FuncId,
    /// Its (mangled or symbolic) name.
    pub name: String,
    /// Parameter registers and types.
    pub params: Vec<(RegId, Type)>,
    /// Return type.
    pub ret_ty: Type,
    /// The blocks, indexed by [`BasicBlock::id`] (not necessarily by position).
    pub blocks: Vec<BasicBlock>,
    /// The entry block.
    pub entry: BlockId,
}

impl Function {
    /// Look up a block by id.
    ///
    /// Fast path: every frontend materialises blocks in id order, so position
    /// `id` almost always *is* the block — checked in O(1) before falling back
    /// to the linear scan the (public) `blocks` field's freedom requires. This
    /// keeps the hot per-lookup cost constant without a cache field that every
    /// struct-literal construction site would have to initialise.
    pub fn block(&self, id: BlockId) -> Option<&BasicBlock> {
        match self.blocks.get(id.index()) {
            Some(b) if b.id == id => Some(b),
            _ => self.blocks.iter().find(|b| b.id == id),
        }
    }

    /// Mutable access to the block with the given id (for MSIR→MSIR passes).
    pub fn block_mut(&mut self, id: BlockId) -> Option<&mut BasicBlock> {
        // Mirrors `block`'s positional fast path. (The borrow is re-taken for
        // the fallback — NLL rejects holding the probe across it.)
        if matches!(self.blocks.get(id.index()), Some(b) if b.id == id) {
            return self.blocks.get_mut(id.index());
        }
        self.blocks.iter_mut().find(|b| b.id == id)
    }

    /// The number of blocks.
    pub fn block_count(&self) -> usize {
        self.blocks.len()
    }
}

/// How big a pointer parameter's valid region is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SizeSpec {
    /// A fixed byte count (from `dereferenceable(N)`).
    Bytes(u64),
    /// `parameter[len_param] * elem_size` bytes — a Rust slice `&[T]`, lowered
    /// as a `(ptr, usize len)` pair.
    ParamElements {
        /// Index of the `usize` length parameter.
        len_param: u32,
        /// Size in bytes of one element.
        elem_size: u64,
    },
    /// A statically-unknown size — an aggregate (`&Struct`/`&mut Struct`) whose
    /// layout is absent from the source IR. Modelled as a fresh symbolic size; a
    /// field access through it is proved in bounds by construction (the field lies
    /// within the aggregate), never by a reconstructed byte offset.
    Opaque,
    /// **Non-null only** — the pointer is guaranteed non-null (an LLVM `nonnull`
    /// parameter attribute: Zig `*T`, and any frontend that asserts it) but carries
    /// *no* size or liveness guarantee (a `nonnull` pointer may still dangle or be
    /// out of bounds). Modelled as a non-null **opaque** pointer, NOT a region: only
    /// `NoNullDeref` is discharged through it; bounds/liveness stay `UNKNOWN` (sound —
    /// no false PASS, since `nonnull` promises nothing spatial or temporal).
    NonNull,
}

/// A caller-guaranteed contract on a pointer parameter (from a frontend, e.g.
/// LLVM's `dereferenceable(N)` / `align` / `readonly` / `writeonly`, or the
/// `(ptr, len)` slice ABI — which `rustc` emits/implies from the Rust reference
/// type).
///
/// When verifying the function in isolation, the contract is *assumed*: the
/// parameter is modelled as a live region of the given size with the given
/// alignment and permissions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtrContract {
    /// The size of the valid region.
    pub size: SizeSpec,
    /// Guaranteed alignment of the pointer (1 if unspecified).
    pub align: u32,
    /// Whether the pointee is readable (false for `writeonly`).
    pub readable: bool,
    /// Whether the pointee is writable (false for `readonly`).
    pub writable: bool,
    /// Overrides the assumption id a proof resting on this contract surfaces
    /// (`None` = the id implied by `size`, e.g. `param-contracts`). Synthesized
    /// contracts (derived rather than declared) must name their own trust basis.
    pub assumption: Option<&'static str>,
    /// Whether a violation against this contract's size may be *refuted* (a
    /// definite FAIL with a witness). True for the declared contract of an
    /// externally-callable function — any safe caller can realize the witness.
    /// **False when the contract is a caller-established precondition** (an
    /// internal function or closure: the guard lives at the call sites, so a
    /// witness picked freely from the parameter space may be infeasible in the
    /// real program — refuting there is a false FAIL). Prove-only contracts
    /// still prove; they never refute.
    pub refutable: bool,
    /// If `Some(elem_bytes)`, the region is **sentinel-terminated**: it contains a
    /// zero element of `elem_bytes` bytes at some index before its end (a C string
    /// is `Some(1)`). A sequential scan `while (p[n] != 0) n++` over it is then
    /// bounded — it must stop at that sentinel — which is what makes a `strlen`-
    /// shaped loop provable. Language-agnostic: any "scan until a zero terminator"
    /// buffer. `None` for an ordinary region.
    pub sentinel: Option<u64>,
}

/// A contract on a *field* of a contracted pointer parameter: the pointer
/// stored at **byte offset `offset`** behind the parameter points to a live
/// region described by `pointee`. Synthesized interprocedurally — a raw pointer
/// member carries no such guarantee from its type, only from the fact that every
/// (visible) call site provably stores a valid pointer there. Keyed by byte
/// offset (not field index) because the frontends address struct fields with
/// byte `PtrOffset`s, so caller store and callee load line up on the offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldContract {
    /// Byte offset of the pointer field within the parameter's aggregate.
    pub offset: u64,
    /// What the loaded field pointer points to (size, alignment, permissions).
    pub pointee: PtrContract,
}

/// A module: a collection of functions plus the target data layout.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    /// Module name (e.g. crate or object name).
    pub name: String,
    /// The functions.
    pub functions: Vec<Function>,
    /// Target sizes/alignments used by all layout queries.
    pub layout: DataLayout,
    /// Contracts on pointer parameters, keyed by `(function, parameter index)`.
    pub param_contracts: HashMap<(FuncId, u32), PtrContract>,
    /// Functions a frontend could not lower (e.g. unsupported constructs), as
    /// `(name, reason)`. They are reported as `UNKNOWN` so the module verdict
    /// reflects that they were not verified — never a silent omission.
    pub unanalyzed: Vec<(String, String)>,
    /// Functions with *internal linkage*: not visible outside this module, so
    /// the module's direct call sites are provably **all** their call sites
    /// (unless the address is taken). This is what licenses synthesizing a
    /// parameter contract from the call sites. Frontends without linkage
    /// information leave it empty — the sound default.
    pub internal: std::collections::HashSet<FuncId>,
    /// Global/static definitions by symbol name. A `Const::Symbol` referring to
    /// one is a pointer to a region of the given size that lives for the whole
    /// program (never freed). Frontends without global information leave it
    /// empty — such symbols stay opaque scalars, the sound default.
    pub globals: HashMap<String, GlobalDef>,
    /// Optional `(pointee byte size, align)` for a **raw** pointer parameter, keyed
    /// by `(function, parameter index)`, recovered from debug info. NOT a contract on
    /// its own (a raw pointer may dangle) — only applied when the caller opts into the
    /// "the framework passes a valid pointer" assumption (`Config::assume_valid_params`),
    /// where it becomes a prove-only contract under the `param-valid` assumption.
    pub raw_ptr_hints: HashMap<(FuncId, u32), (u64, u32)>,
    /// The **provenance lattice**: which capability ids each provenance-label id grants
    /// (from external contracts, `prov <label> grants=…`). An [`Inst::ProvLabel`] tags a
    /// region with a label id; an [`Inst::CapRequire`] checks this map. A label absent
    /// here (or an unlabelled region) grants **everything** — the sound default, so the
    /// capability mechanism never introduces a false FAIL on code that names no labels.
    pub prov_grants: HashMap<u32, std::collections::HashSet<u32>>,
    /// **Constant symbol-pointer tables** for indirect-call devirtualisation:
    /// global symbol name → `(byte offset, target function)` for each function
    /// pointer stored in that global's constant initializer (an ops-struct /
    /// vtable). A load of such a field, at a matching concrete offset from the
    /// global's region, resolves the loaded function pointer to `FuncId` — so an
    /// indirect call through it is analysed with the callee's summary instead of
    /// an opaque havoc. Only external references that resolve to a defined
    /// function are kept; the rest stay opaque (sound).
    pub global_fn_ptrs: HashMap<String, Vec<(u64, FuncId)>>,
    /// **Pointee byte size of a register**, recovered from the struct type of the `gep` that
    /// indexes it: a `getelementptr %struct.T, ptr %r, …` proves `%r` designates a `%struct.T`,
    /// so `sizeof(%struct.T)` bounds every access through `%r`. Keyed by `(function, register)`.
    ///
    /// Used to give a **loop-carried pointer** a size: at a loop header a moving iterator
    /// (`iter = iter->next`) is havoc'd and would otherwise become an *unsized* region, leaving
    /// its `in_bounds` obligations UNKNOWN. Consulted only under `--assume-valid-loop-ptrs`
    /// (which already assumes the iterator designates a valid live object); the type then says
    /// how big that object is. Empty for frontends that carry no type information — the sound
    /// default (the region stays unsized).
    pub reg_ptr_hints: HashMap<(FuncId, RegId), PtrHint>,
    /// Functions registered as a **memory-mapped-I/O dispatch handler** — the `.read`/`.write`
    /// of a `MemoryRegionOps` passed to `memory_region_init_io(mr, owner, ops, opaque, name,
    /// size)`. Such a handler is *only* ever called by the memory core's dispatch, which
    /// guarantees `size ∈ {1,2,4,8}` and `addr + size ≤ region_size`. The value is the region
    /// byte size when the init call passed a constant (`Some`), else `None` (size-arg only).
    ///
    /// These are genuine guarantees of how the handler is invoked, not assumptions — modelling
    /// them is precision. Without them, treating a handler as an entry point (via
    /// `--auto-entries`) with a free `addr`/`size` refutes on a register offset or access size
    /// the dispatch never produces (a false FAIL). Keyed by handler `FuncId`.
    ///
    /// Keyed by handler **name** (not `FuncId`) so it survives cross-file linking: a device's
    /// ops global may name a handler (`register_read_memory`) that is *defined in another file*
    /// (`hw/core/register.c`), and registration wrappers like `register_init_block32` pass the
    /// ops through. The name is recovered from the ops global's initialiser regardless of where
    /// the handler is defined; the verifier resolves it against the function being analysed.
    pub mmio_handlers: HashMap<String, MmioHandler>,
}

/// What the frontend recovered about a memory-mapped-I/O dispatch handler (see
/// [`Module::mmio_handlers`]). The address is always parameter 1; the access size is at
/// `size_param` (2 for a plain `.read`/`.write`, 3 for a `.read_with_attrs`/`.write_with_attrs`,
/// which take a data pointer/value at parameter 2). `region_size` is the mapped byte size when
/// the `memory_region_init_io` call passed a constant, else `None`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MmioHandler {
    /// Mapped region byte size, when the init call passed a constant.
    pub region_size: Option<u64>,
    /// Parameter index of the `unsigned size` access-size argument.
    pub size_param: u32,
}

/// What a frontend recovered about the object a register points at: its byte size and,
/// when debug info records it, the **declared alignment of the pointee type**.
///
/// The alignment is not an extra assumption on top of `--assume-valid-params`: that flag
/// already assumes the pointer designates a *valid instance* of its pointee type, and a
/// valid instance of `T` is aligned to `alignof(T)`. Taking the alignment from the type
/// rather than guessing it from the size is what lets an over-aligned kernel struct
/// (`____cacheline_aligned`, `alignof == 64`) discharge a `load … align 64`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtrHint {
    /// Byte size of the pointee type. Always `> 0` when a hint is recorded.
    pub size: u64,
    /// Declared byte alignment of the pointee type; `0` when debug info does not record
    /// it, in which case the consumer derives a conservative alignment from the size.
    pub align: u32,
    /// **Trailing-context extent**: the byte extent the code itself reaches through the C
    /// "context behind the struct" idiom — `getelementptr %struct.T, ptr %p, i64 k` with
    /// `k >= 1`, i.e. `p + k * sizeof(T)`, as in `crypto_skcipher_ctx(tfm)` (`tfm + 1`) or
    /// `netdev_priv(dev)`. Such a pointer designates an allocation that is *larger than its
    /// declared type*: the struct followed by a context whose size only the allocation site
    /// knows. Navigating into element `k` reaches at most `(k + 1) * sizeof(T)`, so that is
    /// the extent recorded here. `0` when the function never uses the idiom on this pointer.
    ///
    /// Honoured only under `--assume-struct-tail`; otherwise the region keeps `size` and every
    /// access into the tail stays UNKNOWN — soundly, since the tail's real size is unknown.
    pub tail: u64,
}

impl PtrHint {
    /// The byte size to give the pointee's region. With `struct_tail` (the `--assume-struct-tail`
    /// opt-in) an object the code navigates past its own type — the C "context behind the struct"
    /// idiom — is sized to cover that reach; otherwise it is exactly the declared type.
    pub fn region_size(&self, struct_tail: bool) -> u64 {
        if struct_tail {
            self.size.max(self.tail)
        } else {
            self.size
        }
    }

    /// The alignment to give the pointee's region: the type's declared one when debug info
    /// recorded it, else derived from the size — a type's size is a multiple of its alignment,
    /// so the size's trailing zeros are a lower bound on it. The derived form is capped at 16
    /// (`max_align_t`), because beyond that the size no longer implies the alignment: a struct
    /// of size 64 need not be 64-aligned. A declared alignment carries no such cap, which is
    /// what discharges a `load … align 64` off an over-aligned (`____cacheline_aligned`) struct.
    pub fn region_align(&self) -> u64 {
        if self.align > 0 {
            u64::from(self.align)
        } else {
            1u64 << self.size.trailing_zeros().min(4)
        }
    }
}

/// A global/static definition: what the analysis may assume about the memory
/// behind its symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GlobalDef {
    /// Byte size of the definition's type.
    pub size: u64,
    /// Declared alignment (1 if unspecified — alignment proofs then fail
    /// soundly rather than assuming).
    pub align: u32,
    /// `false` for `constant` definitions (stores to them are invalid).
    pub writable: bool,
}

impl Module {
    /// An empty module with the given name and the default 64-bit layout.
    pub fn new(name: impl Into<String>) -> Self {
        Module {
            name: name.into(),
            functions: Vec::new(),
            layout: DataLayout::default(),
            param_contracts: HashMap::new(),
            unanalyzed: Vec::new(),
            internal: std::collections::HashSet::new(),
            globals: HashMap::new(),
            raw_ptr_hints: HashMap::new(),
            prov_grants: HashMap::new(),
            global_fn_ptrs: HashMap::new(),
            reg_ptr_hints: HashMap::new(),
            mmio_handlers: HashMap::new(),
        }
    }

    /// The contracts for `func`'s parameters, as a vec parallel to its params
    /// (`None` where there is no contract).
    pub fn contracts_for(&self, func: &Function) -> Vec<Option<PtrContract>> {
        (0..func.params.len() as u32)
            .map(|i| self.param_contracts.get(&(func.id, i)).copied())
            .collect()
    }

    /// Look up a function by id.
    pub fn function(&self, id: FuncId) -> Option<&Function> {
        self.functions.iter().find(|f| f.id == id)
    }
}

/// The id assignment [`merge_modules`] uses, exposed separately so a whole-program
/// analysis can resolve call edges by name **without linking**, keyed by the same
/// `FuncId`s the linked module would have. For `mods` in order every function gets
/// a fresh sequential id; every *external* (non-`internal`) definition contributes
/// its name → id (first definition wins) so a cross-module `Symbol` call resolves
/// to its definition exactly as it does after linking. Returns `(name → id map,
/// per-module old→new id remap)`.
pub fn merge_id_plan(mods: &[&Module]) -> (HashMap<String, FuncId>, Vec<HashMap<FuncId, FuncId>>) {
    let mut name_to_id: HashMap<String, FuncId> = HashMap::new();
    let mut remaps: Vec<HashMap<FuncId, FuncId>> = Vec::with_capacity(mods.len());
    let mut next: u32 = 0;
    for m in mods {
        let mut remap = HashMap::new();
        for f in &m.functions {
            let nid = FuncId(next);
            next += 1;
            remap.insert(f.id, nid);
            if !m.internal.contains(&f.id) {
                name_to_id.entry(f.name.clone()).or_insert(nid);
            }
        }
        remaps.push(remap);
    }
    (name_to_id, remaps)
}

/// **Link** several single-translation-unit modules into one whole-program module
/// (cross-file analysis). Every function is given a fresh global [`FuncId`]; a call
/// that was opaque because the callee lived in another file — a `Callee::Symbol(name)`
/// — is resolved to the defining function when that definition is present in the merged
/// set, so a caller's context (e.g. a `switch (optname) case A..B:` validation) now flows
/// into the callee. Only **external-linkage** definitions are resolved by name: a
/// `static`/internal function's name may collide across files, so internal functions keep
/// their per-file identity and are only reachable through their own `Callee::Direct` edges.
/// Declarations (no definition anywhere) stay `Callee::Symbol` (opaque, contract-modelled).
pub fn merge_modules(mods: Vec<Module>, name: impl Into<String>) -> Module {
    let mut merged = Module::new(name);
    if let Some(m) = mods.first() {
        merged.layout = m.layout;
    }
    // Pass 1: assign fresh ids and, for external definitions, a name → id map (first wins).
    let (name_to_id, remaps) = merge_id_plan(&mods.iter().collect::<Vec<_>>());
    // Pass 2: **move** functions in with remapped ids and resolved call edges; merge side
    // tables. Taking ownership avoids cloning every function/instruction of the group — the
    // dominant cost when linking large driver TUs for cross-file scanning.
    for (mi, m) in mods.into_iter().enumerate() {
        let remap = &remaps[mi];
        let internal = &m.internal;
        for mut nf in m.functions {
            let was_internal = internal.contains(&nf.id);
            nf.id = remap[&nf.id];
            for block in &mut nf.blocks {
                for inst in &mut block.insts {
                    if let Inst::Call { callee, .. } = inst {
                        *callee = match callee {
                            // In-module edge: renumber to the function's new id.
                            Callee::Direct(old) => Callee::Direct(remap[old]),
                            // Cross-file edge: resolve to the definition if we now have it.
                            Callee::Symbol(nm) => match name_to_id.get(nm) {
                                Some(&id) => Callee::Direct(id),
                                None => Callee::Symbol(std::mem::take(nm)),
                            },
                            Callee::Indirect(op) => Callee::Indirect(op.clone()),
                        };
                    }
                }
            }
            if was_internal {
                merged.internal.insert(nf.id);
            }
            merged.functions.push(nf);
        }
        for ((fid, idx), c) in m.param_contracts {
            merged.param_contracts.insert((remap[&fid], idx), c);
        }
        for ((fid, idx), h) in m.raw_ptr_hints {
            merged.raw_ptr_hints.insert((remap[&fid], idx), h);
        }
        for ((fid, reg), hint) in m.reg_ptr_hints {
            merged.reg_ptr_hints.insert((remap[&fid], reg), hint);
        }
        for (name, h) in m.mmio_handlers {
            merged.mmio_handlers.insert(name, h);
        }
        for (k, v) in m.globals {
            merged.globals.entry(k).or_insert(v);
        }
        for (k, v) in m.global_fn_ptrs {
            merged
                .global_fn_ptrs
                .entry(k)
                .or_insert_with(|| v.into_iter().map(|(off, fid)| (off, remap[&fid])).collect());
        }
        for (k, v) in m.prov_grants {
            merged.prov_grants.entry(k).or_default().extend(v);
        }
        merged.unanalyzed.extend(m.unanalyzed);
    }
    merged
}

#[cfg(test)]
#[path = "func_tests.rs"]
mod tests;
