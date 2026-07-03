//! Blocks, terminators, functions and modules.

use crate::id::{BlockId, FuncId, RegId};
use crate::inst::{Inst, Operand};
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
    pub fn block(&self, id: BlockId) -> Option<&BasicBlock> {
        self.blocks.iter().find(|b| b.id == id)
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

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used)]
    use super::*;
    use crate::inst::{CmpOp, Const, RValue};
    use csolver_core::SafetyProperty;

    /// Build a tiny function:
    ///   bb0: %2 = icmp ult %0, %1 ; safety-check in_bounds ; condbr -> bb1/bb2
    ///   bb1: return %0
    ///   bb2: unreachable
    fn sample() -> Function {
        let r0 = RegId(0);
        let r1 = RegId(1);
        let r2 = RegId(2);
        let bb0 = {
            let mut b = BasicBlock::new(
                BlockId(0),
                Terminator::CondBr {
                    cond: Operand::Reg(r2),
                    then_blk: BlockId(1),
                    then_args: vec![],
                    else_blk: BlockId(2),
                    else_args: vec![],
                },
            );
            b.insts.push(Inst::Assign {
                dst: r2,
                ty: Type::Bool,
                value: RValue::Cmp {
                    op: CmpOp::Ult,
                    lhs: Operand::Reg(r0),
                    rhs: Operand::Reg(r1),
                },
            });
            b.insts.push(Inst::SafetyCheck {
                property: SafetyProperty::InBounds,
                condition: crate::inst::Condition::Cmp {
                    op: CmpOp::Ult,
                    lhs: Operand::Reg(r0),
                    rhs: Operand::Reg(r1),
                },
                note: "index < len".into(),
            });
            b
        };
        let bb1 = BasicBlock::new(BlockId(1), Terminator::Return(Some(Operand::Reg(r0))));
        let bb2 = BasicBlock::new(BlockId(2), Terminator::Unreachable);

        Function {
            id: FuncId(0),
            name: "sample".into(),
            params: vec![(r0, Type::int(64)), (r1, Type::int(64))],
            ret_ty: Type::int(64),
            blocks: vec![bb0, bb1, bb2],
            entry: BlockId(0),
        }
    }

    #[test]
    fn successors_and_lookup() {
        let f = sample();
        assert_eq!(f.block_count(), 3);
        let entry = f.block(f.entry).unwrap();
        assert_eq!(entry.successors(), vec![BlockId(1), BlockId(2)]);
        assert_eq!(f.block(BlockId(1)).unwrap().successors(), vec![]);
    }

    #[test]
    fn defined_registers() {
        let f = sample();
        let defs: Vec<_> = f
            .block(BlockId(0))
            .unwrap()
            .insts
            .iter()
            .filter_map(Inst::defined_reg)
            .collect();
        assert_eq!(defs, vec![RegId(2)]);
    }

    #[test]
    fn const_null_is_distinct() {
        assert_ne!(Const::Null, Const::Undef);
    }
}
