//! # csolver-ir — the Memory-Safety IR (MSIR)
//!
//! MSIR is the single intermediate representation that every frontend (Rust
//! MIR, LLVM-IR, machine assembly) lowers into. The heavy analyses are written
//! once against MSIR, never per-frontend.
//!
//! ## Design choices
//!
//! * **Typed SSA with block arguments.** Each [`BasicBlock`] declares
//!   [`BasicBlock::params`] and every branch supplies matching arguments. This
//!   replaces LLVM PHI nodes with a representation that is easier to reason
//!   about: a value's definition point is unambiguous and dataflow across edges
//!   is explicit. Frontends lower PHIs to block parameters.
//! * **Explicit memory operations.** [`Inst::Load`], [`Inst::Store`],
//!   [`Inst::Alloc`], [`Inst::Dealloc`] and [`Inst::PtrOffset`] carry the type,
//!   alignment and region information that proof-obligation generation needs.
//!   Pointer arithmetic is never hidden inside an arithmetic op.
//! * **Safety checks are first-class.** [`Inst::SafetyCheck`] embeds a proof
//!   obligation directly in the instruction stream. Frontends emit the
//!   canonical checks implied by each memory op and may add more from source
//!   information (borrow facts, panic edges).
//!
//! ## Soundness obligation on frontends
//!
//! A lowering must *over-approximate* the original's behaviours: every concrete
//! execution of the source must correspond to a concrete execution of the
//! emitted MSIR. Each frontend argues this in its `Verification/` folder.

pub mod frontend;
pub mod func;
pub mod id;
pub mod inst;
mod ops;
pub mod ty;

pub use frontend::Frontend;
pub use func::{
    merge_field_evidence, merge_id_plan, merge_modules, BasicBlock, FieldContract, Function,
    GlobalDef, MmioHandler, Module, PtrContract, PtrHint, SizeSpec, Terminator,
};
pub use id::{BlockId, FuncId, RegId};
pub use inst::{
    BinOp, Callee, CastOp, CmpOp, Condition, Const, Inst, MemKind, Operand, RValue, RefResult,
    WrapFlags,
};
pub use ty::{DataLayout, Type};
