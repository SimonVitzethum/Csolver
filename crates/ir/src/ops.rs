//! MSIR operands, r-values, conditions and call targets (split out of `inst`).

use crate::id::{FuncId, RegId};
use crate::ty::Type;
use csolver_core::BitVector;

/// A compile-time-constant operand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Const {
    /// A fixed-width integer constant.
    Int(BitVector),
    /// The null pointer.
    Null,
    /// An undefined value (`undef`/`poison`): reading it is itself a safety
    /// concern and is tracked as such.
    Undef,
    /// The address of a named symbol (global / function).
    Symbol(String),
    /// The address of a named symbol plus a constant byte offset — a folded
    /// `getelementptr` constant expression into a global.
    SymbolOffset(String, i64),
}

/// An instruction operand: either an SSA register or a constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    /// A previously-defined SSA value.
    Reg(RegId),
    /// A constant.
    Const(Const),
}

impl Operand {
    /// Convenience: an integer constant operand.
    pub fn int(width: u32, value: u128) -> Operand {
        Operand::Const(Const::Int(BitVector::new(width, value)))
    }

    /// If this operand is a register, its id.
    pub fn as_reg(&self) -> Option<RegId> {
        match self {
            Operand::Reg(r) => Some(*r),
            Operand::Const(_) => None,
        }
    }
}

/// Binary arithmetic / bitwise operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Unsigned division.
    UDiv,
    /// Signed division.
    SDiv,
    /// Unsigned remainder.
    URem,
    /// Signed remainder.
    SRem,
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise xor.
    Xor,
    /// Shift left.
    Shl,
    /// Logical shift right.
    LShr,
    /// Arithmetic shift right.
    AShr,
}

/// Overflow flags on a binary arithmetic op, carried from the frontend
/// (LLVM `nsw`/`nuw`). When either is set the producer has declared the
/// operation must not wrap, so the verifier raises an overflow obligation
/// (bug-finding only). The default — both clear — means wrapping is allowed
/// and no obligation is raised, so every non-arithmetic frontend can leave
/// it at `Default` soundly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct WrapFlags {
    /// `nsw` — signed overflow is undefined behaviour.
    pub nsw: bool,
    /// `nuw` — unsigned overflow is undefined behaviour.
    pub nuw: bool,
}

/// Integer comparison predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Unsigned less-than.
    Ult,
    /// Unsigned less-or-equal.
    Ule,
    /// Unsigned greater-than.
    Ugt,
    /// Unsigned greater-or-equal.
    Uge,
    /// Signed less-than.
    Slt,
    /// Signed less-or-equal.
    Sle,
    /// Signed greater-than.
    Sgt,
    /// Signed greater-or-equal.
    Sge,
}

/// Conversion operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastOp {
    /// Truncate to a narrower integer.
    Trunc,
    /// Zero-extend to a wider integer.
    ZExt,
    /// Sign-extend to a wider integer.
    SExt,
    /// Reinterpret a pointer as an integer (loses, then must re-derive,
    /// provenance — flagged for the memory model).
    PtrToInt,
    /// Reinterpret an integer as a pointer (provenance must be re-established).
    IntToPtr,
    /// Same-size reinterpretation.
    Bitcast,
}

/// The right-hand side of a register-defining assignment (a pure computation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RValue {
    /// Copy an operand.
    Use(Operand),
    /// A binary operation.
    Bin {
        /// Operator.
        op: BinOp,
        /// Left operand.
        lhs: Operand,
        /// Right operand.
        rhs: Operand,
        /// Overflow flags carried from the frontend (`add nsw`/`add nuw`/…).
        /// Default is wrapping (no obligation); set only where the producer
        /// documents the operation as overflow-free.
        flags: WrapFlags,
    },
    /// A comparison producing an `i1`.
    Cmp {
        /// Predicate.
        op: CmpOp,
        /// Left operand.
        lhs: Operand,
        /// Right operand.
        rhs: Operand,
    },
    /// A type conversion.
    Cast {
        /// Conversion kind.
        op: CastOp,
        /// Value being converted.
        operand: Operand,
        /// Target type.
        to: Type,
    },
    /// `cond ? then_val : else_val` — an operand-level select (LLVM `select`). For
    /// pointers this keeps BOTH operands as a provenance join, so an access through
    /// the result is proved in-bounds for each alternative under its guard (rather
    /// than degrading to an opaque pointer). For scalars it is an `ite`.
    Select {
        /// The `i1` condition operand.
        cond: Operand,
        /// The value when `cond` is true.
        then_val: Operand,
        /// The value when `cond` is false.
        else_val: Operand,
    },
}

/// A boolean predicate over operands, used to express a [`Inst::SafetyCheck`]
/// condition without yet committing to the solver's constraint IR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Condition {
    /// Always true (a discharged/vacuous check).
    True,
    /// A comparison.
    Cmp {
        /// Predicate.
        op: CmpOp,
        /// Left operand.
        lhs: Operand,
        /// Right operand.
        rhs: Operand,
    },
    /// Conjunction.
    And(Vec<Condition>),
    /// Disjunction.
    Or(Vec<Condition>),
    /// Negation.
    Not(Box<Condition>),
}

/// Which bulk memory operation an [`Inst::MemIntrinsic`] performs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemKind {
    /// `memcpy`: copy, non-overlapping.
    Copy,
    /// `memmove`: copy, may overlap.
    Move,
    /// `memset`: fill with a byte value.
    Set,
    /// A `copy_from_user`-style bulk write of **untrusted user data** into the
    /// destination (kernel) buffer: bounds-checked like `Set`, but it additionally
    /// marks the destination region user-controlled, so a value later loaded from it
    /// is a *genuine adversarial input* (an attacker picks it) — a length read back
    /// from a user-copied struct can then drive a refutable overflow.
    UserFill,
    /// A `copy_to_user`-style bulk **read** of the kernel source buffer that is
    /// disclosed to userspace: bounds-checked like a read, and additionally
    /// carries the `NoInfoLeak` obligation — the copied source bytes must have
    /// been initialized (a never-written freshly-allocated buffer copied out is a
    /// kernel information leak).
    UserDrain,
}

/// The target of a [`Inst::Call`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Callee {
    /// A direct call to a known function in this module.
    Direct(FuncId),
    /// A call to an externally-named symbol (FFI / not-yet-resolved).
    Symbol(String),
    /// An indirect call through a computed pointer.
    Indirect(Operand),
}
