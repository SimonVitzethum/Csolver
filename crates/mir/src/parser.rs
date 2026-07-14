//! A parser for a practical subset of textual Rust MIR.
//!
//! It is deliberately tolerant: the scope/debug/`let` preamble is skipped, and
//! any statement, rvalue, place, type, or terminator outside the supported
//! subset degrades to an explicit `Unsupported` marker rather than failing — so
//! the lowerer can reject just that function (recording it as unanalyzed) while
//! still verifying the rest of the module. Nothing here is guessed into a
//! sound-looking shape: an unrecognised construct is always surfaced.

use crate::lexer::{lex, Tok};
use csolver_core::{Error, Result};

/// A MIR local (`_N`).
pub(crate) type Local = u32;

/// A (subset of) MIR type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MType {
    /// `iN` / `uN` / `isize` / `usize`.
    Int { width: u32, signed: bool },
    /// `bool`.
    Bool,
    /// `()`.
    Unit,
    /// `&T` / `&mut T` (the bool is `true` for `&mut`).
    Ref(Box<MType>, bool),
    /// `*const T` / `*mut T` (the bool is `true` for `*mut`).
    Ptr(Box<MType>, bool),
    /// `[T; N]`.
    Array(Box<MType>, u64),
    /// `[T]`.
    Slice(Box<MType>),
    /// An **interior-mutable** named type (`UnsafeCell`/`Cell`/`RefCell`/`Mutex`/`RwLock`/
    /// `Atomic*`, …): opaque like [`MType::Other`] for layout, but flagged so the aliasing model
    /// does NOT track a `&`-borrow of it — interior mutability legitimately writes through a
    /// shared reference, so treating such a borrow like an ordinary `&T` could false-FAIL.
    InteriorMut,
    /// A type outside the modelled subset.
    Other,
}

/// Whether a type-path segment names an interior-mutable wrapper (the `UnsafeCell` family).
pub(crate) fn is_interior_mut_name(n: &str) -> bool {
    matches!(
        n,
        "UnsafeCell" | "SyncUnsafeCell" | "Cell" | "RefCell" | "OnceCell" | "LazyCell"
            | "Mutex" | "RwLock" | "ReentrantMutex"
    ) || n.starts_with("Atomic")
}

/// A MIR constant (the subset we model).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MConst {
    Int(i128),
    Bool(bool),
}

/// A MIR place: a local with projections.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Place {
    Local(Local),
    Deref(Box<Place>),
    Index(Box<Place>, Local),
    /// A *constant* index projection `PLACE[N of M]` (MIR's `ConstantIndex`):
    /// element `N` of an array/slice of at least `M` elements. Distinct from
    /// `Index` (a runtime local index) because the offset is a compile-time
    /// constant.
    ConstIndex(Box<Place>, u64),
    /// A field projection `.N`, carrying the field's type from the place's type
    /// ascription (`((*_1).0: i32)`) when present — the field type gives its size
    /// and alignment, which is all the layout a field access needs.
    Field(Box<Place>, u32, Option<MType>),
}

/// A MIR operand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Operand {
    Copy(Place),
    Move(Place),
    Const(MConst),
}

/// The binary operators we model (others lower to an opaque value).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinKind {
    Add,
    Sub,
    Mul,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    BitAnd,
    BitOr,
    BitXor,
    /// Pointer arithmetic `ptr.offset(count)` — `base + count * size_of::<pointee>()`.
    Offset,
    Other,
}

/// A MIR rvalue (the subset we model).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Rvalue {
    Use(Operand),
    Bin(BinKind, Operand, Operand),
    /// Checked arithmetic (`AddWithOverflow`/…): a `(result, overflow)` tuple.
    /// Field `.0` is the arithmetic result, `.1` the overflow flag.
    CheckedBin(BinKind, Operand, Operand),
    Len(Place),
    /// `&PLACE` / `&mut PLACE` / `&raw …` — with the borrow kind (for the aliasing model).
    Ref(Place, RefKind),
    Cast(Operand),
    /// `discriminant(PLACE)` — reads an enum's tag. The value is opaque (so a
    /// `switchInt` on it soundly explores every arm); lowering still checks the
    /// enum reference is valid.
    Discriminant(Place),
    /// An rvalue outside the modelled subset.
    Other,
}

/// The kind of a `&`-borrow, for the opt-in aliasing (borrow-stack) model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RefKind {
    /// A mutable borrow (`&mut PLACE` / `&raw mut PLACE`) — a unique reborrow.
    Mut,
    /// A shared borrow (`&PLACE` / `&raw const PLACE`).
    Shared,
    /// A borrow that is NOT a plain unique/shared reborrow (`fake`/`shallow`/`two_phase`),
    /// so it emits no retag marker (the aliasing model would otherwise risk a false FAIL).
    Opaque,
}

/// Who an assignment-form call invokes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CalleeSpec {
    /// A named function/path (the last path segment is the resolution key).
    Named(String),
    /// An indirect call through a function-pointer local.
    Indirect(Local),
}

/// A MIR statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MStmt {
    Assign(Place, Rvalue),
    /// `StorageLive(_N)` — the local's stack storage becomes live (its scope begins).
    StorageLive(Local),
    /// `StorageDead(_N)` — the local's stack storage ends; a pointer into it is now dangling
    /// (use-after-scope). Only meaningful for an address-taken local (see the lowering).
    StorageDead(Local),
    /// `nop`/`FakeRead`/`AscribeUserType`/… — no effect on the model.
    Nop,
}

/// A MIR terminator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MTerm {
    Goto(usize),
    Return,
    /// `switchInt(op) -> [v: bb, …, otherwise: bb]`.
    SwitchInt(Operand, Vec<(i128, usize)>, usize),
    /// `assert(<!?>cond, …) -> bb`: the bounds/overflow check. `expected` is the
    /// value `cond` must take to *continue* (true unless negated with `!`).
    Assert { cond: Operand, expected: bool, target: usize },
    /// `_d = callee(args) -> [return: bb, …]`: a function call (`target` is
    /// `None` for a diverging call with no return edge).
    Call { dst: Place, callee: CalleeSpec, args: Vec<Operand>, target: Option<usize>, unwind: Option<usize> },
    /// `drop(place) -> [return: bb, …]`: runs the value's destructor, which may
    /// free what it owns. Modelled as a freeing call (`target` is `None` for a
    /// diverging drop). The dropped place itself is not needed — the conservative
    /// free invalidates every owned region's liveness regardless.
    Drop { target: Option<usize>, unwind: Option<usize> },
    Unreachable,
    /// A terminator outside the modelled subset (`call`, `drop`, …): the whole
    /// function is rejected (recorded unanalyzed) rather than mis-modelled.
    Unsupported,
}

/// A MIR basic block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MBlock {
    pub(crate) id: usize,
    pub(crate) stmts: Vec<MStmt>,
    /// Source location of each statement (`FILE:LINE:COL`), parallel to `stmts`;
    /// `None` where unknown. Threaded into the lowered instructions' obligations.
    pub(crate) stmt_spans: Vec<Option<String>>,
    pub(crate) term: MTerm,
    /// Source location of the terminator.
    pub(crate) term_span: Option<String>,
}

/// A parsed MIR function body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MirBody {
    pub(crate) name: String,
    pub(crate) params: Vec<(Local, MType)>,
    pub(crate) ret: MType,
    /// The `let _N: T;` declarations from the body preamble (including those nested
    /// in `scope { … }`). Carries the type of every non-parameter local — notably a
    /// call result `let _x: &T;`, so its `Inst::Call` gets a pointer `ret_ty`
    /// instead of an opaque scalar.
    pub(crate) locals: Vec<(Local, MType)>,
    pub(crate) blocks: Vec<MBlock>,
}

/// The successfully-parsed bodies plus the `(name, reason)` of any that failed.
pub(crate) type ParsedModule = (Vec<MirBody>, Vec<(String, String)>);

/// Parse every `fn` body in a MIR dump. A body that fails to parse does not
/// abort the whole module: its name is recorded (so the lowerer can report it
/// `UNKNOWN`) and parsing resumes at the next `fn` — per-function recovery, like
/// the lowerer's.
pub(crate) fn parse_module(src: &str) -> Result<ParsedModule> {
    let (toks, locs) = lex(src)?;
    let mut p = Parser { toks, pos: 0, locs };
    let mut bodies = Vec::new();
    let mut failed = Vec::new();
    while p.skip_to_fn() {
        let name = match p.peek() {
            Tok::Word(w) => w.clone(),
            _ => String::new(),
        };
        let start = p.pos;
        match p.body() {
            Ok(b) => bodies.push(b),
            Err(e) => {
                failed.push((name, e.to_string()));
                if p.pos <= start {
                    p.pos = start + 1; // guarantee progress before the next `fn`
                }
            }
        }
    }
    Ok((bodies, failed))
}

pub(crate) struct Parser {
    pub(crate) toks: Vec<Tok>,
    pub(crate) pos: usize,
    /// Per-token source location (`FILE:LINE:COL`), parallel to `toks`; `None`
    /// where the MIR carries no span. Read at a statement's first token to give
    /// each lowered obligation a source pointer.
    pub(crate) locs: Vec<Option<String>>,
}


// --- module split (mechanical refactor) ---
mod body;
mod expr;
mod types;
mod helpers;
pub(crate) use helpers::*;
