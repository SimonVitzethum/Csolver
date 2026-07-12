//! A recursive-descent parser for a practical subset of textual LLVM IR.
//!
//! Supported: `define`d functions; integer/`ptr`/array/`void` types (and legacy
//! `T*`); the instructions `alloca`, `load`, `store`, `getelementptr`
//! (pointer-arith and `[N x T]` array forms), the integer binary ops, `icmp`,
//! the integer/pointer casts, `call`, and `phi`; the terminators `ret`, `br`
//! (conditional and unconditional) and `unreachable`. Anything outside the
//! subset is reported as an error so the caller degrades to `UNKNOWN` rather
//! than silently mis-modelling it.

use crate::lexer::{lex, Tok};
use csolver_core::{Error, Result};
use std::collections::HashMap;

/// A parsed module.
#[derive(Debug, Clone)]
pub struct LModule {
    /// The defined functions that parsed successfully.
    pub funcs: Vec<LFunc>,
    /// `(name, reason)` for functions that failed to parse and were skipped, so
    /// the caller can report them as `UNKNOWN` rather than silently dropping
    /// them.
    pub unanalyzed: Vec<(String, String)>,
    /// Top-level global/static definitions (`@name = … global/constant <ty> …`).
    /// Only definitions whose type parsed are recorded; anything else is skipped
    /// (its symbol then stays an opaque scalar — the sound default).
    pub globals: Vec<LGlobal>,
    /// The debug-info type graph (`!DI…`), for recovering opaque-pointer pointee
    /// types. Empty when the module carries no debug info.
    pub(crate) debuginfo: crate::debuginfo::DebugInfo,
    /// Per global-symbol, the largest `dereferenceable(N)` a bare `@g` use asserts —
    /// an authoritative lower bound on the global's byte size (clang emits it from the
    /// type), used to correct a size the type-layout computation gets wrong.
    pub(crate) deref_hints: std::collections::HashMap<String, u64>,
}

/// A parsed global definition.
#[derive(Debug, Clone)]
pub struct LGlobal {
    /// Symbol name (without the `@`).
    pub name: String,
    /// The definition's type (its size is the region size).
    pub ty: LType,
    /// `false` for `constant` definitions.
    pub writable: bool,
    /// Declared `align` (1 if unspecified).
    pub align: u32,
    /// The type was a *packed* struct `<{ … }>`: its size is the plain sum ofgrep FAIL ~/fullscan.log
    /// the field sizes (no padding). Packed types stay rejected in instruction
    /// contexts (a padded stand-in could oversize them); here the exact packed
    /// size is computable, so global definitions can be recorded.
    pub packed: bool,
    /// **Function/symbol-pointer fields** of a *constant* initializer: `(byte
    /// offset, symbol name)` for every element that is the address of a named
    /// symbol (`ptr @foo`). Used to devirtualise an indirect call whose target
    /// is loaded from a known constant ops-struct global. Populated only when the
    /// whole initializer's layout could be tracked exactly (else left empty — a
    /// missed field only lowers recall, an imprecise one would be unsound).
    pub fn_ptrs: Vec<(u64, String)>,
}

/// A parsed function definition.
#[derive(Debug, Clone)]
pub struct LFunc {
    /// Function name (without the leading `@`).
    pub name: String,
    /// Return type.
    pub ret: LType,
    /// Parameters, in order.
    pub params: Vec<LParam>,
    /// Basic blocks in textual order (the first is the entry).
    pub blocks: Vec<LBlock>,
    /// `define internal`/`private`: the function is not visible outside this
    /// module, so the module's call sites are all its call sites.
    pub internal: bool,
    /// The `!dbg !N` `DISubprogram` metadata id, if the function carries debug
    /// info — the key into [`crate::debuginfo`] for recovering pointee types.
    pub dbg: Option<u32>,
}

/// A parsed function parameter with the attributes relevant to memory safety.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LParam {
    /// Parameter type.
    pub ty: LType,
    /// Local name (empty if unnamed).
    pub name: String,
    /// `dereferenceable(N)`: bytes guaranteed valid behind a pointer.
    pub deref: Option<u64>,
    /// `sret(T)` / `byval(T)`: the pointer refers to a caller-provided buffer of
    /// `sizeof(T)` bytes (the ABI for returning / passing an aggregate by value).
    /// Semantically a `dereferenceable(sizeof(T))`; kept as the type so the
    /// lowering computes the size with its layout.
    pub abi_buf: Option<LType>,
    /// `align N`.
    pub align: Option<u32>,
    /// `readonly`.
    pub readonly: bool,
    /// `writeonly`.
    pub writeonly: bool,
}

/// A parsed basic block.
#[derive(Debug, Clone)]
pub struct LBlock {
    /// The block label.
    pub label: String,
    /// Leading `phi` instructions (become MSIR block parameters).
    pub phis: Vec<LPhi>,
    /// Straight-line instructions.
    pub insts: Vec<LInst>,
    /// The terminator.
    pub term: LTerm,
}

/// A `phi` node: `dst = phi ty [v, %pred], ...`.
#[derive(Debug, Clone)]
pub struct LPhi {
    /// Destination register name.
    pub dst: String,
    /// Value type.
    pub ty: LType,
    /// `(incoming value, predecessor label)` pairs.
    pub incomings: Vec<(LValue, String)>,
}

/// A parsed LLVM type (subset).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LType {
    /// `void`.
    Void,
    /// `iN`.
    Int(u32),
    /// `ptr` (or legacy `T*`).
    Ptr,
    /// `[N x T]`.
    Array(Box<LType>, u64),
    /// `<N x T>` (a vector — modelled by its byte size).
    Vector(Box<LType>, u64),
    /// `{ T, T, … }` (an aggregate — e.g. the `{iN, i1}` of a checked-arithmetic
    /// intrinsic; destructured by `extractvalue`, not used directly).
    Struct(Vec<LType>),
    /// `<{ T, T, … }>` — a *packed* struct (no inter-field padding, byte
    /// alignment). Modelled with an exact packed layout, so — unlike a padded
    /// stand-in — it never oversizes. Swift lowers every type to a packed struct.
    PackedStruct(Vec<LType>),
    /// `%"name"` — a reference to a top-level `%"name" = type { … }` definition.
    /// Resolved by [`Parser::ltype`] against the collected definitions before it
    /// leaves the parser; reaching the lowering unresolved is a parser bug.
    Named(String),
    /// `metadata` — a compiler-annotation operand (`llvm.assume`,
    /// `llvm.experimental.noalias.scope.decl`, …). Zero-sized; never memory.
    Metadata,
}

/// A parsed operand value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LValue {
    /// `%name`.
    Local(String),
    /// An integer literal (`true`/`false` map to 1/0).
    Int(i128),
    /// `null`.
    Null,
    /// `undef` / `poison`.
    Undef,
    /// `@name`.
    Global(String),
    /// A folded `getelementptr` constant expression into a global:
    /// `@name` displaced by `index` elements of `elem`.
    GlobalOff {
        /// The base symbol.
        name: String,
        /// Element type of the constant gep (byte stride).
        elem: LType,
        /// Element index.
        index: i128,
    },
}

/// Integer binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LBin {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
}

/// Comparison predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LPred {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

/// Cast operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LCast {
    Trunc,
    ZExt,
    SExt,
    PtrToInt,
    IntToPtr,
    Bitcast,
}

/// A parsed straight-line instruction.
#[derive(Debug, Clone)]
pub enum LInst {
    /// `dst = alloca ty[, align n]`.
    Alloca { dst: String, ty: LType, align: u32 },
    /// `dst = load ty, ptr p[, align n]`.
    Load {
        dst: String,
        ty: LType,
        ptr: LValue,
        align: u32,
        align_meta: Option<u32>,
        /// `atomic`/`volatile` — a race-free access (excluded from the data-race pass).
        atomic: bool,
    },
    /// `store ty v, ptr p[, align n]`.
    Store {
        ty: LType,
        val: LValue,
        ptr: LValue,
        align: u32,
        /// `atomic`/`volatile` — a race-free access (excluded from the data-race pass).
        atomic: bool,
    },
    /// `dst = getelementptr [inbounds] elem, ptr base, i.. index`.
    Gep {
        dst: String,
        elem: LType,
        base: LValue,
        index: LValue,
    },
    /// A binary op.
    Bin {
        dst: String,
        op: LBin,
        ty: LType,
        a: LValue,
        b: LValue,
    },
    /// `dst = icmp pred ty a, b`.
    Icmp {
        dst: String,
        pred: LPred,
        ty: LType,
        a: LValue,
        b: LValue,
    },
    /// A cast.
    Cast {
        dst: String,
        op: LCast,
        val: LValue,
        to: LType,
    },
    /// `[dst =] call ret @callee(args)`.
    Call {
        dst: Option<String>,
        ret: LType,
        callee: String,
        args: Vec<LValue>,
    },
    /// `dst = extractvalue AGG %agg, index` — a field of an aggregate value (the
    /// first index only; nested indices are skipped). Used to recover a
    /// checked-arithmetic tuple's sum (index 0) and overflow flag (index 1).
    ExtractValue {
        dst: String,
        agg: LValue,
        index: u32,
    },
    /// `dst = atomicrmw <op> ptr p, T v <ord>` / `dst = cmpxchg ptr p, T c, T n
    /// <ord> <ord>` — an atomic read-modify-write of `sizeof(T)` bytes at `p`.
    /// At this abstraction both are a *load* (the returned old value) plus a
    /// *store* of an unknown value; `tuple` marks cmpxchg's `{T, i1}` result,
    /// which stays opaque (destructured by `extractvalue`).
    AtomicRmw {
        dst: String,
        ty: LType,
        ptr: LValue,
        tuple: bool,
    },
    /// `dst = getelementptr {S}, ptr base, iN index, i32 field` — an array-of-
    /// structs element's *field*: `base + index * sizeof(S) + offsetof(S, field)`.
    /// Lowered as a two-step pointer-offset chain with the exact padded field
    /// offset (a dropped field offset would misplace every subsequent access).
    GepField {
        dst: String,
        struct_ty: LType,
        base: LValue,
        index: LValue,
        field: u32,
    },
    /// A **multi-level** gep into a nested aggregate with an all-constant navigation
    /// path: `base + index * sizeof(agg) + offsetof(agg, path)` where `path` walks
    /// struct fields and constant array indices (`gep %S, ptr, i, K1, K2, …`). The
    /// exact nested byte offset is resolved at lowering from the type layout. This
    /// is pervasive in real C/kernel IR; without it the whole function was dropped.
    GepChain {
        dst: String,
        agg_ty: LType,
        base: LValue,
        indices: Vec<LValue>,
    },
    /// A value the frontend models opaquely — e.g. `landingpad`'s exception
    /// object, which carries no memory-safety content. Lowered to `undef` (sound;
    /// unconstrained), so a function that merely has an unwind-cleanup path is
    /// analysed rather than dropped whole.
    Opaque { dst: String },
    /// `dst = select i1 cond, T a, T b` — an operand-level select. Kept (not opaque)
    /// so a pointer select becomes a provenance join and a scalar select an `ite`.
    Select { dst: String, cond: LValue, then_val: LValue, else_val: LValue },
}

/// A parsed terminator.
#[derive(Debug, Clone)]
pub enum LTerm {
    /// `ret void` / `ret ty v`.
    Ret(Option<LValue>),
    /// `br label %dest`.
    Br(String),
    /// `br i1 c, label %t, label %f`.
    CondBr(LValue, String, String),
    /// `switch iN %v, label %default [ iN c0, label %d0 ... ]`.
    Switch {
        /// The scrutinee.
        value: LValue,
        /// Bit width of the scrutinee (and every case constant).
        width: u32,
        /// The default destination.
        default: String,
        /// `(case constant, destination)` pairs.
        cases: Vec<(i128, String)>,
    },
    /// `unreachable`.
    Unreachable,
    /// `[dst =] invoke ret @callee(args) to label %ok unwind label %cleanup` — a
    /// call with a normal and an unwind successor. Lowered to a `Call` instruction
    /// plus a branch to *both* edges (the unwind/cleanup path may run `Drop` code,
    /// whose memory safety must still be checked).
    Invoke {
        dst: Option<String>,
        ret: LType,
        callee: String,
        args: Vec<LValue>,
        ok: String,
        cleanup: String,
    },
    /// `[dst =] callbr … asm …(args) to label %ft [label %t1, …]` — an inline-asm
    /// **goto**: an opaque asm effect whose control may continue at the fallthrough
    /// or any listed label. Pervasive in the kernel (static keys, exception tables).
    /// Lowered to an asm havoc + a branch to *every* target (sound over-approximation).
    CallBr {
        dst: Option<String>,
        targets: Vec<String>,
    },
}

/// Parse a `.ll` source into an [`LModule`].
pub fn parse_module(src: &str) -> Result<LModule> {
    let debuginfo = crate::debuginfo::parse(src);
    let toks = lex(src)?;
    let mut p = Parser {
        toks,
        pos: 0,
        types: HashMap::new(),
        meta_ints: scan_meta_ints(src),
        deref_hints: HashMap::new(),
    };
    // Pre-scan for `%"name" = type <T>` definitions: a definition may lexically
    // follow its first use, so the table must be complete before any function
    // parses. An unparseable definition is skipped — a function using it then
    // fails per-function recovery (UNKNOWN), never a silent guess.
    p.collect_type_defs();
    p.pos = 0;
    let mut funcs = Vec::new();
    let mut unanalyzed = Vec::new();
    let mut globals = Vec::new();
    loop {
        p.skip_newlines();
        match p.peek() {
            Tok::Eof => break,
            // `@name = … global/constant <ty> <init>[, align N]` — a definition
            // the analysis can size. An unparseable line is skipped whole (its
            // symbol stays an opaque scalar).
            Tok::Global(_) if matches!(p.peek2(), Tok::Punct('=')) => {
                if let Some(g) = p.global_def() {
                    globals.push(g);
                }
            }
            Tok::Word(w) if w == "define" => {
                let start = p.pos;
                match p.function() {
                    Ok(f) => funcs.push(f),
                    // Per-function recovery: skip this function's body and
                    // record it so the verifier reports it as UNKNOWN.
                    Err(e) => {
                        p.pos = start;
                        let name = p.recover_function();
                        unanalyzed.push((name, e.to_string()));
                    }
                }
            }
            // Every other top-level line — `declare`, `source_filename`,
            // `target …`, `attributes #N = …`, `%T = type …`, `@g = …`, and
            // `!…` metadata — is irrelevant to the analysis and skipped.
            _ => p.skip_to_eol(),
        }
    }
    Ok(LModule {
        funcs,
        unanalyzed,
        globals,
        debuginfo,
        deref_hints: std::mem::take(&mut p.deref_hints),
    })
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    /// Top-level `%"name" = type <T>` definitions, collected in a pre-scan (a
    /// definition may lexically follow its first use). Values may themselves
    /// contain [`LType::Named`] references; [`Parser::resolve_named`] substitutes
    /// them at use time.
    types: HashMap<String, LType>,
    /// Single-integer metadata nodes (`!N = !{iW V}`), pre-scanned so an
    /// instruction's `!align !N` reference can be resolved to its value `V` while
    /// the instruction is parsed (the node may lexically follow the use).
    meta_ints: HashMap<u32, u64>,
    /// Per global-symbol, the largest `dereferenceable(N)` any use asserts on a
    /// **bare** `@g` operand. Clang emits it from the operand's *type* size, so it is
    /// an authoritative lower bound on the global's byte size — used to correct a
    /// size our own type-layout computation gets wrong (e.g. a 1-byte packed-struct
    /// discrepancy). Sound: it can only *raise* a global's size.
    deref_hints: HashMap<String, u64>,
}

/// Pre-scan single-integer metadata nodes (`!126 = !{i64 8}`) into a map from
/// node id to value. Only exact `!{iW V}` shapes are recorded — enough for the
/// `!align`/`!range`-style annotations the analysis reads; anything else is left
/// out (a missing entry just means the annotation is not credited).
fn scan_meta_ints(src: &str) -> HashMap<u32, u64> {
    let mut m = HashMap::new();
    for line in src.lines() {
        let Some((id, after)) = line
            .trim()
            .strip_prefix('!')
            .and_then(|r| r.split_once(" = "))
        else {
            continue;
        };
        let Ok(id) = id.trim().parse::<u32>() else {
            continue;
        };
        let Some(inner) = after
            .trim()
            .strip_prefix("!{")
            .and_then(|s| s.strip_suffix('}'))
        else {
            continue;
        };
        let mut parts = inner.split_whitespace();
        match (parts.next(), parts.next(), parts.next()) {
            // A single `iW V` element (no trailing tokens).
            (Some(ty), Some(val), None) if ty.starts_with('i') => {
                if let Ok(v) = val.trim_end_matches(',').parse::<u64>() {
                    m.insert(id, v);
                }
            }
            _ => {}
        }
    }
    m
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos]
    }
    fn peek2(&self) -> &Tok {
        self.toks.get(self.pos + 1).unwrap_or(&Tok::Eof)
    }
    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn expect_punct(&mut self, c: char) -> Result<()> {
        match self.bump() {
            Tok::Punct(p) if p == c => Ok(()),
            other => Err(Error::parse(format!("expected `{c}`, found {other:?}"))),
        }
    }
    fn expect_word(&mut self, w: &str) -> Result<()> {
        match self.bump() {
            Tok::Word(x) if x == w => Ok(()),
            other => Err(Error::parse(format!("expected `{w}`, found {other:?}"))),
        }
    }
    fn eat_word(&mut self, w: &str) -> bool {
        if matches!(self.peek(), Tok::Word(x) if x == w) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn global(&mut self) -> Result<String> {
        match self.bump() {
            Tok::Global(s) => Ok(s),
            other => Err(Error::parse(format!(
                "expected global @name, found {other:?}"
            ))),
        }
    }
    fn local(&mut self) -> Result<String> {
        match self.bump() {
            Tok::Local(s) => Ok(s),
            other => Err(Error::parse(format!(
                "expected local %name, found {other:?}"
            ))),
        }
    }

    /// Pre-scan the token stream for top-level `%"name" = type <T>` definitions.
    /// Runs before function parsing; leaves `self.pos` at the end of input.
    fn collect_type_defs(&mut self) {
        loop {
            self.skip_newlines();
            if matches!(self.peek(), Tok::Eof) {
                break;
            }
            if let (Tok::Local(name), Tok::Punct('=')) = (self.peek(), self.peek2()) {
                if matches!(self.toks.get(self.pos + 2), Some(Tok::Word(w)) if w == "type") {
                    let name = name.clone();
                    self.pos += 3;
                    if let Ok(ty) = self.ltype_raw() {
                        self.types.insert(name, ty);
                    }
                }
            }
            self.skip_to_eol();
        }
    }

    /// Substitute [`LType::Named`] references using the collected definitions.
    /// The depth cap breaks pathological reference cycles (a *valid* IR struct
    /// cannot contain itself by value, only behind `ptr`, which does not recurse).
    fn resolve_named(&self, ty: &LType, depth: u32) -> Result<LType> {
        if depth > 32 {
            return Err(Error::unsupported("named-type reference cycle"));
        }
        Ok(match ty {
            LType::Named(n) => match self.types.get(n) {
                Some(def) => self.resolve_named(&def.clone(), depth + 1)?,
                None => return Err(Error::unsupported(format!("unknown named type %\"{n}\""))),
            },
            LType::Array(e, n) => LType::Array(Box::new(self.resolve_named(e, depth + 1)?), *n),
            LType::Vector(e, n) => LType::Vector(Box::new(self.resolve_named(e, depth + 1)?), *n),
            LType::Struct(fs) => LType::Struct(
                fs.iter()
                    .map(|f| self.resolve_named(f, depth + 1))
                    .collect::<Result<_>>()?,
            ),
            LType::PackedStruct(fs) => LType::PackedStruct(
                fs.iter()
                    .map(|f| self.resolve_named(f, depth + 1))
                    .collect::<Result<_>>()?,
            ),
            other => other.clone(),
        })
    }

    /// Parse a type and resolve any named references — nothing downstream of the
    /// parser ever sees [`LType::Named`].
    fn ltype(&mut self) -> Result<LType> {
        let raw = self.ltype_raw()?;
        self.resolve_named(&raw, 0)
    }

    fn ltype_raw(&mut self) -> Result<LType> {
        let mut ty = match self.bump() {
            Tok::Word(w) if w == "void" => LType::Void,
            Tok::Word(w) if w == "metadata" => LType::Metadata,
            Tok::Word(w) if w == "ptr" => LType::Ptr,
            Tok::Word(w) if is_int_type(&w) => LType::Int(int_bits(&w)?),
            // Floating-point types carry no memory-safety content; model them as
            // opaque scalars of the right byte width (so a `load`/`store float`
            // gets the correct 4-byte access size). Float arithmetic never runs.
            Tok::Word(w) => match float_bits(&w) {
                Some(bits) => LType::Int(bits),
                None => return Err(Error::unsupported(format!("type name `{w}`"))),
            },
            // `%"core::…"` — a reference to a top-level type definition.
            Tok::Local(n) => LType::Named(n),
            Tok::Punct('[') => {
                let n = self.int()?;
                self.expect_word("x")?;
                let elem = self.ltype_raw()?;
                self.expect_punct(']')?;
                LType::Array(Box::new(elem), n as u64)
            }
            Tok::Punct('<') => {
                // `<{ … }>` — a packed struct (exact unpadded layout, so sound).
                if matches!(self.peek(), Tok::Punct('{')) {
                    self.pos += 1;
                    return Ok(LType::PackedStruct(self.struct_fields()?));
                }
                let n = self.int()?;
                self.expect_word("x")?;
                let elem = self.ltype_raw()?;
                self.expect_punct('>')?;
                LType::Vector(Box::new(elem), n as u64)
            }
            Tok::Punct('{') => LType::Struct(self.struct_fields()?),
            other => return Err(Error::unsupported(format!("type starting with {other:?}"))),
        };
        // Legacy pointer suffixes: `i32*`, `[..]**`, etc. all collapse to `ptr`.
        while matches!(self.peek(), Tok::Punct('*')) {
            self.pos += 1;
            ty = LType::Ptr;
        }
        Ok(ty)
    }

    /// The comma-separated field types of a struct body, ending at (and
    /// consuming) the closing `}`. The opening `{` is already consumed.
    fn struct_fields(&mut self) -> Result<Vec<LType>> {
        let mut fields = Vec::new();
        if !matches!(self.peek(), Tok::Punct('}')) {
            loop {
                fields.push(self.ltype_raw()?);
                if !matches!(self.peek(), Tok::Punct(',')) {
                    break;
                }
                self.pos += 1;
            }
        }
        self.expect_punct('}')?;
        Ok(fields)
    }

    fn int(&mut self) -> Result<i128> {
        match self.bump() {
            Tok::Int(n) => Ok(n),
            other => Err(Error::parse(format!("expected integer, found {other:?}"))),
        }
    }

    fn value(&mut self) -> Result<LValue> {
        // Aggregate/vector constants `<…>`, `[…]`, `{…}`: the value is not
        // modelled (memory safety needs only the access type/size), so skip it.
        match self.peek() {
            Tok::Punct('<') => {
                self.skip_balanced('<', '>')?;
                return Ok(LValue::Undef);
            }
            Tok::Punct('[') => {
                self.skip_balanced('[', ']')?;
                return Ok(LValue::Undef);
            }
            Tok::Punct('{') => {
                self.skip_balanced('{', '}')?;
                return Ok(LValue::Undef);
            }
            // A constant expression: an operator word (+ flags) then a
            // parenthesised body — `getelementptr inbounds (…)`, `bitcast (…)`,
            // `inttoptr (…)`, … . The value is opaque (memory safety needs the
            // access, not the constant address), so consume the body and forget it.
            Tok::Word(w)
                if !matches!(w.as_str(), "null" | "undef" | "poison" | "true" | "false") =>
            {
                let is_gep = w == "getelementptr";
                let mut j = self.pos;
                while matches!(self.toks.get(j), Some(Tok::Word(_))) {
                    j += 1;
                }
                if matches!(self.toks.get(j), Some(Tok::Punct('('))) {
                    self.pos = j;
                    // The folded global-displacement form —
                    // `getelementptr inbounds (T, ptr @g, iN K)` — keeps its
                    // base symbol and offset, so a load/store through it can be
                    // checked against the global's region. Any other constant
                    // expression is consumed opaquely.
                    if is_gep {
                        if let Some(v) = self.try_const_gep() {
                            return Ok(v);
                        }
                    }
                    self.skip_balanced('(', ')')?;
                    return Ok(LValue::Undef);
                }
            }
            _ => {}
        }
        // A metadata reference (`!5`, `!name`, `!{…}`): an annotation, not a value.
        if matches!(self.peek(), Tok::Punct('!')) {
            self.pos += 1;
            match self.peek() {
                Tok::Punct('{') => self.skip_balanced('{', '}')?,
                _ => self.pos += 1,
            }
            return Ok(LValue::Undef);
        }
        match self.bump() {
            Tok::Local(s) => Ok(LValue::Local(s)),
            Tok::Int(n) => Ok(LValue::Int(n)),
            // A float constant carries no memory-safety content — opaque.
            Tok::Float(_) => Ok(LValue::Undef),
            Tok::Global(s) => Ok(LValue::Global(s)),
            Tok::Word(w) if w == "null" => Ok(LValue::Null),
            Tok::Word(w) if w == "undef" || w == "poison" || w == "zeroinitializer" => {
                Ok(LValue::Undef)
            }
            Tok::Word(w) if w == "true" => Ok(LValue::Int(1)),
            Tok::Word(w) if w == "false" => Ok(LValue::Int(0)),
            other => Err(Error::unsupported(format!("operand value {other:?}"))),
        }
    }

    /// Skip the `atomic` / `volatile` qualifiers of a `load`/`store`, returning whether either
    /// was present — such an access is **race-free by construction** (`READ_ONCE`/`WRITE_ONCE`/
    /// `atomic_*` lower to volatile/atomic accesses), so the data-race pass excludes it.
    fn skip_memory_qualifiers(&mut self) -> bool {
        let mut atomic = false;
        while self.eat_word("atomic") || self.eat_word("volatile") {
            atomic = true;
        }
        atomic
    }

    /// Skip an atomic access's trailing `syncscope("…")` and ordering keyword
    /// (`load atomic i32, ptr %p seq_cst, align 4`).
    fn skip_atomic_ordering(&mut self) {
        if self.eat_word("syncscope") && matches!(self.peek(), Tok::Punct('(')) {
            let _ = self.skip_balanced('(', ')');
        }
        while matches!(self.peek(), Tok::Word(w) if matches!(w.as_str(),
            "unordered" | "monotonic" | "acquire" | "release" | "acq_rel" | "seq_cst"))
        {
            self.pos += 1;
        }
    }

    /// Try the folded constant-gep form `( T , ptr @g , iN K )` with the
    /// opening paren as the next token. On success the group is consumed; on
    /// any mismatch the position is restored (`None`) so the caller can skip
    /// the group opaquely.
    fn try_const_gep(&mut self) -> Option<LValue> {
        let start = self.pos;
        let mut attempt = || -> Option<LValue> {
            self.expect_punct('(').ok()?;
            let elem = self.ltype().ok()?;
            self.expect_punct(',').ok()?;
            let _pty = self.ltype().ok()?; // `ptr`
            let name = match self.bump() {
                Tok::Global(n) => n,
                _ => return None,
            };
            self.expect_punct(',').ok()?;
            let _ity = self.ltype().ok()?; // `iN`
            let index = match self.bump() {
                Tok::Int(k) => k,
                _ => return None,
            };
            // Multi-index constant geps are not folded here — opaque.
            if !matches!(self.peek(), Tok::Punct(')')) {
                return None;
            }
            self.pos += 1;
            Some(LValue::GlobalOff { name, elem, index })
        };
        match attempt() {
            Some(v) => Some(v),
            None => {
                self.pos = start;
                None
            }
        }
    }

    /// `, align N` if present.
    fn maybe_align(&mut self) -> Option<u32> {
        if matches!(self.peek(), Tok::Punct(','))
            && matches!(self.peek2(), Tok::Word(w) if w == "align")
        {
            self.pos += 2; // ',' 'align'
            if let Tok::Int(n) = self.bump() {
                return Some(n as u32);
            }
        }
        None
    }

    /// Scan the current instruction's trailing metadata (without consuming — the
    /// block loop's `skip_to_eol` drops it) for `!align !N`, returning the node's
    /// value from the pre-scanned integer-metadata table.
    fn peek_load_align_meta(&self) -> Option<u32> {
        let mut i = self.pos;
        while let Some(t) = self.toks.get(i) {
            match t {
                Tok::Newline | Tok::Eof => break,
                Tok::Punct('!') => {
                    if matches!(self.toks.get(i + 1), Some(Tok::Word(w)) if w == "align") {
                        if let Some(Tok::Int(n)) = self.toks.get(i + 3) {
                            return u32::try_from(*n)
                                .ok()
                                .and_then(|id| self.meta_ints.get(&id))
                                .and_then(|v| u32::try_from(*v).ok());
                        }
                    }
                    i += 1;
                }
                _ => i += 1,
            }
        }
        None
    }

    /// Advance past any run of newline tokens.
    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline) {
            self.pos += 1;
        }
    }

    /// Parse a parameter's attributes (up to its `%name` / `,` / `)`),
    /// capturing the memory-safety-relevant ones and skipping the rest.
    #[allow(clippy::type_complexity)]
    fn param_attrs(&mut self) -> Result<(Option<u64>, Option<u32>, bool, bool, Option<LType>)> {
        let mut deref = None;
        let mut align = None;
        let mut readonly = false;
        let mut writeonly = false;
        let mut abi_buf = None;
        loop {
            match self.peek() {
                Tok::Local(_) | Tok::Punct(',') | Tok::Punct(')') | Tok::Eof => break,
                Tok::Punct('(') => self.skip_balanced('(', ')')?,
                Tok::Word(w) => {
                    let w = w.clone();
                    self.pos += 1;
                    match w.as_str() {
                        "align" => {
                            if let Tok::Int(n) = *self.peek() {
                                align = Some(n as u32);
                                self.pos += 1;
                            }
                        }
                        "dereferenceable" => deref = Some(self.paren_u64()?),
                        // `sret(T)` / `byval(T)`: a caller-provided buffer of
                        // `sizeof(T)` bytes — capture the type for a size contract.
                        // An unparseable payload (e.g. a named struct type) falls
                        // back to skipping: no contract, never a dropped function.
                        "sret" | "byval" if matches!(self.peek(), Tok::Punct('(')) => {
                            let open = self.pos;
                            self.pos += 1; // '('
                            match self.ltype() {
                                Ok(ty) if matches!(self.peek(), Tok::Punct(')')) => {
                                    self.pos += 1; // ')'
                                    abi_buf = Some(ty);
                                }
                                _ => {
                                    self.pos = open;
                                    self.skip_balanced('(', ')')?;
                                }
                            }
                        }
                        "readonly" => readonly = true,
                        "writeonly" => writeonly = true,
                        // `dereferenceable_or_null`, `byval(T)`, `captures(...)`,
                        // etc.: skip, including any parenthesized payload.
                        _ => {
                            if matches!(self.peek(), Tok::Punct('(')) {
                                self.skip_balanced('(', ')')?;
                            }
                        }
                    }
                }
                _ => self.pos += 1,
            }
        }
        Ok((deref, align, readonly, writeonly, abi_buf))
    }

    /// Skip a call argument's attributes up to its operand. Crucially, `align
    /// N` is skipped as a *pair* (so the alignment value `N` is not mistaken for
    /// the operand), and parenthesized attributes are skipped balanced.
    fn skip_arg_attrs(&mut self) -> Result<Option<u64>> {
        let mut deref = None;
        loop {
            match self.peek() {
                // The operand: a register, global, integer/float, or aggregate const.
                Tok::Local(_)
                | Tok::Global(_)
                | Tok::Int(_)
                | Tok::Float(_)
                | Tok::Punct(',')
                | Tok::Punct(')')
                | Tok::Punct('<')
                | Tok::Punct('[')
                | Tok::Punct('{')
                | Tok::Eof => break,
                // A value has begun: a literal, or a constant-expression operator
                // (whose `(…)` body would otherwise be mistaken for an attribute).
                Tok::Word(w)
                    if matches!(
                        w.as_str(),
                        "null"
                            | "undef"
                            | "poison"
                            | "true"
                            | "false"
                            | "zeroinitializer"
                            | "getelementptr"
                            | "bitcast"
                            | "inttoptr"
                            | "ptrtoint"
                            | "addrspacecast"
                            | "trunc"
                            | "zext"
                            | "sext"
                            | "blockaddress"
                    ) =>
                {
                    break
                }
                Tok::Word(w) if w == "align" => {
                    self.pos += 1;
                    if matches!(self.peek(), Tok::Int(_)) {
                        self.pos += 1;
                    }
                }
                // `dereferenceable(N)`: capture N — an authoritative byte-size bound on
                // this operand. (`dereferenceable_or_null` is deliberately excluded: it
                // permits a null pointer, so it is not a size guarantee.)
                Tok::Word(w) if w == "dereferenceable" => {
                    self.pos += 1;
                    if matches!(self.peek(), Tok::Punct('(')) {
                        if let Ok(n) = self.paren_u64() {
                            deref = Some(deref.map_or(n, |d: u64| d.max(n)));
                        }
                    }
                }
                Tok::Punct('(') => self.skip_balanced('(', ')')?,
                _ => self.pos += 1,
            }
        }
        Ok(deref)
    }

    /// Parse `( N )` and return `N`.
    fn paren_u64(&mut self) -> Result<u64> {
        self.expect_punct('(')?;
        let n = self.int()?;
        self.expect_punct(')')?;
        Ok(n.max(0) as u64)
    }

    /// Skip attribute/linkage words (including parenthesized ones like
    /// `dereferenceable(32)`) up to the next token that can begin a type.
    fn skip_to_type(&mut self) -> Result<()> {
        while !is_type_start(self.peek()) && !matches!(self.peek(), Tok::Eof | Tok::Punct('{')) {
            if matches!(self.peek(), Tok::Punct('(')) {
                self.skip_balanced('(', ')')?;
            } else {
                self.pos += 1;
            }
        }
        Ok(())
    }

    /// Skip a balanced bracketed group, assuming the opener is the next token.
    fn skip_balanced(&mut self, open: char, close: char) -> Result<()> {
        self.expect_punct(open)?;
        let mut depth = 1;
        while depth > 0 {
            match self.bump() {
                Tok::Punct(c) if c == open => depth += 1,
                Tok::Punct(c) if c == close => depth -= 1,
                Tok::Eof => return Err(Error::parse("unbalanced brackets")),
                _ => {}
            }
        }
        Ok(())
    }

    /// Advance to the end of the current line (consuming the newline). Used to
    /// drop trailing instruction metadata (`, !dbg !5`) and to skip top-level
    /// directive lines (`source_filename`, `target`, `attributes`, `!…`, …).
    fn skip_to_eol(&mut self) {
        while !matches!(self.peek(), Tok::Newline | Tok::Eof) {
            self.pos += 1;
        }
        if matches!(self.peek(), Tok::Newline) {
            self.pos += 1;
        }
    }

    /// Skip a function that failed to parse: extract its `@name` and advance
    /// past its `{ … }` body. Assumes the next token is `define`.
    fn recover_function(&mut self) -> String {
        self.pos += 1; // `define`
        let mut name = "<unnamed>".to_string();
        while !matches!(self.peek(), Tok::Eof | Tok::Punct('{')) {
            if let Tok::Global(g) = self.peek() {
                name = g.clone();
                break;
            }
            self.pos += 1;
        }
        while !matches!(self.peek(), Tok::Punct('{') | Tok::Eof) {
            self.pos += 1;
        }
        if matches!(self.peek(), Tok::Punct('{')) {
            let _ = self.skip_balanced('{', '}');
        }
        name
    }

    /// Parse a top-level global definition line; `None` (with the line
    /// consumed) when it is not a sizable definition (alias, ifunc, or an
    /// unsupported type).
    fn global_def(&mut self) -> Option<LGlobal> {
        let name = match self.bump() {
            Tok::Global(n) => n,
            _ => unreachable!("caller matched Tok::Global"),
        };
        self.pos += 1; // '='
                       // Skip linkage/visibility/attribute words up to `global`/`constant`.
        let writable = loop {
            match self.peek() {
                Tok::Word(w) if w == "constant" => {
                    self.pos += 1;
                    break false;
                }
                Tok::Word(w) if w == "global" => {
                    self.pos += 1;
                    break true;
                }
                // `alias`/`ifunc` (no sizable storage of their own) or anything
                // unexpected: skip the line.
                Tok::Word(w) if w == "alias" || w == "ifunc" => {
                    self.skip_to_eol();
                    return None;
                }
                Tok::Word(_) => self.pos += 1,
                Tok::Punct('(') => {
                    // e.g. `thread_local(localdynamic)`.
                    if self.skip_balanced('(', ')').is_err() {
                        self.skip_to_eol();
                        return None;
                    }
                }
                _ => {
                    self.skip_to_eol();
                    return None;
                }
            }
        };
        let snapshot = self.pos;
        let (ty, packed) = match self.ltype() {
            Ok(t) => (t, false),
            // `<{ … }>` — a packed struct (ltype rejects it in instruction
            // contexts). Its exact size is the unpadded field sum, so a global
            // of this shape is still sizable.
            Err(_) => {
                self.pos = snapshot;
                match self.packed_struct_type() {
                    Some(fields) => (LType::Struct(fields), true),
                    None => {
                        self.skip_to_eol();
                        return None;
                    }
                }
            }
        };
        // For a *constant* global, walk the initializer to collect symbol-pointer
        // fields (offset → name) for indirect-call devirtualisation. Purely a
        // side analysis: snapshot the position, try to track the layout exactly,
        // and restore — the `, align N` scan below runs from the same point
        // regardless. A tracking failure discards *all* fields for this global
        // (an imprecise offset would be unsound), so recovery is silent.
        let init_start = self.pos;
        let mut fn_ptrs = Vec::new();
        if !writable {
            let mut collected = Vec::new();
            if self.scan_init_value(&ty, packed, 0, &mut collected).is_ok() {
                fn_ptrs = collected;
            }
        }
        self.pos = init_start;
        // Scan the initializer tail for `, align N`, then consume the line.
        let mut align = 1u32;
        while !matches!(self.peek(), Tok::Newline | Tok::Eof) {
            if matches!(self.peek(), Tok::Word(w) if w == "align") {
                if let Tok::Int(n) = *self.peek2() {
                    align = n as u32;
                }
            }
            self.pos += 1;
        }
        Some(LGlobal {
            name,
            ty,
            writable,
            align,
            packed,
            fn_ptrs,
        })
    }

    /// Walk a constant initializer *value* whose type is `ty` (already resolved),
    /// starting at byte `base`, appending `(offset, symbol)` for each `@symbol`
    /// address it contains. `outer_packed` is `ty`'s packed-ness (only meaningful
    /// for the top-level packed-struct value). Returns `Err` if the layout could
    /// not be tracked exactly, so the caller discards partial results.
    fn scan_init_value(
        &mut self,
        ty: &LType,
        outer_packed: bool,
        base: u64,
        out: &mut Vec<(u64, String)>,
    ) -> Result<()> {
        match ty {
            LType::Struct(_) | LType::PackedStruct(_) => {
                if self.eat_aggregate_zero() {
                    return Ok(());
                }
                let packed = outer_packed || matches!(ty, LType::PackedStruct(_));
                let angled = matches!(self.peek(), Tok::Punct('<'));
                if angled {
                    self.expect_punct('<')?;
                }
                self.expect_punct('{')?;
                let mut off = base;
                if !matches!(self.peek(), Tok::Punct('}')) {
                    loop {
                        let ety = self.ltype()?;
                        let a = if packed { 1 } else { ltype_align(&ety)? };
                        off =
                            align_up(off, a).ok_or_else(|| Error::unsupported("init overflow"))?;
                        let ep = matches!(ety, LType::PackedStruct(_));
                        self.scan_init_value(&ety, ep, off, out)?;
                        off = off
                            .checked_add(ltype_size(&ety)?)
                            .ok_or_else(|| Error::unsupported("init overflow"))?;
                        if matches!(self.peek(), Tok::Punct(',')) {
                            self.pos += 1;
                        } else {
                            break;
                        }
                    }
                }
                self.expect_punct('}')?;
                if angled {
                    self.expect_punct('>')?;
                }
                Ok(())
            }
            LType::Array(elem, _) | LType::Vector(elem, _) => {
                if self.eat_aggregate_zero() {
                    return Ok(());
                }
                let close = if matches!(ty, LType::Vector(..)) {
                    '>'
                } else {
                    ']'
                };
                let open = if matches!(ty, LType::Vector(..)) {
                    '<'
                } else {
                    '['
                };
                // A `c"…"` string body is not a bracketed element list: skip it
                // exactly (no pointer fields), consuming the string token.
                if !matches!(self.peek(), Tok::Punct(p) if *p == open) {
                    let _ = self.value()?;
                    return Ok(());
                }
                self.expect_punct(open)?;
                let stride = align_up(ltype_size(elem)?, ltype_align(elem)?)
                    .ok_or_else(|| Error::unsupported("init overflow"))?;
                let mut idx: u64 = 0;
                if !matches!(self.peek(), Tok::Punct(p) if *p == close) {
                    loop {
                        let ety = self.ltype()?;
                        let ep = matches!(ety, LType::PackedStruct(_));
                        let off = base
                            .checked_add(
                                idx.checked_mul(stride)
                                    .ok_or_else(|| Error::unsupported("init overflow"))?,
                            )
                            .ok_or_else(|| Error::unsupported("init overflow"))?;
                        self.scan_init_value(&ety, ep, off, out)?;
                        idx += 1;
                        if matches!(self.peek(), Tok::Punct(',')) {
                            self.pos += 1;
                        } else {
                            break;
                        }
                    }
                }
                self.expect_punct(close)?;
                Ok(())
            }
            // A scalar element: consume its value; a symbol address is a field.
            _ => {
                let v = self.value()?;
                if let LValue::Global(n) = v {
                    out.push((base, n));
                }
                Ok(())
            }
        }
    }

    /// Consume a whole-aggregate `zeroinitializer`/`undef`/`poison` value if the
    /// current token is one (no pointer fields in it); return whether it did.
    fn eat_aggregate_zero(&mut self) -> bool {
        self.eat_word("zeroinitializer") || self.eat_word("undef") || self.eat_word("poison")
    }

    /// Parse `<{ T, T, … }>` (a packed struct type), resolving named fields;
    /// restores the position on any mismatch.
    fn packed_struct_type(&mut self) -> Option<Vec<LType>> {
        let start = self.pos;
        let mut attempt = || -> Option<Vec<LType>> {
            self.expect_punct('<').ok()?;
            self.expect_punct('{').ok()?;
            let fields = self.struct_fields().ok()?;
            self.expect_punct('>').ok()?;
            fields
                .iter()
                .map(|f| self.resolve_named(f, 0).ok())
                .collect()
        };
        match attempt() {
            Some(f) => Some(f),
            None => {
                self.pos = start;
                None
            }
        }
    }

    fn function(&mut self) -> Result<LFunc> {
        self.expect_word("define")?;
        // Linkage: `internal`/`private` mean the function is invisible outside
        // this module — captured, because it licenses call-site contract
        // synthesis. Everything else up to the return type is skipped
        // (`dso_local`, `noundef`, `signext`, `dereferenceable(N)`, …).
        let internal = matches!(self.peek(), Tok::Word(w) if w == "internal" || w == "private");
        self.skip_to_type()?;
        let ret = self.ltype()?;
        let name = self.global()?;
        self.expect_punct('(')?;
        let mut params = Vec::new();
        if !matches!(self.peek(), Tok::Punct(')')) {
            loop {
                // A variadic marker `...` is always the final "parameter" and
                // carries nothing for the analysis (the fixed parameters are what
                // is checked) — consume it and end the list, so variadic functions
                // (`printf`-style wrappers, logging) are analyzed rather than
                // dropped whole.
                if matches!(self.peek(), Tok::Word(w) if w == "...") {
                    self.pos += 1;
                    break;
                }
                let ty = self.ltype()?;
                let (deref, align, readonly, writeonly, abi_buf) = self.param_attrs()?;
                let name = if let Tok::Local(_) = self.peek() {
                    self.local()?
                } else {
                    String::new() // unnamed parameter
                };
                params.push(LParam {
                    ty,
                    name,
                    deref,
                    abi_buf,
                    align,
                    readonly,
                    writeonly,
                });
                if matches!(self.peek(), Tok::Punct(',')) {
                    self.pos += 1;
                } else {
                    break;
                }
            }
        }
        self.expect_punct(')')?;
        // Skip everything up to the opening brace (attributes, `unnamed_addr`,
        // `#0`, …), capturing the `!dbg !N` DISubprogram id along the way.
        let mut dbg = None;
        while !matches!(self.peek(), Tok::Punct('{') | Tok::Eof) {
            if matches!(self.peek(), Tok::Punct('!'))
                && matches!(self.peek2(), Tok::Word(w) if w == "dbg")
            {
                if let Some(Tok::Int(n)) = self.toks.get(self.pos + 3) {
                    dbg = u32::try_from(*n).ok();
                }
            }
            self.pos += 1;
        }
        self.expect_punct('{')?;
        let blocks = self.blocks(params.len())?;
        self.expect_punct('}')?;
        Ok(LFunc {
            name,
            ret,
            params,
            blocks,
            internal,
            dbg,
        })
    }

    fn blocks(&mut self, param_count: usize) -> Result<Vec<LBlock>> {
        let mut blocks = Vec::new();
        let mut auto = 0;
        loop {
            self.skip_newlines();
            if matches!(self.peek(), Tok::Punct('}') | Tok::Eof) {
                break;
            }
            // Optional block label: `name:` or `N:`.
            let labeled = matches!(self.peek(), Tok::Word(_) | Tok::Int(_))
                && matches!(self.peek2(), Tok::Punct(':'));
            let label = if labeled {
                let l = match self.bump() {
                    Tok::Word(w) => w,
                    Tok::Int(n) => n.to_string(),
                    _ => unreachable!(),
                };
                self.expect_punct(':')?;
                l
            } else if blocks.is_empty() {
                // The *entry* block is often unlabeled. LLVM still assigns it an
                // implicit value number — the next after the (numbered) parameters
                // — and a `phi` in a later block can name it as a predecessor
                // (`[ v, %<n> ]`). Use that number as its label so the reference
                // resolves; otherwise the phi dangles and the whole function is
                // dropped (it did, for any `goto`/loop entry that a phi refers to).
                param_count.to_string()
            } else {
                let l = format!("__bb{auto}");
                auto += 1;
                l
            };

            let mut phis = Vec::new();
            let mut insts = Vec::new();
            let term = loop {
                self.skip_newlines();
                // A `-g` debug record (`#dbg_declare(…)` / `#dbg_value(…)`) is
                // interleaved in the instruction stream but is not an
                // instruction — skip the whole line.
                if matches!(self.peek(), Tok::Punct('#')) {
                    self.skip_to_eol();
                    continue;
                }
                if let Some(t) = self.try_terminator()? {
                    self.skip_to_eol(); // drop trailing metadata (`, !dbg !N`)
                    break t;
                }
                match self.instruction()? {
                    InstOrPhi::Phi(p) => phis.push(p),
                    InstOrPhi::Inst(i) => insts.push(i),
                }
                self.skip_to_eol(); // drop trailing metadata
            };
            blocks.push(LBlock {
                label,
                phis,
                insts,
                term,
            });
        }
        Ok(blocks)
    }

    fn try_terminator(&mut self) -> Result<Option<LTerm>> {
        // `invoke` is a terminator that may bind a result: `%dst = invoke …`.
        // Detect that form (3-token lookahead) and consume the `%dst =` prefix.
        let invoke_dst = if matches!(self.peek(), Tok::Local(_))
            && matches!(self.peek2(), Tok::Punct('='))
            && matches!(self.toks.get(self.pos + 2), Some(Tok::Word(w)) if w == "invoke" || w == "callbr")
        {
            let d = self.local()?;
            self.expect_punct('=')?;
            Some(d)
        } else {
            None
        };
        let kw = match self.peek() {
            Tok::Word(w) => w.clone(),
            _ => return Ok(None),
        };
        if kw == "invoke" {
            {
                self.pos += 1;
                self.skip_to_type()?;
                let ret = self.ltype()?;
                let callee = self.callee_name()?;
                self.expect_punct('(')?;
                let mut args = Vec::new();
                if !matches!(self.peek(), Tok::Punct(')')) {
                    loop {
                        let _ty = self.ltype()?;
                        self.skip_arg_attrs()?;
                        args.push(self.value()?);
                        if matches!(self.peek(), Tok::Punct(',')) {
                            self.pos += 1;
                        } else {
                            break;
                        }
                    }
                }
                self.expect_punct(')')?;
                // Skip function attributes / newlines up to the `to` clause (which
                // continues onto the next line).
                while !matches!(self.peek(), Tok::Word(w) if w == "to")
                    && !matches!(self.peek(), Tok::Eof | Tok::Punct('}'))
                {
                    self.pos += 1;
                }
                self.expect_word("to")?;
                self.expect_word("label")?;
                let ok = self.local()?;
                self.expect_word("unwind")?;
                self.expect_word("label")?;
                let cleanup = self.local()?;
                return Ok(Some(LTerm::Invoke {
                    dst: invoke_dst,
                    ret,
                    callee,
                    args,
                    ok,
                    cleanup,
                }));
            }
        }
        if kw == "callbr" {
            self.pos += 1;
            self.skip_to_type()?;
            let _ret = self.ltype()?;
            // Callee is inline asm (`asm "…", "…"`) or, rarely, a value — skip up to
            // the argument list either way.
            while !matches!(self.peek(), Tok::Punct('(') | Tok::Eof | Tok::Punct('}')) {
                self.pos += 1;
            }
            self.skip_balanced('(', ')')?;
            // Attributes, then `to label %ft [label %t1, …]`.
            while !matches!(self.peek(), Tok::Word(w) if w == "to")
                && !matches!(self.peek(), Tok::Eof | Tok::Punct('}'))
            {
                self.pos += 1;
            }
            self.expect_word("to")?;
            self.expect_word("label")?;
            let mut targets = vec![self.local()?];
            // The indirect label list `[label %t1, label %t2, …]`.
            if matches!(self.peek(), Tok::Punct('[')) {
                self.pos += 1;
                while !matches!(self.peek(), Tok::Punct(']') | Tok::Eof) {
                    if self.eat_word("label") {
                        targets.push(self.local()?);
                    } else {
                        self.pos += 1; // a comma or other separator
                    }
                }
                self.expect_punct(']')?;
            }
            return Ok(Some(LTerm::CallBr {
                dst: invoke_dst,
                targets,
            }));
        }
        match kw.as_str() {
            "ret" => {
                self.pos += 1;
                let ty = self.ltype()?;
                if ty == LType::Void {
                    Ok(Some(LTerm::Ret(None)))
                } else {
                    Ok(Some(LTerm::Ret(Some(self.value()?))))
                }
            }
            "br" => {
                self.pos += 1;
                if self.eat_word("label") {
                    Ok(Some(LTerm::Br(self.local()?)))
                } else {
                    let _ty = self.ltype()?; // i1
                    let cond = self.value()?;
                    self.expect_punct(',')?;
                    self.expect_word("label")?;
                    let t = self.local()?;
                    self.expect_punct(',')?;
                    self.expect_word("label")?;
                    let f = self.local()?;
                    Ok(Some(LTerm::CondBr(cond, t, f)))
                }
            }
            "switch" => {
                self.pos += 1;
                let LType::Int(width) = self.ltype()? else {
                    return Err(Error::unsupported("switch on a non-integer scrutinee"));
                };
                let value = self.value()?;
                self.expect_punct(',')?;
                self.expect_word("label")?;
                let default = self.local()?;
                self.expect_punct('[')?;
                let mut cases = Vec::new();
                loop {
                    // The case table spans lines (`[` newline `i64 0, label %bb` …).
                    self.skip_newlines();
                    if matches!(self.peek(), Tok::Punct(']')) {
                        break;
                    }
                    let _cty = self.ltype()?; // each case repeats the scrutinee's int type
                    let cv = match self.value()? {
                        LValue::Int(n) => n,
                        other => {
                            return Err(Error::unsupported(format!(
                                "non-constant switch case value {other:?}"
                            )))
                        }
                    };
                    self.expect_punct(',')?;
                    self.expect_word("label")?;
                    cases.push((cv, self.local()?));
                }
                self.expect_punct(']')?;
                Ok(Some(LTerm::Switch {
                    value,
                    width,
                    default,
                    cases,
                }))
            }
            "unreachable" => {
                self.pos += 1;
                Ok(Some(LTerm::Unreachable))
            }
            "resume" => {
                // Re-raise an in-flight unwind — control leaves the function without
                // returning normally, so there is no successor.
                self.pos += 1;
                let _ty = self.ltype()?;
                let _ = self.value();
                Ok(Some(LTerm::Unreachable))
            }
            _ => Ok(None),
        }
    }

    /// Consume a `landingpad`'s clauses (`cleanup` / `catch T v` / `filter T v`),
    /// which may continue onto following lines. Only advances `pos` over an actual
    /// clause, so a following instruction is left intact for the block loop.
    fn skip_landingpad_clauses(&mut self) {
        loop {
            let mut j = self.pos;
            while matches!(self.toks.get(j), Some(Tok::Newline)) {
                j += 1;
            }
            match self.toks.get(j) {
                Some(Tok::Word(w)) if w == "cleanup" => self.pos = j + 1,
                Some(Tok::Word(w)) if w == "catch" || w == "filter" => {
                    self.pos = j + 1;
                    let _ = self.ltype();
                    let _ = self.value();
                }
                _ => break,
            }
        }
    }

    fn instruction(&mut self) -> Result<InstOrPhi> {
        // Assignment form: `%dst = <op> ...`.
        if matches!(self.peek(), Tok::Local(_)) && matches!(self.peek2(), Tok::Punct('=')) {
            let dst = self.local()?;
            self.expect_punct('=')?;
            return self.rhs(Some(dst));
        }
        // Void form: `store ...` / `call ...`.
        self.rhs(None)
    }

    fn rhs(&mut self, dst: Option<String>) -> Result<InstOrPhi> {
        // `tail` / `musttail` / `notail` prefix a `call`.
        while self.eat_word("tail") || self.eat_word("musttail") || self.eat_word("notail") {}
        let op = match self.peek() {
            Tok::Word(w) => w.clone(),
            other => return Err(Error::parse(format!("expected an opcode, found {other:?}"))),
        };
        self.pos += 1;
        let need_dst = || {
            dst.clone()
                .ok_or_else(|| Error::parse(format!("`{op}` needs a destination")))
        };

        let inst = match op.as_str() {
            "alloca" => {
                let ty = self.ltype()?;
                let align = self.maybe_align().unwrap_or(0);
                LInst::Alloca {
                    dst: need_dst()?,
                    ty,
                    align,
                }
            }
            "load" => {
                // `atomic`/`volatile` qualifiers don't change the memory-safety
                // obligations (the analysis models sequential memory, as does the
                // Miri oracle); the access itself must still be checked.
                let atomic = self.skip_memory_qualifiers();
                let ty = self.ltype()?;
                self.expect_punct(',')?;
                let _pty = self.ltype()?;
                let ptr = self.value()?;
                self.skip_atomic_ordering();
                let align = self.maybe_align().unwrap_or(0);
                // `!align !N` metadata states the *loaded pointer's* alignment — an
                // LLVM guarantee independent of the pointee type, so it is recorded
                // and later folded into the loaded reference's alignment.
                let align_meta = self.peek_load_align_meta();
                LInst::Load {
                    dst: need_dst()?,
                    ty,
                    ptr,
                    align,
                    align_meta,
                    atomic,
                }
            }
            "store" => {
                let atomic = self.skip_memory_qualifiers();
                let ty = self.ltype()?;
                let val = self.value()?;
                self.expect_punct(',')?;
                let _pty = self.ltype()?;
                let ptr = self.value()?;
                self.skip_atomic_ordering();
                let align = self.maybe_align().unwrap_or(0);
                LInst::Store {
                    ty,
                    val,
                    ptr,
                    align,
                    atomic,
                }
            }
            "getelementptr" => self.gep(need_dst()?)?,
            "icmp" => {
                // `samesign` is an optimization-hint flag, not a predicate.
                let _ = self.eat_word("samesign");
                let pred = self.pred()?;
                let ty = self.ltype()?;
                let a = self.value()?;
                self.expect_punct(',')?;
                let b = self.value()?;
                LInst::Icmp {
                    dst: need_dst()?,
                    pred,
                    ty,
                    a,
                    b,
                }
            }
            "extractvalue" => {
                let _agg_ty = self.ltype()?;
                let agg = self.value()?;
                self.expect_punct(',')?;
                let index = self.int()? as u32;
                // Skip nested indices (`, j, k`); the checked-arith tuple is flat.
                while matches!(self.peek(), Tok::Punct(',')) {
                    self.pos += 1;
                    let _ = self.int();
                }
                LInst::ExtractValue {
                    dst: need_dst()?,
                    agg,
                    index,
                }
            }
            "landingpad" => {
                let _ty = self.ltype()?;
                self.skip_landingpad_clauses();
                LInst::Opaque { dst: need_dst()? }
            }
            "select" => {
                // `select i1 %c, T %a, T %b` — kept as `LInst::Select` so a pointer
                // select is a provenance join (each alternative proved under its guard)
                // and a scalar select an `ite`.
                let _cty = self.ltype()?;
                let cond = self.value()?;
                self.expect_punct(',')?;
                let _aty = self.ltype()?;
                let then_val = self.value()?;
                self.expect_punct(',')?;
                let _bty = self.ltype()?;
                let else_val = self.value()?;
                LInst::Select { dst: need_dst()?, cond, then_val, else_val }
            }
            "insertvalue" => {
                // `insertvalue AGG %agg, T %val, idx…` — the resulting aggregate is
                // modelled opaquely (its fields are recovered by `extractvalue` when
                // it matters, e.g. checked arithmetic; here it is an exception tuple).
                let _agg_ty = self.ltype()?;
                let _agg = self.value()?;
                self.expect_punct(',')?;
                let _val_ty = self.ltype()?;
                let _val = self.value()?;
                self.expect_punct(',')?;
                let _index = self.int()?;
                while matches!(self.peek(), Tok::Punct(',')) {
                    self.pos += 1;
                    let _ = self.int();
                }
                LInst::Opaque { dst: need_dst()? }
            }
            "call" => self.call(dst)?,
            "phi" => {
                let phi = self.phi(need_dst()?)?;
                return Ok(InstOrPhi::Phi(phi));
            }
            "atomicrmw" => {
                let _ = self.eat_word("volatile");
                // The RMW operator (`add`, `xchg`, `umax`, …).
                let _op = match self.bump() {
                    Tok::Word(w) => w,
                    other => {
                        return Err(Error::parse(format!(
                            "expected atomicrmw op, found {other:?}"
                        )))
                    }
                };
                let _pty = self.ltype()?; // `ptr`
                let ptr = self.value()?;
                self.expect_punct(',')?;
                let ty = self.ltype()?;
                let _val = self.value()?;
                self.skip_atomic_ordering();
                LInst::AtomicRmw {
                    dst: need_dst()?,
                    ty,
                    ptr,
                    tuple: false,
                }
            }
            "cmpxchg" => {
                while self.eat_word("weak") || self.eat_word("volatile") {}
                let _pty = self.ltype()?; // `ptr`
                let ptr = self.value()?;
                self.expect_punct(',')?;
                let ty = self.ltype()?;
                let _cmp = self.value()?;
                self.expect_punct(',')?;
                let _nty = self.ltype()?;
                let _new = self.value()?;
                self.skip_atomic_ordering(); // consumes both orderings
                LInst::AtomicRmw {
                    dst: need_dst()?,
                    ty,
                    ptr,
                    tuple: true,
                }
            }
            "insertelement" | "extractelement" | "shufflevector" | "freeze" => {
                // Vector shuffling and `freeze` produce values with no
                // memory-safety content of their own — opaque; the operands are
                // consumed by the block loop's `skip_to_eol`.
                LInst::Opaque { dst: need_dst()? }
            }
            other if is_float_op(other) => {
                // Float arithmetic/casts/compares produce an opaque scalar. The
                // operands are left for `skip_to_eol` (run after every
                // instruction) to consume — no float value is ever modelled.
                LInst::Opaque { dst: need_dst()? }
            }
            other => {
                if let Some(bop) = bin_op(other) {
                    // Skip flags like `nuw`, `nsw`, `exact`, `disjoint`.
                    while matches!(self.peek(), Tok::Word(w) if matches!(w.as_str(), "nuw" | "nsw" | "exact" | "disjoint"))
                    {
                        self.pos += 1;
                    }
                    let ty = self.ltype()?;
                    let a = self.value()?;
                    self.expect_punct(',')?;
                    let b = self.value()?;
                    LInst::Bin {
                        dst: need_dst()?,
                        op: bop,
                        ty,
                        a,
                        b,
                    }
                } else if let Some(cop) = cast_op(other) {
                    // Skip cast flags (`trunc nuw`, `trunc nsw`, `zext nneg`).
                    while matches!(self.peek(), Tok::Word(w) if matches!(w.as_str(), "nuw" | "nsw" | "nneg"))
                    {
                        self.pos += 1;
                    }
                    let _from = self.ltype()?;
                    let val = self.value()?;
                    self.expect_word("to")?;
                    let to = self.ltype()?;
                    LInst::Cast {
                        dst: need_dst()?,
                        op: cop,
                        val,
                        to,
                    }
                } else {
                    return Err(Error::unsupported(format!("instruction `{other}`")));
                }
            }
        };
        Ok(InstOrPhi::Inst(inst))
    }

    fn gep(&mut self, dst: String) -> Result<LInst> {
        // Flags: `inbounds`, `nuw`, `nusw` in any combination.
        while self.eat_word("inbounds") || self.eat_word("nuw") || self.eat_word("nusw") {}
        let base_ty = self.ltype()?;
        self.expect_punct(',')?;
        let _pty = self.ltype()?;
        let base = self.value()?;
        // Index list. Stop at a trailing `, !dbg …` (a `,` not followed by a
        // type) rather than mistaking the metadata for another index.
        let mut indices = Vec::new();
        while matches!(self.peek(), Tok::Punct(',')) && is_type_start(self.peek2()) {
            self.pos += 1;
            let _ity = self.ltype()?;
            indices.push(self.value()?);
        }
        // A single index is plain pointer arithmetic over the base type. Anything
        // with a navigation below the first level (nested struct fields / array
        // indices, constant *or* variable) becomes a `GepChain`, resolved to a
        // PtrOffset chain at lowering by walking the aggregate type.
        match indices.as_slice() {
            [idx] => Ok(LInst::Gep {
                dst,
                elem: base_ty.clone(),
                base,
                index: idx.clone(),
            }),
            _ if matches!(
                base_ty,
                LType::Struct(_) | LType::PackedStruct(_) | LType::Array(..)
            ) =>
            {
                Ok(LInst::GepChain {
                    dst,
                    agg_ty: base_ty.clone(),
                    base,
                    indices,
                })
            }
            _ => Err(Error::unsupported(
                "getelementptr with a navigation into a non-aggregate",
            )),
        }
    }

    /// The callee of a `call`/`invoke`: a direct `@name`, or — for an *indirect*
    /// call through a function pointer — a `%local`. The indirect case maps to a
    /// name no real global can have; it never resolves to a known function, so
    /// the lowering emits `Callee::Symbol` and the engine applies the sound
    /// unknown-callee semantics (heap/liveness havoc, no refutation through it).
    fn callee_name(&mut self) -> Result<String> {
        match self.peek() {
            Tok::Local(n) => {
                let name = format!("<indirect via %{n}>");
                self.pos += 1;
                Ok(name)
            }
            _ => self.global(),
        }
    }

    fn call(&mut self, dst: Option<String>) -> Result<LInst> {
        // Skip calling-convention / tail / return-attribute words.
        while self.eat_word("tail") || self.eat_word("notail") || self.eat_word("musttail") {}
        self.skip_to_type()?;
        let ret = self.ltype()?;
        // A variadic (or explicitly-typed) call prints the *full function type*
        // before the callee — `call i64 (i32, ...) @f(args)` — with an optional
        // trailing `*` in pre-opaque-pointer IR. Skip that parenthesized signature
        // so the callee parses; without this the whole caller was dropped (and
        // with it every contract its call sites would have synthesized).
        if matches!(self.peek(), Tok::Punct('(')) {
            self.skip_balanced('(', ')')?;
            if matches!(self.peek(), Tok::Punct('*')) {
                self.pos += 1;
            }
        }
        // Inline assembly: `<ret> asm [sideeffect|alignstack|inteldialect|unwind]
        // "template", "constraints" (args)`. Model it as an opaque, memory-clobbering
        // call (the callee name resolves to no function, so the lowering emits
        // `Callee::Symbol` → the sound unknown-callee havoc). Without this the `asm`
        // token failed the `@name` parse and the whole function was dropped — and
        // kernel C is saturated with inline asm.
        let callee = if matches!(self.peek(), Tok::Word(w) if w == "asm") {
            self.pos += 1;
            while matches!(self.peek(), Tok::Word(w)
                if matches!(w.as_str(), "sideeffect" | "alignstack" | "inteldialect" | "unwind"))
            {
                self.pos += 1;
            }
            // The template and constraint strings (each a quoted `Word`), separated
            // by a comma; tolerate either being absent.
            if matches!(self.peek(), Tok::Word(_)) {
                self.pos += 1; // template (not needed to decide the memory effect)
            }
            let mut constraints = String::new();
            if matches!(self.peek(), Tok::Punct(',')) {
                self.pos += 1;
                if let Tok::Word(c) = self.peek() {
                    constraints = c.clone();
                    self.pos += 1;
                }
            }
            // Decide the memory effect from the constraint string. A "memory" clobber
            // or an OUTPUT memory operand (`=m`/`+m`/`=*m`/`=&m`, …) means the asm may
            // write memory we track → the sound unknown-callee havoc (`<inline asm>`).
            // Otherwise (register/immediate operands, or a read-only `m` input) it is
            // register-only and touches no tracked memory (`<inline asm nomem>`), which
            // the executor treats as a non-clobbering call — preserving the heap and
            // provenance that a havoc would destroy (kernel C is saturated with such asm).
            if asm_may_write_memory(&constraints) {
                "<inline asm>".to_string()
            } else {
                "<inline asm nomem>".to_string()
            }
        } else {
            self.callee_name()?
        };
        // A debug intrinsic (`llvm.dbg.value/declare/label`) carries only `metadata`
        // operands (`metadata !5, metadata !DIExpression()`) the value parser cannot
        // read and no memory-safety content — skip its argument list wholesale.
        if callee.starts_with("llvm.dbg.") {
            self.skip_balanced('(', ')')?;
            return Ok(LInst::Call {
                dst,
                ret,
                callee,
                args: Vec::new(),
            });
        }
        self.expect_punct('(')?;
        let mut args = Vec::new();
        if !matches!(self.peek(), Tok::Punct(')')) {
            loop {
                // A `metadata` argument (`metadata !5`, `metadata !DIExpression()`)
                // carries no value — skip to the next `,` or the closing `)`.
                if matches!(self.peek(), Tok::Word(w) if w == "metadata") {
                    while !matches!(self.peek(), Tok::Punct(',' | ')') | Tok::Eof) {
                        if matches!(self.peek(), Tok::Punct('(')) {
                            self.skip_balanced('(', ')')?;
                        } else {
                            self.pos += 1;
                        }
                    }
                    args.push(LValue::Undef);
                } else {
                    let _ty = self.ltype()?;
                    let deref = self.skip_arg_attrs()?;
                    let v = self.value()?;
                    // A `dereferenceable(N)` on a bare `@g` operand is an authoritative
                    // lower bound on that global's size (clang derives it from the type).
                    if let (Some(n), LValue::Global(name)) = (deref, &v) {
                        self.deref_hints
                            .entry(name.clone())
                            .and_modify(|m| *m = (*m).max(n))
                            .or_insert(n);
                    }
                    args.push(v);
                }
                if matches!(self.peek(), Tok::Punct(',')) {
                    self.pos += 1;
                } else {
                    break;
                }
            }
        }
        self.expect_punct(')')?;
        Ok(LInst::Call {
            dst,
            ret,
            callee,
            args,
        })
    }

    fn phi(&mut self, dst: String) -> Result<LPhi> {
        let ty = self.ltype()?;
        let mut incomings = Vec::new();
        loop {
            self.expect_punct('[')?;
            let v = self.value()?;
            self.expect_punct(',')?;
            let pred = self.local()?;
            self.expect_punct(']')?;
            incomings.push((v, pred));
            // Another `[…]` incoming follows a `,`; a `, !dbg …` does not.
            if matches!(self.peek(), Tok::Punct(',')) && matches!(self.peek2(), Tok::Punct('[')) {
                self.pos += 1;
            } else {
                break;
            }
        }
        Ok(LPhi { dst, ty, incomings })
    }

    fn pred(&mut self) -> Result<LPred> {
        let w = match self.bump() {
            Tok::Word(w) => w,
            other => {
                return Err(Error::parse(format!(
                    "expected icmp predicate, found {other:?}"
                )))
            }
        };
        Ok(match w.as_str() {
            "eq" => LPred::Eq,
            "ne" => LPred::Ne,
            "ult" => LPred::Ult,
            "ule" => LPred::Ule,
            "ugt" => LPred::Ugt,
            "uge" => LPred::Uge,
            "slt" => LPred::Slt,
            "sle" => LPred::Sle,
            "sgt" => LPred::Sgt,
            "sge" => LPred::Sge,
            other => return Err(Error::unsupported(format!("icmp predicate `{other}`"))),
        })
    }
}

enum InstOrPhi {
    Phi(LPhi),
    Inst(LInst),
}

fn is_int_type(w: &str) -> bool {
    w.starts_with('i') && w.len() > 1 && w[1..].bytes().all(|b| b.is_ascii_digit())
}

/// Whether an inline-asm constraint string means the asm may **write memory** we
/// track — a `"memory"` clobber, or an OUTPUT operand that references memory
/// (`=m`/`+m`/`=*m`/`=&m`/`=*A`…). A register/immediate output, or a read-only
/// memory *input* (`m` with no `=`/`+`), touches no tracked memory. Conservative
/// by direction: any doubt about an output resolves to "may write" (a false havoc,
/// never a missed write), so an unrecognised shape can only lose precision.
fn asm_may_write_memory(constraints: &str) -> bool {
    // A `~{memory}` clobber, or an indirect operand (`*` — the asm is handed a pointer
    // and may write through it, in any direction), or an OUTPUT memory operand
    // (`=m`/`+m`). Register/immediate operands and a read-only register output do not.
    constraints.contains("memory")
        || constraints.contains('*')
        || constraints
            .split(',')
            .any(|tok| (tok.contains('=') || tok.contains('+')) && tok.contains('m'))
}

/// Round `v` up to a multiple of the power-of-two `align`; `None` on overflow.
fn align_up(v: u64, align: u64) -> Option<u64> {
    debug_assert!(align.is_power_of_two());
    let mask = align - 1;
    v.checked_add(mask).map(|x| x & !mask)
}

/// Byte size of a resolved `LType` under the 64-bit layout (matches the IR's
/// `DataLayout::LP64`, so an initializer offset agrees with the executor's gep).
/// `None` for a type whose size cannot be determined (bails the whole scan).
fn ltype_size(ty: &LType) -> Result<u64> {
    let bad = || Error::unsupported("unsizable init element");
    Ok(match ty {
        LType::Void | LType::Metadata => 0,
        LType::Int(bits) => (*bits as u64).div_ceil(8),
        LType::Ptr => 8,
        LType::Array(e, n) | LType::Vector(e, n) => {
            let stride = align_up(ltype_size(e)?, ltype_align(e)?).ok_or_else(bad)?;
            stride.checked_mul(*n).ok_or_else(bad)?
        }
        LType::Struct(fs) => {
            let mut off = 0u64;
            let mut max_a = 1u64;
            for f in fs {
                let a = ltype_align(f)?;
                max_a = max_a.max(a);
                off = align_up(off, a).ok_or_else(bad)?;
                off = off.checked_add(ltype_size(f)?).ok_or_else(bad)?;
            }
            align_up(off, max_a).ok_or_else(bad)?
        }
        LType::PackedStruct(fs) => {
            let mut off = 0u64;
            for f in fs {
                off = off.checked_add(ltype_size(f)?).ok_or_else(bad)?;
            }
            off
        }
        LType::Named(_) => return Err(bad()),
    })
}

/// Byte alignment of a resolved `LType` under the 64-bit layout.
fn ltype_align(ty: &LType) -> Result<u64> {
    Ok(match ty {
        LType::Void | LType::Metadata => 1,
        LType::Int(bits) => (*bits as u64).div_ceil(8).max(1).next_power_of_two().min(8),
        LType::Ptr => 8,
        LType::Array(e, _) | LType::Vector(e, _) => ltype_align(e)?,
        LType::Struct(fs) => {
            let mut a = 1u64;
            for f in fs {
                a = a.max(ltype_align(f)?);
            }
            a
        }
        LType::PackedStruct(_) => 1,
        LType::Named(_) => return Err(Error::unsupported("unsizable init element")),
    })
}

/// Whether a token can begin a type (used to tell a real operand from trailing
/// `, !dbg …` metadata in comma-separated operand lists).
fn is_type_start(t: &Tok) -> bool {
    match t {
        Tok::Word(w) => is_int_type(w) || float_bits(w).is_some() || w == "ptr" || w == "void",
        // `%"name"` — a named-type reference.
        Tok::Local(_) => true,
        Tok::Punct('[') | Tok::Punct('<') | Tok::Punct('{') => true,
        _ => false,
    }
}

fn int_bits(w: &str) -> Result<u32> {
    w[1..]
        .parse()
        .map_err(|_| Error::parse(format!("bad integer type `{w}`")))
}

/// The byte-accurate bit width of an LLVM floating-point type, or `None` if `w`
/// is not one. Modelled as an opaque integer scalar of this width.
fn float_bits(w: &str) -> Option<u32> {
    Some(match w {
        "half" | "bfloat" => 16,
        "float" => 32,
        "double" => 64,
        "x86_fp80" => 80,
        "fp128" | "ppc_fp128" => 128,
        _ => return None,
    })
}

/// Whether an opcode is a floating-point arithmetic/cast/compare op. These carry
/// no memory-safety content, so they are lowered opaquely (`Undef`).
fn is_float_op(op: &str) -> bool {
    matches!(
        op,
        "fadd"
            | "fsub"
            | "fmul"
            | "fdiv"
            | "frem"
            | "fneg"
            | "fcmp"
            | "fptrunc"
            | "fpext"
            | "fptoui"
            | "fptosi"
            | "uitofp"
            | "sitofp"
    )
}

fn bin_op(op: &str) -> Option<LBin> {
    Some(match op {
        "add" => LBin::Add,
        "sub" => LBin::Sub,
        "mul" => LBin::Mul,
        "udiv" => LBin::UDiv,
        "sdiv" => LBin::SDiv,
        "urem" => LBin::URem,
        "srem" => LBin::SRem,
        "and" => LBin::And,
        "or" => LBin::Or,
        "xor" => LBin::Xor,
        "shl" => LBin::Shl,
        "lshr" => LBin::LShr,
        "ashr" => LBin::AShr,
        _ => return None,
    })
}

fn cast_op(op: &str) -> Option<LCast> {
    Some(match op {
        "trunc" => LCast::Trunc,
        "zext" => LCast::ZExt,
        "sext" => LCast::SExt,
        "ptrtoint" => LCast::PtrToInt,
        "inttoptr" => LCast::IntToPtr,
        "bitcast" => LCast::Bitcast,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = r#"
define void @make_and_store(i64 %i) {
entry:
  %buf = alloca [8 x i32], align 4
  %c0 = icmp sle i64 0, %i
  br i1 %c0, label %check, label %done
check:
  %c1 = icmp slt i64 %i, 8
  br i1 %c1, label %body, label %done
body:
  %p = getelementptr inbounds i32, ptr %buf, i64 %i
  store i32 0, ptr %p, align 4
  br label %done
done:
  ret void
}
"#;

    #[test]
    fn parses_the_sample() {
        let m = parse_module(SRC).expect("parse");
        assert_eq!(m.funcs.len(), 1);
        let f = &m.funcs[0];
        assert_eq!(f.name, "make_and_store");
        assert_eq!(f.params.len(), 1);
        assert_eq!(f.params[0].ty, LType::Int(64));
        assert_eq!(f.params[0].name, "i");
        assert_eq!(f.blocks.len(), 4);
        assert_eq!(f.blocks[0].label, "entry");
        // entry: alloca + icmp, then a conditional branch.
        assert_eq!(f.blocks[0].insts.len(), 2);
        assert!(matches!(f.blocks[0].term, LTerm::CondBr(..)));
        // body: gep + store.
        let body = f.blocks.iter().find(|b| b.label == "body").unwrap();
        assert!(matches!(body.insts[0], LInst::Gep { .. }));
        assert!(matches!(body.insts[1], LInst::Store { .. }));
    }

    #[test]
    fn scans_single_integer_metadata_nodes() {
        let m = scan_meta_ints("!126 = !{i64 8}\n!7 = !{i32 4}\n!9 = !{}\n!5 = !{!1, !2}\n");
        assert_eq!(m.get(&126), Some(&8));
        assert_eq!(m.get(&7), Some(&4));
        // An empty tuple and a multi-element tuple are not single integers.
        assert_eq!(m.get(&9), None);
        assert_eq!(m.get(&5), None);
    }

    #[test]
    fn parses_variadic_function() {
        // `...` is the trailing variadic marker; the fixed params are kept and the
        // function is analyzed rather than dropped whole.
        let src = "define i64 @sum(i32 %0, ...) {\nentry:\n  ret i64 0\n}\n";
        let m = parse_module(src).expect("parse");
        assert_eq!(m.unanalyzed.len(), 0, "variadic fn must not be dropped");
        assert_eq!(
            m.funcs[0].params.len(),
            1,
            "only the fixed i32 param is kept"
        );
    }

    #[test]
    fn numbers_unlabeled_entry_block_as_phi_predecessor() {
        // The entry block is unlabeled; its implicit LLVM number is the parameter
        // count (2 here → `%2`), and a later phi names it as a predecessor. It must
        // resolve — otherwise the whole function is dropped.
        let src = r#"
define i64 @f(ptr %0, i32 %1) {
  %3 = icmp sgt i32 %1, 0
  br i1 %3, label %4, label %5
4:
  br label %5
5:
  %6 = phi i64 [ 0, %2 ], [ 7, %4 ]
  ret i64 %6
}
"#;
        let m = parse_module(src).expect("parse");
        assert_eq!(
            m.unanalyzed.len(),
            0,
            "entry-referencing phi must not drop the fn"
        );
        // The entry block is labeled with its implicit number "2".
        assert_eq!(m.funcs[0].blocks[0].label, "2");
    }

    #[test]
    fn parses_variadic_call_with_explicit_function_type() {
        // A variadic call prints the full function type before the callee:
        // `call i64 (i32, ...) @f(...)`. The caller must not be dropped (which
        // would erase the call sites every contract synthesis depends on).
        let src = r#"
define i64 @caller() {
entry:
  %r = call i64 (i32, ...) @printf_like(i32 0, i64 1, i64 2)
  ret i64 %r
}
"#;
        let m = parse_module(src).expect("parse");
        assert_eq!(
            m.unanalyzed.len(),
            0,
            "variadic call must not drop the caller"
        );
        // The call parsed with its fixed + variadic arguments and callee.
        let call = m.funcs[0].blocks[0].insts.iter().find_map(|i| match i {
            LInst::Call { callee, args, .. } => Some((callee.clone(), args.len())),
            _ => None,
        });
        assert_eq!(call, Some(("printf_like".to_string(), 3)));
    }

    #[test]
    fn captures_load_align_metadata() {
        let src = r#"
define i64 @f(ptr %p) {
entry:
  %v = load ptr, ptr %p, align 8, !nonnull !0, !align !1
  %w = load i64, ptr %p, align 8
  ret i64 %w
}
!0 = !{}
!1 = !{i64 16}
"#;
        let m = parse_module(src).expect("parse");
        let f = &m.funcs[0];
        // The pointer load records its `!align 16` guarantee; the plain load does not.
        let mut loads = f.blocks[0].insts.iter().filter_map(|i| match i {
            LInst::Load { align_meta, .. } => Some(*align_meta),
            _ => None,
        });
        assert_eq!(loads.next(), Some(Some(16)));
        assert_eq!(loads.next(), Some(None));
    }
}
