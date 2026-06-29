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
    /// A type outside the modelled subset.
    Other,
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
    Ref(Place),
    Cast(Operand),
    /// `discriminant(PLACE)` — reads an enum's tag. The value is opaque (so a
    /// `switchInt` on it soundly explores every arm); lowering still checks the
    /// enum reference is valid.
    Discriminant(Place),
    /// An rvalue outside the modelled subset.
    Other,
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
    /// `StorageLive`/`StorageDead`/`nop`/`FakeRead`/… — no effect on the model.
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
    Call { dst: Place, callee: CalleeSpec, args: Vec<Operand>, target: Option<usize> },
    /// `drop(place) -> [return: bb, …]`: runs the value's destructor, which may
    /// free what it owns. Modelled as a freeing call (`target` is `None` for a
    /// diverging drop). The dropped place itself is not needed — the conservative
    /// free invalidates every owned region's liveness regardless.
    Drop { target: Option<usize> },
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
    pub(crate) term: MTerm,
}

/// A parsed MIR function body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MirBody {
    pub(crate) name: String,
    pub(crate) params: Vec<(Local, MType)>,
    pub(crate) ret: MType,
    pub(crate) blocks: Vec<MBlock>,
}

/// The successfully-parsed bodies plus the `(name, reason)` of any that failed.
pub(crate) type ParsedModule = (Vec<MirBody>, Vec<(String, String)>);

/// Parse every `fn` body in a MIR dump. A body that fails to parse does not
/// abort the whole module: its name is recorded (so the lowerer can report it
/// `UNKNOWN`) and parsing resumes at the next `fn` — per-function recovery, like
/// the lowerer's.
pub(crate) fn parse_module(src: &str) -> Result<ParsedModule> {
    let toks = lex(src)?;
    let mut p = Parser { toks, pos: 0 };
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

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> &Tok {
        self.toks.get(self.pos).unwrap_or(&Tok::Eof)
    }

    fn peek2(&self) -> &Tok {
        self.toks.get(self.pos + 1).unwrap_or(&Tok::Eof)
    }

    fn bump(&mut self) -> Tok {
        let t = self.peek().clone();
        if self.pos < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    fn eat_punct(&mut self, c: char) -> bool {
        if self.peek() == &Tok::Punct(c) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_punct(&mut self, c: char) -> Result<()> {
        if self.eat_punct(c) {
            Ok(())
        } else {
            Err(Error::parse(format!("expected `{c}`, found {:?}", self.peek())))
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

    fn word(&mut self) -> Result<String> {
        match self.bump() {
            Tok::Word(w) => Ok(w),
            other => Err(Error::parse(format!("expected a word, found {other:?}"))),
        }
    }

    /// Advance to the next top-level `fn`, returning whether one was found.
    fn skip_to_fn(&mut self) -> bool {
        while !matches!(self.peek(), Tok::Eof) {
            if matches!(self.peek(), Tok::Word(w) if w == "fn") {
                self.pos += 1;
                return true;
            }
            self.pos += 1;
        }
        false
    }

    /// Parse one function body (the cursor sits just past `fn`).
    fn body(&mut self) -> Result<MirBody> {
        // The header name may be a plain ident (`foo`), a qualified path
        // (`Type::method`), or — most commonly for `impl` methods — a path that
        // *starts* with `<`: `<impl at …>::method`, `<T as Trait>::method`.
        // Consume a leading `<…>`, then take the last path segment before the
        // argument `(` as the function's name.
        if self.peek() == &Tok::Punct('<') {
            self.skip_balanced_angle();
        }
        let mut name = String::new();
        while !matches!(self.peek(), Tok::Punct('(') | Tok::Eof) {
            if let Tok::Word(w) = self.peek() {
                name = w.clone();
            }
            self.pos += 1;
        }
        self.expect_punct('(')?;
        let mut params = Vec::new();
        while !self.eat_punct(')') {
            let local = self.local()?;
            self.expect_punct(':')?;
            let ty = self.ty()?;
            params.push((local, ty));
            let _ = self.eat_punct(',');
        }
        let ret = if self.peek() == &Tok::Arrow {
            self.pos += 1;
            self.ty()?
        } else {
            MType::Unit
        };
        self.expect_punct('{')?;

        // Skip the scope/debug/`let` preamble: advance to the first `bbN:`.
        self.skip_to_first_block();

        let mut blocks = Vec::new();
        while self.at_block_header() {
            blocks.push(self.block()?);
        }
        // Consume the function's closing brace (tolerant of trailing tokens).
        while !matches!(self.peek(), Tok::Eof) && !self.eat_punct('}') {
            self.pos += 1;
        }
        Ok(MirBody { name, params, ret, blocks })
    }

    /// `_N` → `N`.
    fn local(&mut self) -> Result<Local> {
        let w = self.word()?;
        w.strip_prefix('_')
            .and_then(|n| n.parse().ok())
            .ok_or_else(|| Error::parse(format!("expected a local `_N`, found `{w}`")))
    }

    fn at_block_header(&self) -> bool {
        // `bbN:` or an annotated header `bbN (cleanup):` — the latter must still be
        // recognised, or the block loop would stop early and silently DROP every
        // following block (which may contain a memory access → an unsound vacuous
        // PASS). So a `bbN` followed by `:` or `(` starts a block.
        matches!(self.peek(), Tok::Word(w) if is_bb(w))
            && matches!(self.peek2(), Tok::Punct(':') | Tok::Punct('('))
    }

    fn skip_to_first_block(&mut self) {
        while !matches!(self.peek(), Tok::Eof) && !self.at_block_header() {
            self.pos += 1;
        }
    }

    fn block(&mut self) -> Result<MBlock> {
        let w = self.word()?;
        let id = bb_index(&w).ok_or_else(|| Error::parse(format!("bad block label `{w}`")))?;
        // An optional block annotation, e.g. `bbN (cleanup):`.
        if self.eat_punct('(') {
            self.skip_balanced_paren();
        }
        self.expect_punct(':')?;
        self.expect_punct('{')?;
        let mut stmts = Vec::new();
        let term = loop {
            if let Some(t) = self.try_terminator()? {
                break t;
            }
            // An assignment-form terminator (`_0 = f(args) -> [return: bb, …]`)
            // reads like a statement but ends in `->` rather than `;`: a call.
            if self.stmt_is_terminator() {
                let t = self.call_terminator()?;
                let _ = self.eat_punct(';');
                break t;
            }
            stmts.push(self.statement()?);
        };
        self.expect_punct('}')?;
        Ok(MBlock { id, stmts, term })
    }

    /// Whether the upcoming statement is actually an assignment-form terminator:
    /// it reaches a top-level `->` before its `;` (or the block's `}`).
    fn stmt_is_terminator(&self) -> bool {
        let mut i = self.pos;
        let mut depth = 0i32;
        while let Some(t) = self.toks.get(i) {
            match t {
                Tok::Punct('(') | Tok::Punct('[') => depth += 1,
                Tok::Punct(')') | Tok::Punct(']') => depth -= 1,
                Tok::Arrow if depth == 0 => return true,
                Tok::Punct(';') if depth == 0 => return false,
                Tok::Punct('}') if depth <= 0 => return false,
                Tok::Eof => return false,
                _ => {}
            }
            i += 1;
        }
        false
    }


    /// Parse a terminator if the cursor is at one, else `None` (a statement).
    fn try_terminator(&mut self) -> Result<Option<MTerm>> {
        let kw = match self.peek() {
            Tok::Word(w) => w.clone(),
            Tok::Punct('}') => return Ok(Some(MTerm::Unreachable)), // empty block: defensive
            _ => return Ok(None),
        };
        let term = match kw.as_str() {
            "return" => {
                self.pos += 1;
                MTerm::Return
            }
            "unreachable" => {
                self.pos += 1;
                MTerm::Unreachable
            }
            "goto" => {
                self.pos += 1;
                MTerm::Goto(self.arrow_block()?)
            }
            "switchInt" => self.switch_int()?,
            "assert" => self.assert_term()?,
            "drop" => self.drop_term()?,
            // Abnormal terminators with no normal continuation: `resume` re-raises
            // a panic, `abort`/`terminate` end the process. They only sit in
            // cleanup blocks reached via `unwind:` edges, which the analysis does
            // not follow — so the block is unreachable in our CFG. Lowering them to
            // `Unreachable` lets the *rest* of the function analyse (instead of
            // being rejected for an unmodelled terminator), soundly.
            "resume" | "abort" | "terminate" => {
                self.skip_statement();
                MTerm::Unreachable
            }
            // `call` (a bare call terminator) and `yield` (a coroutine resume point,
            // which *does* have a normal continuation) are not modelled: reject.
            "call" | "yield" => {
                self.skip_statement();
                MTerm::Unsupported
            }
            _ => return Ok(None),
        };
        // Consume the terminating `;` if present.
        let _ = self.eat_punct(';');
        Ok(Some(term))
    }

    /// `-> bbN` → `N`.
    fn arrow_block(&mut self) -> Result<usize> {
        if self.peek() == &Tok::Arrow {
            self.pos += 1;
        }
        let w = self.word()?;
        bb_index(&w).ok_or_else(|| Error::parse(format!("expected a block after `->`, found `{w}`")))
    }

    /// `_dst = callee(args) -> [return: bb, …]`.
    fn call_terminator(&mut self) -> Result<MTerm> {
        let dst = self.place()?;
        self.expect_punct('=')?;
        let callee = self.callee_spec()?;
        self.expect_punct('(')?;
        let mut args = Vec::new();
        while !self.eat_punct(')') {
            args.push(self.operand()?);
            let _ = self.eat_punct(',');
        }
        let target = self.return_edge()?;
        Ok(MTerm::Call { dst, callee, args, target })
    }

    /// The callee of a call: an indirect function-pointer local (`move _N`), or
    /// a named path whose last identifier is the resolution key.
    fn callee_spec(&mut self) -> Result<CalleeSpec> {
        if self.eat_word("move") || self.eat_word("copy") {
            return Ok(match self.place()? {
                Place::Local(n) => CalleeSpec::Indirect(n),
                _ => CalleeSpec::Named(String::new()),
            });
        }
        let _ = self.eat_word("const");
        // Consume the path up to the argument `(`, keeping the last identifier
        // (the function name) and balancing `<…>` / `[…]` in qualified paths.
        let mut last = String::new();
        let mut depth = 0i32;
        loop {
            match self.peek() {
                Tok::Punct('(') if depth == 0 => break,
                Tok::Eof => break,
                Tok::Punct('<') | Tok::Punct('[') => depth += 1,
                Tok::Punct('>') | Tok::Punct(']') => depth -= 1,
                Tok::Word(w) => last = w.clone(),
                _ => {}
            }
            self.pos += 1;
        }
        Ok(CalleeSpec::Named(last))
    }

    /// The `return`/`success` target of a call's edges (`None` ⇒ diverging).
    fn return_edge(&mut self) -> Result<Option<usize>> {
        if self.peek() == &Tok::Arrow {
            self.pos += 1;
        }
        if self.eat_punct('[') {
            let mut target = None;
            while !self.eat_punct(']') {
                let key = self.word()?;
                if self.eat_punct(':') {
                    let bb = self.arrow_block_bare()?;
                    if key == "return" || key == "success" {
                        target = Some(bb);
                    }
                } else if matches!(self.peek(), Tok::Word(_)) {
                    self.pos += 1; // an unwind action without a block
                    if self.eat_punct('(') {
                        self.skip_balanced_paren();
                    }
                }
                let _ = self.eat_punct(',');
            }
            Ok(target)
        } else if self.eat_word("unwind") {
            // A diverging call `-> unwind continue` / `unwind unreachable` /
            // `unwind terminate(…)` (e.g. `_ = panic(…) -> unwind continue`): no
            // return target. Consume the action word and any payload.
            if matches!(self.peek(), Tok::Word(_)) {
                self.pos += 1;
                if self.eat_punct('(') {
                    self.skip_balanced_paren();
                }
            }
            Ok(None)
        } else {
            let w = self.word()?;
            Ok(bb_index(&w))
        }
    }

    fn switch_int(&mut self) -> Result<MTerm> {
        self.pos += 1; // switchInt
        self.expect_punct('(')?;
        let scrutinee = self.operand()?;
        self.expect_punct(')')?;
        if self.peek() == &Tok::Arrow {
            self.pos += 1;
        }
        self.expect_punct('[')?;
        let mut cases = Vec::new();
        let mut otherwise = None;
        while !self.eat_punct(']') {
            if self.eat_word("otherwise") {
                self.expect_punct(':')?;
                otherwise = Some(self.arrow_block_bare()?);
            } else {
                let v = self.int_lit()?;
                self.expect_punct(':')?;
                cases.push((v, self.arrow_block_bare()?));
            }
            let _ = self.eat_punct(',');
        }
        let otherwise = otherwise.ok_or_else(|| Error::parse("switchInt without an `otherwise`"))?;
        Ok(MTerm::SwitchInt(scrutinee, cases, otherwise))
    }

    /// `drop(place) -> [return: bb, unwind …]` — a destructor run. The dropped
    /// place is parsed (so it is consumed) but discarded: the conservative free
    /// model does not need to know which value is dropped.
    fn drop_term(&mut self) -> Result<MTerm> {
        self.pos += 1; // drop
        self.expect_punct('(')?;
        let _ = self.place()?;
        self.expect_punct(')')?;
        let target = self.return_edge()?;
        Ok(MTerm::Drop { target })
    }

    fn assert_term(&mut self) -> Result<MTerm> {
        self.pos += 1; // assert
        self.expect_punct('(')?;
        let expected = !self.eat_punct('!'); // `assert(!cond, …)` expects false
        let cond = self.operand()?;
        // Skip the message and its format args up to the matching `)`.
        let mut depth = 1;
        while depth > 0 {
            match self.bump() {
                Tok::Punct('(') => depth += 1,
                Tok::Punct(')') => depth -= 1,
                Tok::Eof => return Err(Error::parse("unterminated assert(...)")),
                _ => {}
            }
        }
        // `-> [success: bbN, unwind …]` or `-> bbN`.
        let target = self.success_block()?;
        Ok(MTerm::Assert { cond, expected, target })
    }

    /// The success target of an `assert`/call-style terminator: either
    /// `-> [success: bbN, …]` or `-> bbN`.
    fn success_block(&mut self) -> Result<usize> {
        if self.peek() == &Tok::Arrow {
            self.pos += 1;
        }
        if self.eat_punct('[') {
            let mut target = None;
            while !self.eat_punct(']') {
                let key = self.word()?;
                if self.eat_punct(':') {
                    let bb = self.arrow_block_bare()?;
                    if key == "success" || key == "return" {
                        target = Some(bb);
                    }
                } else {
                    // An unwind *action* without a block: `unwind continue` /
                    // `unwind unreachable` / `unwind terminate(...)`. Consume the
                    // action word and any parenthesised payload.
                    if matches!(self.peek(), Tok::Word(_)) {
                        self.pos += 1;
                        if self.eat_punct('(') {
                            self.skip_balanced_paren();
                        }
                    }
                }
                let _ = self.eat_punct(',');
            }
            target.ok_or_else(|| Error::parse("assert without a success edge"))
        } else {
            let w = self.word()?;
            bb_index(&w).ok_or_else(|| Error::parse(format!("bad assert target `{w}`")))
        }
    }

    /// A bare `bbN` (no leading arrow).
    fn arrow_block_bare(&mut self) -> Result<usize> {
        let w = self.word()?;
        bb_index(&w).ok_or_else(|| Error::parse(format!("expected a block, found `{w}`")))
    }

    fn statement(&mut self) -> Result<MStmt> {
        // No-effect statements: skip to `;`.
        if let Tok::Word(w) = self.peek() {
            if matches!(
                w.as_str(),
                "StorageLive" | "StorageDead" | "nop" | "FakeRead" | "AscribeUserType" | "Retag"
                    | "PlaceMention" | "Coverage" | "ConstEvalCounter" | "Deinit" | "assume"
                    | "BackwardIncompatibleDropHint"
            ) {
                self.skip_statement();
                return Ok(MStmt::Nop);
            }
        }
        // `PLACE = RVALUE ;`
        let place = self.place()?;
        self.expect_punct('=')?;
        let rv = self.rvalue()?;
        let _ = self.eat_punct(';');
        Ok(MStmt::Assign(place, rv))
    }

    /// Skip the rest of the current statement/terminator up to and including `;`.
    fn skip_statement(&mut self) {
        while !matches!(self.peek(), Tok::Eof) {
            let t = self.bump();
            if t == Tok::Punct(';') {
                break;
            }
        }
    }

    fn place(&mut self) -> Result<Place> {
        let mut base = if self.eat_punct('(') {
            // `(*PLACE)` or a parenthesised place, optionally a variant downcast
            // (`(_5 as Some)`) and/or a type ascription (`(_11.1: bool)`).
            let inner = if self.eat_punct('*') {
                Place::Deref(Box::new(self.place()?))
            } else {
                self.place()?
            };
            if self.eat_word("as") {
                let _ = self.word(); // the variant name (downcast is opaque here)
            }
            let mut inner = inner;
            if self.eat_punct(':') {
                let ty = self.ty()?;
                // For `((*_1).0: i32)` the ascription is the field's type — attach
                // it so the lowerer knows the field's size/alignment.
                if let Place::Field(_, _, fty @ None) = &mut inner {
                    *fty = Some(ty);
                }
            }
            self.expect_punct(')')?;
            inner
        } else if self.eat_punct('*') {
            Place::Deref(Box::new(self.place()?))
        } else {
            Place::Local(self.local()?)
        };
        // Projections: `[_M]`, `.N`, `.field`.
        loop {
            if self.eat_punct('[') {
                let idx = self.local()?;
                self.expect_punct(']')?;
                base = Place::Index(Box::new(base), idx);
            } else if self.eat_punct('.') {
                let field = self.field_index()?;
                base = Place::Field(Box::new(base), field, None);
            } else {
                break;
            }
        }
        Ok(base)
    }

    fn field_index(&mut self) -> Result<u32> {
        match self.bump() {
            Tok::Int(n) => Ok(n as u32),
            // `.field` named projections are not modelled precisely; treat the
            // ordinal as unknown (0) — a field place still yields a sound
            // (opaque) lowering downstream.
            Tok::Word(_) => Ok(0),
            other => Err(Error::parse(format!("expected a field index, found {other:?}"))),
        }
    }

    fn rvalue(&mut self) -> Result<Rvalue> {
        // `&PLACE` / `&mut PLACE` / `&raw const PLACE` / `&raw const (fake) PLACE`.
        if self.eat_punct('&') {
            let _ = self.eat_word("mut");
            if self.eat_word("raw") {
                let _ = self.eat_word("const") || self.eat_word("mut");
            }
            // Skip a parenthesised borrow-kind annotation `(fake)` / `(shallow)`
            // — distinguished from the place `(*_p)` by its leading keyword.
            if self.peek() == &Tok::Punct('(')
                && matches!(self.peek2(), Tok::Word(w) if matches!(w.as_str(), "fake" | "shallow" | "shared" | "two_phase"))
            {
                self.pos += 1;
                self.skip_balanced_paren();
            }
            return Ok(Rvalue::Ref(self.place()?));
        }
        if let Tok::Word(w) = self.peek().clone() {
            // `Len(PLACE)`.
            if w == "Len" && self.peek2() == &Tok::Punct('(') {
                self.pos += 1;
                self.expect_punct('(')?;
                let p = self.place()?;
                self.expect_punct(')')?;
                return Ok(Rvalue::Len(p));
            }
            // `PtrMetadata(OPERAND)`: for a slice/array reference the pointer
            // metadata *is* the length, so it lowers like `Len` of that place
            // (modern rustc emits this instead of `Len((*_1))`).
            if w == "PtrMetadata" && self.peek2() == &Tok::Punct('(') {
                self.pos += 1;
                self.expect_punct('(')?;
                let op = self.operand()?;
                self.expect_punct(')')?;
                return Ok(match op {
                    Operand::Copy(p) | Operand::Move(p) => Rvalue::Len(p),
                    Operand::Const(_) => Rvalue::Other,
                });
            }
            // `<BinKind>(a, b)` — but not an operand prefix `copy (…)` / `move (…)`
            // (where the `(` opens a parenthesised place, not an operator's args).
            let is_operand_prefix = matches!(w.as_str(), "copy" | "move" | "const");
            if self.peek2() == &Tok::Punct('(') && !is_operand_prefix {
                if let Some(kind) = bin_kind(&w) {
                    self.pos += 1;
                    self.expect_punct('(')?;
                    let a = self.operand()?;
                    let _ = self.eat_punct(',');
                    let b = self.operand()?;
                    self.expect_punct(')')?;
                    return Ok(Rvalue::Bin(kind, a, b));
                }
                // Checked arithmetic (`AddWithOverflow`/…): a `(result, overflow)`.
                if let Some(kind) = checked_bin_kind(&w) {
                    self.pos += 1;
                    self.expect_punct('(')?;
                    let a = self.operand()?;
                    let _ = self.eat_punct(',');
                    let b = self.operand()?;
                    self.expect_punct(')')?;
                    return Ok(Rvalue::CheckedBin(kind, a, b));
                }
                // `discriminant(PLACE)` — an enum tag read.
                if w == "discriminant" {
                    self.pos += 1;
                    self.expect_punct('(')?;
                    let place = self.place()?;
                    self.expect_punct(')')?;
                    return Ok(Rvalue::Discriminant(place));
                }
                // A different `Word(...)` rvalue (Aggregate, a checked op, …) is
                // not modelled.
                self.skip_statement_inline();
                return Ok(Rvalue::Other);
            }
        }
        // Otherwise an operand, possibly a cast `OPERAND as TYPE`.
        let op = self.operand()?;
        if self.eat_word("as") {
            let _ = self.ty()?;
            // Skip a trailing `(CastKind)` annotation.
            if self.eat_punct('(') {
                let mut depth = 1;
                while depth > 0 && !matches!(self.peek(), Tok::Eof) {
                    match self.bump() {
                        Tok::Punct('(') => depth += 1,
                        Tok::Punct(')') => depth -= 1,
                        _ => {}
                    }
                }
            }
            return Ok(Rvalue::Cast(op));
        }
        Ok(Rvalue::Use(op))
    }

    /// Skip the remainder of an rvalue up to (not including) the `;`.
    fn skip_statement_inline(&mut self) {
        while !matches!(self.peek(), Tok::Punct(';') | Tok::Eof) {
            self.pos += 1;
        }
    }

    fn operand(&mut self) -> Result<Operand> {
        if self.eat_word("move") {
            Ok(Operand::Move(self.place()?))
        } else if self.eat_word("copy") {
            Ok(Operand::Copy(self.place()?))
        } else if self.eat_word("const") {
            Ok(Operand::Const(self.constant()?))
        } else if self.starts_place() {
            // A bare place operand (`_N`, `(*_p)…`).
            Ok(Operand::Copy(self.place()?))
        } else {
            // A path / aggregate / unevaluated constant in operand position
            // (`RangeTo::<usize> { … }`, `Foo::Bar(…)`, `core::X`): not a memory
            // operation, so model it as an opaque value and consume it whole.
            self.skip_opaque_value();
            Ok(Operand::Const(MConst::Int(0)))
        }
    }

    /// Whether the cursor is at the start of a *bare* place operand: a local `_N`,
    /// a deref `*_p`, or a parenthesised place `(*_p)…`. A bare `(` that is a tuple
    /// aggregate `(a, b)` / `()` is *not* a place, and a bare identifier is a path
    /// — both are consumed opaquely instead.
    fn starts_place(&self) -> bool {
        match self.peek() {
            Tok::Punct('*') => true,
            Tok::Word(w) => w.starts_with('_'),
            Tok::Punct('(') => !self.paren_is_tuple(),
            _ => false,
        }
    }

    /// Look ahead at a `( … )` to tell a tuple aggregate (a top-level comma, or
    /// `()`) from a parenthesised place (`(*_p)`, `((*_p).0: T)` — no top-level
    /// comma). Brackets balance by depth; only `()[]{}` are tracked.
    fn paren_is_tuple(&self) -> bool {
        let mut i = self.pos + 1;
        let mut depth = 1i32;
        let mut saw_content = false;
        while let Some(t) = self.toks.get(i) {
            match t {
                Tok::Punct('(') | Tok::Punct('[') | Tok::Punct('{') => depth += 1,
                Tok::Punct(')') | Tok::Punct(']') | Tok::Punct('}') => {
                    depth -= 1;
                    if depth == 0 {
                        return !saw_content; // `()` is the unit tuple
                    }
                }
                Tok::Punct(',') if depth == 1 => return true,
                Tok::Eof => break,
                _ => saw_content = true,
            }
            i += 1;
        }
        false
    }

    /// Consume a path/aggregate/const expression opaquely: a path with generics
    /// (`core::ops::RangeTo::<usize>`), then any struct-literal `{ … }`, call/tuple
    /// `( … )` or array `[ … ]` body, balancing all brackets, up to the enclosing
    /// statement/argument delimiter. Used where the value is not a memory operation
    /// and only its presence (not its contents) matters.
    fn skip_opaque_value(&mut self) {
        let mut depth = 0i32;
        loop {
            match self.peek() {
                Tok::Eof => break,
                Tok::Punct('(') | Tok::Punct('[') | Tok::Punct('{') | Tok::Punct('<') => {
                    depth += 1;
                    self.pos += 1;
                }
                Tok::Punct(')') | Tok::Punct(']') | Tok::Punct('}') | Tok::Punct('>')
                    if depth > 0 =>
                {
                    depth -= 1;
                    self.pos += 1;
                }
                Tok::Punct(',') | Tok::Punct(';') if depth == 0 => break,
                Tok::Punct(')') | Tok::Punct(']') | Tok::Punct('}') if depth == 0 => break,
                _ => self.pos += 1,
            }
        }
    }

    fn constant(&mut self) -> Result<MConst> {
        match self.peek().clone() {
            Tok::Int(n) => {
                self.pos += 1;
                Ok(MConst::Int(n))
            }
            Tok::Word(w) if w == "true" => {
                self.pos += 1;
                Ok(MConst::Bool(true))
            }
            Tok::Word(w) if w == "false" => {
                self.pos += 1;
                Ok(MConst::Bool(false))
            }
            // A negative literal `const -1_i32`.
            Tok::Punct('-') if matches!(self.peek2(), Tok::Int(_)) => {
                self.pos += 1;
                if let Tok::Int(n) = self.bump() {
                    Ok(MConst::Int(-n))
                } else {
                    unreachable!()
                }
            }
            // A symbolic / unevaluated constant (a function item, a promoted
            // value, an associated const `<A as Array>::CAPACITY`, …): consume the
            // whole path/expression; model as 0 (its value is never relied on for a
            // sound PASS).
            _ => {
                self.skip_opaque_value();
                Ok(MConst::Int(0))
            }
        }
    }

    fn int_lit(&mut self) -> Result<i128> {
        match self.bump() {
            Tok::Int(n) => Ok(n),
            other => Err(Error::parse(format!("expected an integer, found {other:?}"))),
        }
    }

    fn ty(&mut self) -> Result<MType> {
        match self.peek().clone() {
            Tok::Punct('&') => {
                self.pos += 1;
                let mutable = self.eat_word("mut");
                // Lifetimes `&'a T` are not tokenised specially; tolerate a stray
                // word that is not a type start by leaving it to the inner `ty`.
                Ok(MType::Ref(Box::new(self.ty()?), mutable))
            }
            Tok::Punct('*') => {
                self.pos += 1;
                let mutable = self.eat_word("mut");
                let _ = self.eat_word("const");
                Ok(MType::Ptr(Box::new(self.ty()?), mutable))
            }
            Tok::Punct('[') => {
                self.pos += 1;
                let elem = self.ty()?;
                if self.eat_punct(';') {
                    // `[T; N]` with a literal length is an array; a const-generic
                    // or expression length (`[T; CAP]`) is a sized array of unknown
                    // size, so model it opaquely (consume up to the `]`).
                    if let &Tok::Int(n) = self.peek() {
                        self.pos += 1;
                        self.expect_punct(']')?;
                        Ok(MType::Array(Box::new(elem), n as u64))
                    } else {
                        while !self.eat_punct(']') && !matches!(self.peek(), Tok::Eof) {
                            self.pos += 1;
                        }
                        Ok(MType::Other)
                    }
                } else {
                    self.expect_punct(']')?;
                    Ok(MType::Slice(Box::new(elem)))
                }
            }
            Tok::Punct('(') => {
                // `()` unit, or a tuple (not modelled).
                self.pos += 1;
                if self.eat_punct(')') {
                    Ok(MType::Unit)
                } else {
                    self.skip_balanced_paren();
                    Ok(MType::Other)
                }
            }
            Tok::Word(w) => {
                self.pos += 1;
                // A trait object / impl-trait type (`dyn core::fmt::Debug`,
                // `impl Iterator + 'a`): consume the `+`-separated trait-path
                // bounds (a lifetime such as `'a` lexes to a bare word). Opaque.
                if w == "dyn" || w == "impl" {
                    self.skip_trait_bounds();
                    return Ok(MType::Other);
                }
                // A named type may be a qualified path with generic arguments
                // (`core::option::Option<i32>`, `Vec<T>`); consume the whole path
                // tail so the type lowers to `Other`, not a parse error. The inner
                // element types are not needed (the aggregate is opaque-size; a
                // field access carries its own type ascription).
                let ty = int_type(&w).unwrap_or(MType::Other);
                self.skip_path_tail();
                Ok(ty)
            }
            // A qualified type `<T as Trait>::Assoc` starts with `<`; consume the
            // `<…>` and any `::Assoc` tail.
            Tok::Punct('<') => {
                self.skip_balanced_angle();
                self.skip_path_tail();
                Ok(MType::Other)
            }
            // An anonymous type printed with braces: `{closure@…}`,
            // `{async block@…}`. Consume exactly the balanced `{…}` (not a function
            // body that may follow, e.g. a closure return type), then any tail.
            Tok::Punct('{') => {
                self.skip_balanced_braces();
                self.skip_path_tail();
                Ok(MType::Other)
            }
            _ => Ok(MType::Other),
        }
    }

    fn skip_balanced_paren(&mut self) {
        let mut depth = 1;
        while depth > 0 && !matches!(self.peek(), Tok::Eof) {
            match self.bump() {
                Tok::Punct('(') => depth += 1,
                Tok::Punct(')') => depth -= 1,
                _ => {}
            }
        }
    }

    /// Consume exactly one balanced `{ … }` group (an anonymous closure/async
    /// type), if one is next.
    fn skip_balanced_braces(&mut self) {
        if !self.eat_punct('{') {
            return;
        }
        let mut depth = 1;
        while depth > 0 && !matches!(self.peek(), Tok::Eof) {
            match self.bump() {
                Tok::Punct('{') => depth += 1,
                Tok::Punct('}') => depth -= 1,
                _ => {}
            }
        }
    }

    /// Skip a balanced `<…>` generic-argument list (`Option<i32>`,
    /// `Vec<Vec<i32>>`), if one follows. Each `>` is a separate token, so nested
    /// closers balance by depth.
    fn skip_balanced_angle(&mut self) {
        if !self.eat_punct('<') {
            return;
        }
        let mut depth = 1;
        while depth > 0 && !matches!(self.peek(), Tok::Eof) {
            match self.bump() {
                Tok::Punct('<') => depth += 1,
                Tok::Punct('>') => depth -= 1,
                _ => {}
            }
        }
    }

    /// Consume the `+`-separated trait-path bounds of a `dyn`/`impl` type
    /// (`dyn core::fmt::Debug + Send + 'a`). Each bound is a path (lifetimes lex
    /// to bare words, the `'` being dropped by the lexer).
    fn skip_trait_bounds(&mut self) {
        loop {
            if matches!(self.peek(), Tok::Word(_)) {
                self.pos += 1;
                self.skip_path_tail();
            } else {
                break;
            }
            if !self.eat_punct('+') {
                break;
            }
        }
    }

    /// Consume a type's path/generic tail: `::segment` steps, generic `<…>` lists,
    /// and turbofish `::<…>`, in any order — so `core::result::Result<…>` and
    /// `Foo<T>::Bar` are fully consumed (the type itself stays `Other`).
    fn skip_path_tail(&mut self) {
        loop {
            match self.peek() {
                Tok::Punct('<') => self.skip_balanced_angle(),
                Tok::Punct(':') if self.peek2() == &Tok::Punct(':') => {
                    self.pos += 2; // `::`
                    match self.peek() {
                        Tok::Punct('<') => self.skip_balanced_angle(), // turbofish
                        Tok::Word(_) => self.pos += 1,                 // a path segment
                        _ => {}
                    }
                }
                _ => break,
            }
        }
    }
}

fn is_bb(w: &str) -> bool {
    w.strip_prefix("bb").is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

fn bb_index(w: &str) -> Option<usize> {
    w.strip_prefix("bb").and_then(|n| n.parse().ok())
}

fn bin_kind(w: &str) -> Option<BinKind> {
    Some(match w {
        "Add" => BinKind::Add,
        "Sub" => BinKind::Sub,
        "Mul" => BinKind::Mul,
        "Lt" => BinKind::Lt,
        "Le" => BinKind::Le,
        "Gt" => BinKind::Gt,
        "Ge" => BinKind::Ge,
        "Eq" => BinKind::Eq,
        "Ne" => BinKind::Ne,
        "BitAnd" => BinKind::BitAnd,
        "BitOr" => BinKind::BitOr,
        "BitXor" => BinKind::BitXor,
        // A modelled-as-opaque arithmetic op (Div/Rem/Shl/Shr/Offset/checked …).
        "Div" | "Rem" | "Shl" | "Shr" | "Offset" => BinKind::Other,
        _ => return None,
    })
}

/// The base operator of a checked-arithmetic rvalue (`AddWithOverflow`,
/// `CheckedAdd`, …) — these produce a `(result, overflow)` tuple.
fn checked_bin_kind(w: &str) -> Option<BinKind> {
    Some(match w {
        "AddWithOverflow" | "CheckedAdd" => BinKind::Add,
        "SubWithOverflow" | "CheckedSub" => BinKind::Sub,
        "MulWithOverflow" | "CheckedMul" => BinKind::Mul,
        _ => return None,
    })
}

fn int_type(w: &str) -> Option<MType> {
    let (signed, rest) = match w.as_bytes().first()? {
        b'i' => (true, &w[1..]),
        b'u' => (false, &w[1..]),
        _ if w == "bool" => return Some(MType::Bool),
        _ => return None,
    };
    let width = match rest {
        "8" => 8,
        "16" => 16,
        "32" => 32,
        "64" | "128" => 64, // 128-bit modelled at 64 (the BV width cap)
        "size" => 64,
        _ => return None,
    };
    Some(MType::Int { width, signed })
}
