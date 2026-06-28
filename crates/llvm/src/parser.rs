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

/// A parsed module.
#[derive(Debug, Clone)]
pub struct LModule {
    /// The defined functions that parsed successfully.
    pub funcs: Vec<LFunc>,
    /// `(name, reason)` for functions that failed to parse and were skipped, so
    /// the caller can report them as `UNKNOWN` rather than silently dropping
    /// them.
    pub unanalyzed: Vec<(String, String)>,
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
}

/// Integer binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LBin {
    Add, Sub, Mul, UDiv, SDiv, URem, SRem, And, Or, Xor, Shl, LShr, AShr,
}

/// Comparison predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LPred {
    Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge,
}

/// Cast operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LCast {
    Trunc, ZExt, SExt, PtrToInt, IntToPtr, Bitcast,
}

/// A parsed straight-line instruction.
#[derive(Debug, Clone)]
pub enum LInst {
    /// `dst = alloca ty[, align n]`.
    Alloca { dst: String, ty: LType, align: u32 },
    /// `dst = load ty, ptr p[, align n]`.
    Load { dst: String, ty: LType, ptr: LValue, align: u32 },
    /// `store ty v, ptr p[, align n]`.
    Store { ty: LType, val: LValue, ptr: LValue, align: u32 },
    /// `dst = getelementptr [inbounds] elem, ptr base, i.. index`.
    Gep { dst: String, elem: LType, base: LValue, index: LValue },
    /// A binary op.
    Bin { dst: String, op: LBin, ty: LType, a: LValue, b: LValue },
    /// `dst = icmp pred ty a, b`.
    Icmp { dst: String, pred: LPred, ty: LType, a: LValue, b: LValue },
    /// A cast.
    Cast { dst: String, op: LCast, val: LValue, to: LType },
    /// `[dst =] call ret @callee(args)`.
    Call { dst: Option<String>, ret: LType, callee: String, args: Vec<LValue> },
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
    /// `unreachable`.
    Unreachable,
}

/// Parse a `.ll` source into an [`LModule`].
pub fn parse_module(src: &str) -> Result<LModule> {
    let toks = lex(src)?;
    let mut p = Parser { toks, pos: 0 };
    let mut funcs = Vec::new();
    let mut unanalyzed = Vec::new();
    loop {
        p.skip_newlines();
        match p.peek() {
            Tok::Eof => break,
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
    Ok(LModule { funcs, unanalyzed })
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
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
            other => Err(Error::parse(format!("expected global @name, found {other:?}"))),
        }
    }
    fn local(&mut self) -> Result<String> {
        match self.bump() {
            Tok::Local(s) => Ok(s),
            other => Err(Error::parse(format!("expected local %name, found {other:?}"))),
        }
    }

    fn ltype(&mut self) -> Result<LType> {
        let mut ty = match self.bump() {
            Tok::Word(w) if w == "void" => LType::Void,
            Tok::Word(w) if w == "ptr" => LType::Ptr,
            Tok::Word(w) if is_int_type(&w) => LType::Int(int_bits(&w)?),
            Tok::Punct('[') => {
                let n = self.int()?;
                self.expect_word("x")?;
                let elem = self.ltype()?;
                self.expect_punct(']')?;
                LType::Array(Box::new(elem), n as u64)
            }
            Tok::Punct('<') => {
                let n = self.int()?;
                self.expect_word("x")?;
                let elem = self.ltype()?;
                self.expect_punct('>')?;
                LType::Vector(Box::new(elem), n as u64)
            }
            other => return Err(Error::unsupported(format!("type starting with {other:?}"))),
        };
        // Legacy pointer suffixes: `i32*`, `[..]**`, etc. all collapse to `ptr`.
        while matches!(self.peek(), Tok::Punct('*')) {
            self.pos += 1;
            ty = LType::Ptr;
        }
        Ok(ty)
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
            _ => {}
        }
        match self.bump() {
            Tok::Local(s) => Ok(LValue::Local(s)),
            Tok::Int(n) => Ok(LValue::Int(n)),
            Tok::Global(s) => Ok(LValue::Global(s)),
            Tok::Word(w) if w == "null" => Ok(LValue::Null),
            Tok::Word(w) if w == "undef" || w == "poison" => Ok(LValue::Undef),
            Tok::Word(w) if w == "true" => Ok(LValue::Int(1)),
            Tok::Word(w) if w == "false" => Ok(LValue::Int(0)),
            other => Err(Error::unsupported(format!("operand value {other:?}"))),
        }
    }

    /// `, align N` if present.
    fn maybe_align(&mut self) -> Option<u32> {
        if matches!(self.peek(), Tok::Punct(',')) && matches!(self.peek2(), Tok::Word(w) if w == "align")
        {
            self.pos += 2; // ',' 'align'
            if let Tok::Int(n) = self.bump() {
                return Some(n as u32);
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
    fn param_attrs(&mut self) -> Result<(Option<u64>, Option<u32>, bool, bool)> {
        let mut deref = None;
        let mut align = None;
        let mut readonly = false;
        let mut writeonly = false;
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
        Ok((deref, align, readonly, writeonly))
    }

    /// Skip a call argument's attributes up to its operand. Crucially, `align
    /// N` is skipped as a *pair* (so the alignment value `N` is not mistaken for
    /// the operand), and parenthesized attributes are skipped balanced.
    fn skip_arg_attrs(&mut self) -> Result<()> {
        loop {
            match self.peek() {
                // The operand: a register, global, integer, or aggregate const.
                Tok::Local(_)
                | Tok::Global(_)
                | Tok::Int(_)
                | Tok::Punct(',')
                | Tok::Punct(')')
                | Tok::Punct('<')
                | Tok::Punct('[')
                | Tok::Punct('{')
                | Tok::Eof => break,
                Tok::Word(w) if matches!(w.as_str(), "null" | "undef" | "poison" | "true" | "false") => {
                    break
                }
                Tok::Word(w) if w == "align" => {
                    self.pos += 1;
                    if matches!(self.peek(), Tok::Int(_)) {
                        self.pos += 1;
                    }
                }
                Tok::Punct('(') => self.skip_balanced('(', ')')?,
                _ => self.pos += 1,
            }
        }
        Ok(())
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

    fn function(&mut self) -> Result<LFunc> {
        self.expect_word("define")?;
        // Skip linkage/visibility/return attributes (`dso_local`, `noundef`,
        // `signext`, `dereferenceable(N)`, …) up to the return type.
        self.skip_to_type()?;
        let ret = self.ltype()?;
        let name = self.global()?;
        self.expect_punct('(')?;
        let mut params = Vec::new();
        if !matches!(self.peek(), Tok::Punct(')')) {
            loop {
                let ty = self.ltype()?;
                let (deref, align, readonly, writeonly) = self.param_attrs()?;
                let name = if let Tok::Local(_) = self.peek() {
                    self.local()?
                } else {
                    String::new() // unnamed parameter
                };
                params.push(LParam { ty, name, deref, align, readonly, writeonly });
                if matches!(self.peek(), Tok::Punct(',')) {
                    self.pos += 1;
                } else {
                    break;
                }
            }
        }
        self.expect_punct(')')?;
        // Skip everything up to the opening brace (attributes, `unnamed_addr`,
        // `#0`, etc.).
        while !matches!(self.peek(), Tok::Punct('{') | Tok::Eof) {
            self.pos += 1;
        }
        self.expect_punct('{')?;
        let blocks = self.blocks()?;
        self.expect_punct('}')?;
        Ok(LFunc { name, ret, params, blocks })
    }

    fn blocks(&mut self) -> Result<Vec<LBlock>> {
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
            } else {
                let l = format!("__bb{auto}");
                auto += 1;
                l
            };

            let mut phis = Vec::new();
            let mut insts = Vec::new();
            let term = loop {
                self.skip_newlines();
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
            blocks.push(LBlock { label, phis, insts, term });
        }
        Ok(blocks)
    }

    fn try_terminator(&mut self) -> Result<Option<LTerm>> {
        let kw = match self.peek() {
            Tok::Word(w) => w.clone(),
            _ => return Ok(None),
        };
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
            "unreachable" => {
                self.pos += 1;
                Ok(Some(LTerm::Unreachable))
            }
            _ => Ok(None),
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
        let need_dst = || dst.clone().ok_or_else(|| Error::parse(format!("`{op}` needs a destination")));

        let inst = match op.as_str() {
            "alloca" => {
                let ty = self.ltype()?;
                let align = self.maybe_align().unwrap_or(0);
                LInst::Alloca { dst: need_dst()?, ty, align }
            }
            "load" => {
                let ty = self.ltype()?;
                self.expect_punct(',')?;
                let _pty = self.ltype()?;
                let ptr = self.value()?;
                let align = self.maybe_align().unwrap_or(0);
                LInst::Load { dst: need_dst()?, ty, ptr, align }
            }
            "store" => {
                let ty = self.ltype()?;
                let val = self.value()?;
                self.expect_punct(',')?;
                let _pty = self.ltype()?;
                let ptr = self.value()?;
                let align = self.maybe_align().unwrap_or(0);
                LInst::Store { ty, val, ptr, align }
            }
            "getelementptr" => self.gep(need_dst()?)?,
            "icmp" => {
                let pred = self.pred()?;
                let ty = self.ltype()?;
                let a = self.value()?;
                self.expect_punct(',')?;
                let b = self.value()?;
                LInst::Icmp { dst: need_dst()?, pred, ty, a, b }
            }
            "call" => self.call(dst)?,
            "phi" => {
                let phi = self.phi(need_dst()?)?;
                return Ok(InstOrPhi::Phi(phi));
            }
            other => {
                if let Some(bop) = bin_op(other) {
                    // Skip flags like `nuw`, `nsw`, `exact`.
                    while matches!(self.peek(), Tok::Word(w) if matches!(w.as_str(), "nuw" | "nsw" | "exact")) {
                        self.pos += 1;
                    }
                    let ty = self.ltype()?;
                    let a = self.value()?;
                    self.expect_punct(',')?;
                    let b = self.value()?;
                    LInst::Bin { dst: need_dst()?, op: bop, ty, a, b }
                } else if let Some(cop) = cast_op(other) {
                    let _from = self.ltype()?;
                    let val = self.value()?;
                    self.expect_word("to")?;
                    let to = self.ltype()?;
                    LInst::Cast { dst: need_dst()?, op: cop, val, to }
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
        let (elem, index) = match (&base_ty, indices.as_slice()) {
            // `gep T, ptr, idx` — pointer arithmetic over T.
            (_, [idx]) => (base_ty.clone(), idx.clone()),
            // `gep [N x T], ptr, 0, idx` — array element.
            (LType::Array(elem, _), [_, idx]) => ((**elem).clone(), idx.clone()),
            _ => {
                return Err(Error::unsupported(
                    "getelementptr with a shape outside {single index, [N x T] array}",
                ))
            }
        };
        Ok(LInst::Gep { dst, elem, base, index })
    }

    fn call(&mut self, dst: Option<String>) -> Result<LInst> {
        // Skip calling-convention / tail / return-attribute words.
        while self.eat_word("tail") || self.eat_word("notail") || self.eat_word("musttail") {}
        self.skip_to_type()?;
        let ret = self.ltype()?;
        let callee = self.global()?;
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
        Ok(LInst::Call { dst, ret, callee, args })
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
            other => return Err(Error::parse(format!("expected icmp predicate, found {other:?}"))),
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

/// Whether a token can begin a type (used to tell a real operand from trailing
/// `, !dbg …` metadata in comma-separated operand lists).
fn is_type_start(t: &Tok) -> bool {
    match t {
        Tok::Word(w) => is_int_type(w) || w == "ptr" || w == "void",
        Tok::Punct('[') | Tok::Punct('<') => true,
        _ => false,
    }
}

fn int_bits(w: &str) -> Result<u32> {
    w[1..].parse().map_err(|_| Error::parse(format!("bad integer type `{w}`")))
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
}
