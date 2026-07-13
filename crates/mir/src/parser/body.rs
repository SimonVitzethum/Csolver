use super::*;

impl Parser {
    /// The source location recorded for the token at index `at` (a statement's
    /// first token), if the MIR carried a span there.
    pub(crate) fn loc_at(&self, at: usize) -> Option<String> {
        self.locs.get(at).cloned().flatten()
    }

    pub(crate) fn peek(&self) -> &Tok {
        self.toks.get(self.pos).unwrap_or(&Tok::Eof)
    }

    pub(crate) fn peek2(&self) -> &Tok {
        self.toks.get(self.pos + 1).unwrap_or(&Tok::Eof)
    }

    pub(crate) fn bump(&mut self) -> Tok {
        let t = self.peek().clone();
        if self.pos < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    pub(crate) fn eat_punct(&mut self, c: char) -> bool {
        if self.peek() == &Tok::Punct(c) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    pub(crate) fn expect_punct(&mut self, c: char) -> Result<()> {
        if self.eat_punct(c) {
            Ok(())
        } else {
            Err(Error::parse(format!("expected `{c}`, found {:?}", self.peek())))
        }
    }

    pub(crate) fn eat_word(&mut self, w: &str) -> bool {
        if matches!(self.peek(), Tok::Word(x) if x == w) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    pub(crate) fn word(&mut self) -> Result<String> {
        match self.bump() {
            Tok::Word(w) => Ok(w),
            other => Err(Error::parse(format!("expected a word, found {other:?}"))),
        }
    }

    /// Advance to the next top-level `fn`, returning whether one was found.
    pub(crate) fn skip_to_fn(&mut self) -> bool {
        while !matches!(self.peek(), Tok::Eof) {
            // A real function header is `fn name(…)` / `fn <impl …>::m(…)`, so the
            // token after `fn` is a name (a `Word`) or the `<` of a qualified
            // path. Anything else is not an item and must be skipped:
            //   - `fn(` — a function-pointer *type* (`unsafe fn(&T) -> R`);
            //   - `fn:` — a vtable/promoted-static alloc entry (`alloc297
            //     (fn: promotable_odd_clone)`), which rustc appends after the
            //     bodies. Landing on these tried to parse a bogus function body.
            if matches!(self.peek(), Tok::Word(w) if w == "fn")
                && matches!(self.peek2(), Tok::Word(_) | Tok::Punct('<'))
            {
                self.pos += 1;
                return true;
            }
            self.pos += 1;
        }
        false
    }

    /// Parse one function body (the cursor sits just past `fn`).
    pub(crate) fn body(&mut self) -> Result<MirBody> {
        // The header name may be a plain ident (`foo`), a qualified path
        // (`Type::method`), or — most commonly for `impl` methods — a path that
        // *starts* with `<`: `<impl at …>::method`, `<T as Trait>::method`.
        // Consume a leading `<…>`, then take the last path segment before the
        // argument `(` as the function's name.
        if self.peek() == &Tok::Punct('<') {
            self.skip_balanced_angle();
        }
        // Accumulate the full path (`Buf::get_u16::{closure#0}::{closure#0}`),
        // not just the last segment: distinct closures must keep distinct names,
        // or every closure in a crate reports as "closure" and a finding cannot
        // be located.
        let mut name = String::new();
        while !matches!(self.peek(), Tok::Punct('(') | Tok::Eof) {
            match self.peek() {
                Tok::Word(w) => {
                    if !name.is_empty() && !name.ends_with('{') {
                        name.push_str("::");
                    }
                    name.push_str(w);
                }
                // `{closure#0}` / `{constant#0}` — anonymous item segments. The
                // lexer drops the `#` sigil, so the index arrives as a bare Int
                // inside the open brace group; keep it, or sibling closures
                // collide.
                Tok::Punct('{') => name.push('{'),
                Tok::Int(n) if name.rfind('{') > name.rfind('}') => {
                    name.push('#');
                    name.push_str(&n.to_string());
                }
                Tok::Punct('}') => name.push('}'),
                _ => {}
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

        // Parse the scope/debug/`let` preamble for its local declarations, then
        // stop at the first `bbN:`. (Previously skipped wholesale — the local types
        // are needed to type call results and dereferences.)
        let locals = self.parse_locals();

        let mut blocks = Vec::new();
        while self.at_block_header() {
            blocks.push(self.block()?);
        }
        // Consume the function's closing brace (tolerant of trailing tokens).
        while !matches!(self.peek(), Tok::Eof) && !self.eat_punct('}') {
            self.pos += 1;
        }
        Ok(MirBody { name, params, ret, locals, blocks })
    }

    /// `_N` → `N`.
    pub(crate) fn local(&mut self) -> Result<Local> {
        let w = self.word()?;
        w.strip_prefix('_')
            .and_then(|n| n.parse().ok())
            .ok_or_else(|| Error::parse(format!("expected a local `_N`, found `{w}`")))
    }

    pub(crate) fn at_block_header(&self) -> bool {
        // `bbN:` or an annotated header `bbN (cleanup):` — the latter must still be
        // recognised, or the block loop would stop early and silently DROP every
        // following block (which may contain a memory access → an unsound vacuous
        // PASS). So a `bbN` followed by `:` or `(` starts a block.
        matches!(self.peek(), Tok::Word(w) if is_bb(w))
            && matches!(self.peek2(), Tok::Punct(':') | Tok::Punct('('))
    }

    /// Collect every `let [mut] _N: T;` in the preamble (descending through
    /// `scope { … }` is automatic — we only act on `let` and skip everything else),
    /// stopping at the first block header. Fully tolerant: a declaration whose type
    /// will not parse is skipped, never aborting the body — preserving the old
    /// skip-the-whole-preamble robustness while capturing the types that do parse.
    pub(crate) fn parse_locals(&mut self) -> Vec<(Local, MType)> {
        let mut locals = Vec::new();
        while !matches!(self.peek(), Tok::Eof) && !self.at_block_header() {
            if matches!(self.peek(), Tok::Word(w) if w == "let") {
                self.pos += 1; // `let`
                if matches!(self.peek(), Tok::Word(w) if w == "mut") {
                    self.pos += 1;
                }
                let decl = self.local().ok().filter(|_| self.eat_punct(':')).and_then(|l| {
                    let ty = self.ty().ok()?;
                    Some((l, ty))
                });
                if let Some(d) = decl {
                    locals.push(d);
                }
                // Recover to the terminating `;` (an array type's inner `;` was
                // consumed by `ty()`), tolerant of a partially-parsed declaration.
                while !matches!(self.peek(), Tok::Eof | Tok::Punct(';')) && !self.at_block_header() {
                    self.pos += 1;
                }
                self.eat_punct(';');
            } else {
                self.pos += 1;
            }
        }
        locals
    }

    pub(crate) fn block(&mut self) -> Result<MBlock> {
        let w = self.word()?;
        let id = bb_index(&w).ok_or_else(|| Error::parse(format!("bad block label `{w}`")))?;
        // An optional block annotation, e.g. `bbN (cleanup):`.
        if self.eat_punct('(') {
            self.skip_balanced_paren();
        }
        self.expect_punct(':')?;
        self.expect_punct('{')?;
        let mut stmts = Vec::new();
        let mut stmt_spans = Vec::new();
        let (term, term_span) = loop {
            let at = self.pos;
            if let Some(t) = self.try_terminator()? {
                break (t, self.loc_at(at));
            }
            // An assignment-form terminator (`_0 = f(args) -> [return: bb, …]`)
            // reads like a statement but ends in `->` rather than `;`: a call.
            if self.stmt_is_terminator() {
                let t = self.call_terminator()?;
                let _ = self.eat_punct(';');
                break (t, self.loc_at(at));
            }
            stmts.push(self.statement()?);
            stmt_spans.push(self.loc_at(at));
        };
        self.expect_punct('}')?;
        Ok(MBlock { id, stmts, stmt_spans, term, term_span })
    }

    /// Whether the upcoming statement is actually an assignment-form terminator:
    /// it reaches a top-level `->` before its `;` (or the block's `}`).
    pub(crate) fn stmt_is_terminator(&self) -> bool {
        let mut i = self.pos;
        let mut depth = 0i32;
        while let Some(t) = self.toks.get(i) {
            match t {
                Tok::Punct('(') | Tok::Punct('[') => depth += 1,
                Tok::Punct(')') | Tok::Punct(']') => depth -= 1,
                // A terminator edge is `-> [return: bb, …]` or `-> bbN`. A `->`
                // followed by anything else is a function-pointer type's return
                // arrow inside the rvalue (`_0 = f as fn(T) -> R`), *not* an edge —
                // keep scanning so the statement is not mis-read as a call.
                Tok::Arrow if depth == 0 => match self.toks.get(i + 1) {
                    Some(Tok::Punct('[')) => return true,
                    Some(Tok::Word(w)) if is_bb(w) => return true,
                    _ => {}
                },
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
    pub(crate) fn try_terminator(&mut self) -> Result<Option<MTerm>> {
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
    pub(crate) fn arrow_block(&mut self) -> Result<usize> {
        if self.peek() == &Tok::Arrow {
            self.pos += 1;
        }
        let w = self.word()?;
        bb_index(&w).ok_or_else(|| Error::parse(format!("expected a block after `->`, found `{w}`")))
    }

    /// `_dst = callee(args) -> [return: bb, …]`.
    pub(crate) fn call_terminator(&mut self) -> Result<MTerm> {
        let dst = self.place()?;
        self.expect_punct('=')?;
        let callee = self.callee_spec()?;
        self.expect_punct('(')?;
        let mut args = Vec::new();
        while !self.eat_punct(')') {
            args.push(self.operand()?);
            let _ = self.eat_punct(',');
        }
        let (target, unwind) = self.return_edge()?;
        Ok(MTerm::Call { dst, callee, args, target, unwind })
    }

    /// The callee of a call: an indirect function-pointer local (`move _N`), or
    /// a named path whose last identifier is the resolution key.
    pub(crate) fn callee_spec(&mut self) -> Result<CalleeSpec> {
        if self.eat_word("move") || self.eat_word("copy") {
            return Ok(match self.place()? {
                Place::Local(n) => CalleeSpec::Indirect(n),
                _ => CalleeSpec::Named(String::new()),
            });
        }
        let _ = self.eat_word("const");
        // Consume the path up to the argument `(`, keeping the last identifier at
        // depth 0 (the **function name**) — NOT a name inside a `::<…>` turbofish
        // (the generic type argument), balancing `<…>` / `[…]` in qualified paths.
        // (Previously the last identifier overall was kept, so `copy_nonoverlapping::<u8>`
        // was mis-named `u8`, losing the intrinsic — see the memcpy-intrinsic lowering.)
        let mut last = String::new();
        let mut depth = 0i32;
        loop {
            match self.peek() {
                Tok::Punct('(') if depth == 0 => break,
                Tok::Eof => break,
                Tok::Punct('<') | Tok::Punct('[') => depth += 1,
                Tok::Punct('>') | Tok::Punct(']') => depth -= 1,
                Tok::Word(w) if depth == 0 => last = w.clone(),
                _ => {}
            }
            self.pos += 1;
        }
        Ok(CalleeSpec::Named(last))
    }

    /// The `return`/`success` target of a call's edges (`None` ⇒ diverging).
    pub(crate) fn return_edge(&mut self) -> Result<(Option<usize>, Option<usize>)> {
        if self.peek() == &Tok::Arrow {
            self.pos += 1;
        }
        if self.eat_punct('[') {
            let mut target = None;
            let mut unwind = None;
            while !self.eat_punct(']') {
                let key = self.word()?;
                if self.eat_punct(':') {
                    let bb = self.arrow_block_bare()?;
                    if key == "return" || key == "success" {
                        target = Some(bb);
                    } else if key == "unwind" {
                        // `unwind: bbN` — the cleanup block. Model it so its
                        // memory ops (drops/writes on the panic path) are checked.
                        unwind = Some(bb);
                    }
                } else if matches!(self.peek(), Tok::Word(_)) {
                    self.pos += 1; // an unwind action without a block
                    if self.eat_punct('(') {
                        self.skip_balanced_paren();
                    }
                }
                let _ = self.eat_punct(',');
            }
            Ok((target, unwind))
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
            Ok((None, None))
        } else {
            let w = self.word()?;
            Ok((bb_index(&w), None))
        }
    }

    pub(crate) fn switch_int(&mut self) -> Result<MTerm> {
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
    pub(crate) fn drop_term(&mut self) -> Result<MTerm> {
        self.pos += 1; // drop
        self.expect_punct('(')?;
        let _ = self.place()?;
        self.expect_punct(')')?;
        let (target, unwind) = self.return_edge()?;
        Ok(MTerm::Drop { target, unwind })
    }

    pub(crate) fn assert_term(&mut self) -> Result<MTerm> {
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
    pub(crate) fn success_block(&mut self) -> Result<usize> {
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
    pub(crate) fn arrow_block_bare(&mut self) -> Result<usize> {
        let w = self.word()?;
        bb_index(&w).ok_or_else(|| Error::parse(format!("expected a block, found `{w}`")))
    }
}
