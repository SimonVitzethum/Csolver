use super::*;

impl Parser {
    pub(crate) fn function(&mut self) -> Result<LFunc> {
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
                let (deref, align, readonly, writeonly, nonnull, abi_buf) = self.param_attrs()?;
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
                    nonnull,
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

    pub(crate) fn blocks(&mut self, param_count: usize) -> Result<Vec<LBlock>> {
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

    pub(crate) fn try_terminator(&mut self) -> Result<Option<LTerm>> {
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
    pub(crate) fn skip_landingpad_clauses(&mut self) {
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
}
