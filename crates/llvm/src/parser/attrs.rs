use super::*;

impl Parser {
    /// Parse a parameter's attributes (up to its `%name` / `,` / `)`),
    /// capturing the memory-safety-relevant ones and skipping the rest.
    #[allow(clippy::type_complexity)]
    pub(crate) fn param_attrs(&mut self) -> Result<(Option<u64>, Option<u32>, bool, bool, bool, Option<LType>)> {
        let mut deref = None;
        let mut align = None;
        let mut readonly = false;
        let mut writeonly = false;
        let mut nonnull = false;
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
                        // `nonnull`: the pointer is guaranteed non-null (no size/liveness
                        // guarantee — a `nonnull` pointer may still dangle). Recovered as a
                        // non-null-only contract (Zig `*T`, and any frontend that asserts it).
                        "nonnull" => nonnull = true,
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
        Ok((deref, align, readonly, writeonly, nonnull, abi_buf))
    }

    /// Skip a call argument's attributes up to its operand. Crucially, `align
    /// N` is skipped as a *pair* (so the alignment value `N` is not mistaken for
    /// the operand), and parenthesized attributes are skipped balanced.
    pub(crate) fn skip_arg_attrs(&mut self) -> Result<Option<u64>> {
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
    pub(crate) fn paren_u64(&mut self) -> Result<u64> {
        self.expect_punct('(')?;
        let n = self.int()?;
        self.expect_punct(')')?;
        Ok(n.max(0) as u64)
    }

    /// Skip attribute/linkage words (including parenthesized ones like
    /// `dereferenceable(32)`) up to the next token that can begin a type.
    pub(crate) fn skip_to_type(&mut self) -> Result<()> {
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
    pub(crate) fn skip_balanced(&mut self, open: char, close: char) -> Result<()> {
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
    pub(crate) fn skip_to_eol(&mut self) {
        while !matches!(self.peek(), Tok::Newline | Tok::Eof) {
            self.pos += 1;
        }
        if matches!(self.peek(), Tok::Newline) {
            self.pos += 1;
        }
    }

    /// Skip a function that failed to parse: extract its `@name` and advance
    /// past its `{ … }` body. Assumes the next token is `define`.
    pub(crate) fn recover_function(&mut self) -> String {
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
}
