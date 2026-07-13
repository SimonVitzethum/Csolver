use super::*;

impl Parser {
    pub(crate) fn peek(&self) -> &Tok {
        &self.toks[self.pos]
    }
    pub(crate) fn peek2(&self) -> &Tok {
        self.toks.get(self.pos + 1).unwrap_or(&Tok::Eof)
    }
    pub(crate) fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    pub(crate) fn expect_punct(&mut self, c: char) -> Result<()> {
        match self.bump() {
            Tok::Punct(p) if p == c => Ok(()),
            other => Err(Error::parse(format!("expected `{c}`, found {other:?}"))),
        }
    }
    pub(crate) fn expect_word(&mut self, w: &str) -> Result<()> {
        match self.bump() {
            Tok::Word(x) if x == w => Ok(()),
            other => Err(Error::parse(format!("expected `{w}`, found {other:?}"))),
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
    pub(crate) fn global(&mut self) -> Result<String> {
        match self.bump() {
            Tok::Global(s) => Ok(s),
            other => Err(Error::parse(format!(
                "expected global @name, found {other:?}"
            ))),
        }
    }
    pub(crate) fn local(&mut self) -> Result<String> {
        match self.bump() {
            Tok::Local(s) => Ok(s),
            other => Err(Error::parse(format!(
                "expected local %name, found {other:?}"
            ))),
        }
    }

    /// Pre-scan the token stream for top-level `%"name" = type <T>` definitions.
    /// Runs before function parsing; leaves `self.pos` at the end of input.
    pub(crate) fn collect_type_defs(&mut self) {
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
    pub(crate) fn resolve_named(&self, ty: &LType, depth: u32) -> Result<LType> {
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
    pub(crate) fn ltype(&mut self) -> Result<LType> {
        let raw = self.ltype_raw()?;
        self.resolve_named(&raw, 0)
    }

    pub(crate) fn ltype_raw(&mut self) -> Result<LType> {
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
    pub(crate) fn struct_fields(&mut self) -> Result<Vec<LType>> {
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

    pub(crate) fn int(&mut self) -> Result<i128> {
        match self.bump() {
            Tok::Int(n) => Ok(n),
            other => Err(Error::parse(format!("expected integer, found {other:?}"))),
        }
    }

    pub(crate) fn value(&mut self) -> Result<LValue> {
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
                let is_ptr_cast = matches!(w.as_str(), "bitcast" | "inttoptr");
                let mut j = self.pos;
                while matches!(self.toks.get(j), Some(Tok::Word(_))) {
                    j += 1;
                }
                if matches!(self.toks.get(j), Some(Tok::Punct('('))) {
                    self.pos = j;
                    // The folded global-displacement form —
                    // `getelementptr inbounds (T, ptr @g, iN K)` — keeps its
                    // base symbol and offset, so a load/store through it can be
                    // checked against the global's region.
                    if is_gep {
                        if let Some(v) = self.try_const_gep() {
                            return Ok(v);
                        }
                    }
                    // A pointer-identity cast of a symbol address — `bitcast (ptr @f to
                    // ptr)` / `inttoptr (… @f …)` — IS that symbol's address (the cast is a
                    // no-op on the pointer). Recover the inner `@symbol` so a function
                    // pointer stored in a constant table (a vtable / ops-struct field) is
                    // devirtualisable, instead of the opaque `Undef` the body would give.
                    if is_ptr_cast {
                        if let Some(sym) = self.first_global_in_balanced() {
                            self.skip_balanced('(', ')')?;
                            return Ok(LValue::Global(sym));
                        }
                    }
                    // Any other constant expression is consumed opaquely.
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
    pub(crate) fn skip_memory_qualifiers(&mut self) -> bool {
        let mut atomic = false;
        while self.eat_word("atomic") || self.eat_word("volatile") {
            atomic = true;
        }
        atomic
    }

    /// Parse an atomic access's trailing `syncscope("…")` and ordering keyword
    /// (`load atomic i32, ptr %p seq_cst, align 4`), returning the ordering so the
    /// lowering can emit the fence it guarantees.
    pub(crate) fn parse_atomic_ordering(&mut self) -> LOrdering {
        if self.eat_word("syncscope") && matches!(self.peek(), Tok::Punct('(')) {
            let _ = self.skip_balanced('(', ')');
        }
        let mut ord = LOrdering::None;
        while let Tok::Word(w) = self.peek() {
            let next = match w.as_str() {
                "acquire" => LOrdering::Acquire,
                "release" => LOrdering::Release,
                "acq_rel" => LOrdering::AcqRel,
                "seq_cst" => LOrdering::SeqCst,
                "unordered" | "monotonic" => LOrdering::None,
                _ => break,
            };
            // Keep the strongest ordering seen (an access carries exactly one).
            ord = next;
            self.pos += 1;
        }
        ord
    }

    /// Try the folded constant-gep form `( T , ptr @g , iN K )` with the
    /// opening paren as the next token. On success the group is consumed; on
    /// any mismatch the position is restored (`None`) so the caller can skip
    /// the group opaquely.
    /// The first `@symbol` token inside the balanced `(…)` group starting at the current
    /// position (which must be at the opening `(`), WITHOUT consuming any tokens. Used to
    /// recover the symbol of a pointer-identity const-expr cast (`bitcast`/`inttoptr`).
    pub(crate) fn first_global_in_balanced(&self) -> Option<String> {
        let mut depth = 0i32;
        let mut i = self.pos;
        while let Some(t) = self.toks.get(i) {
            match t {
                Tok::Punct('(') => depth += 1,
                Tok::Punct(')') => {
                    depth -= 1;
                    if depth == 0 {
                        return None;
                    }
                }
                Tok::Global(s) => return Some(s.clone()),
                _ => {}
            }
            i += 1;
        }
        None
    }

    pub(crate) fn try_const_gep(&mut self) -> Option<LValue> {
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
    pub(crate) fn maybe_align(&mut self) -> Option<u32> {
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
    pub(crate) fn peek_load_align_meta(&self) -> Option<u32> {
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
    pub(crate) fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline) {
            self.pos += 1;
        }
    }
}
