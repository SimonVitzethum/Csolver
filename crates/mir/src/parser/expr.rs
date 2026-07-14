use super::*;

impl Parser {
    pub(crate) fn statement(&mut self) -> Result<MStmt> {
        // No-effect statements: skip to `;`.
        if let Tok::Word(w) = self.peek().clone() {
            // `StorageLive(_N)` / `StorageDead(_N)` carry the local whose stack storage begins/ends
            // — captured (not skipped) so an address-taken local's scope can be modelled for
            // use-after-scope.
            if w == "StorageLive" || w == "StorageDead" {
                self.pos += 1;
                let local = if self.eat_punct('(') {
                    let l = self.local().ok();
                    let _ = self.eat_punct(')');
                    l
                } else {
                    None
                };
                self.skip_statement();
                return Ok(match (w.as_str(), local) {
                    ("StorageLive", Some(l)) => MStmt::StorageLive(l),
                    ("StorageDead", Some(l)) => MStmt::StorageDead(l),
                    _ => MStmt::Nop,
                });
            }
            if matches!(
                w.as_str(),
                "nop" | "FakeRead" | "AscribeUserType" | "Retag"
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
    pub(crate) fn skip_statement(&mut self) {
        while !matches!(self.peek(), Tok::Eof) {
            let t = self.bump();
            if t == Tok::Punct(';') {
                break;
            }
        }
    }

    pub(crate) fn place(&mut self) -> Result<Place> {
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
                // `[_M]` (runtime local), `[N of M]` / `[N]` (constant index), or
                // a subslice range `[from:to]` / `[from:]` / `[:to]` / `[:]`
                // (MIR's `Subslice`), modelled by its *start* element pointer —
                // sound for the pointer; the length change is over-approximated.
                if self.eat_punct(':') {
                    // `[:to]` — starts at 0.
                    if matches!(self.peek(), Tok::Int(_)) { self.pos += 1; }
                    self.expect_punct(']')?;
                    base = Place::ConstIndex(Box::new(base), 0);
                } else if let Tok::Int(n) = *self.peek() {
                    self.pos += 1;
                    if self.eat_punct(':') {
                        // `[from:to]` / `[from:]` — start element is `from`.
                        if matches!(self.peek(), Tok::Int(_)) { self.pos += 1; }
                        self.expect_punct(']')?;
                    } else {
                        // `[N of M]` — the `of M` min-length is discarded.
                        if self.eat_word("of") {
                            let _ = self.int_lit();
                        }
                        self.expect_punct(']')?;
                    }
                    base = Place::ConstIndex(Box::new(base), n as u64);
                } else {
                    let idx = self.local()?;
                    self.expect_punct(']')?;
                    base = Place::Index(Box::new(base), idx);
                }
            } else if self.eat_punct('.') {
                let field = self.field_index()?;
                base = Place::Field(Box::new(base), field, None);
            } else {
                break;
            }
        }
        Ok(base)
    }

    pub(crate) fn field_index(&mut self) -> Result<u32> {
        match self.bump() {
            Tok::Int(n) => Ok(n as u32),
            // `.field` named projections are not modelled precisely; treat the
            // ordinal as unknown (0) — a field place still yields a sound
            // (opaque) lowering downstream.
            Tok::Word(_) => Ok(0),
            other => Err(Error::parse(format!("expected a field index, found {other:?}"))),
        }
    }

    pub(crate) fn rvalue(&mut self) -> Result<Rvalue> {
        // `&PLACE` / `&mut PLACE` / `&raw const PLACE` / `&raw const (fake) PLACE`.
        if self.eat_punct('&') {
            let mut kind = if self.eat_word("mut") { RefKind::Mut } else { RefKind::Shared };
            if self.eat_word("raw") {
                // `&raw mut PLACE` is a unique borrow; `&raw const PLACE` a shared one.
                kind = if self.eat_word("mut") {
                    RefKind::Mut
                } else {
                    let _ = self.eat_word("const");
                    RefKind::Shared
                };
            }
            // A parenthesised borrow-kind annotation, distinguished from the place `(*_p)` by
            // its leading keyword. A `two_phase` `&mut` is modelled as a **shared** reborrow: its
            // reservation phase legitimately coexists with the parent (a shared tag never pops a
            // sibling — sound, no false FAIL — while a real aliasing `&mut` write through a lower
            // tag still invalidates it, so it is not merely dropped). A `fake`/`shallow` borrow is
            // not a real reborrow at all → `Opaque` (no marker).
            if self.peek() == &Tok::Punct('(') {
                match self.peek2() {
                    Tok::Word(w) if w == "two_phase" => {
                        kind = RefKind::Shared;
                        self.pos += 1;
                        self.skip_balanced_paren();
                    }
                    Tok::Word(w) if matches!(w.as_str(), "fake" | "shallow" | "shared") => {
                        kind = RefKind::Opaque;
                        self.pos += 1;
                        self.skip_balanced_paren();
                    }
                    _ => {}
                }
            }
            return Ok(Rvalue::Ref(self.place()?, kind));
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
    pub(crate) fn skip_statement_inline(&mut self) {
        while !matches!(self.peek(), Tok::Punct(';') | Tok::Eof) {
            self.pos += 1;
        }
    }

    pub(crate) fn operand(&mut self) -> Result<Operand> {
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
    pub(crate) fn starts_place(&self) -> bool {
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
    pub(crate) fn paren_is_tuple(&self) -> bool {
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
    pub(crate) fn skip_opaque_value(&mut self) {
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

    pub(crate) fn constant(&mut self) -> Result<MConst> {
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

    pub(crate) fn int_lit(&mut self) -> Result<i128> {
        match self.bump() {
            Tok::Int(n) => Ok(n),
            other => Err(Error::parse(format!("expected an integer, found {other:?}"))),
        }
    }
}
