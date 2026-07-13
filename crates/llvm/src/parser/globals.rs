use super::*;

impl Parser {
    /// Parse a top-level global definition line; `None` (with the line
    /// consumed) when it is not a sizable definition (alias, ifunc, or an
    /// unsupported type).
    pub(crate) fn global_def(&mut self) -> Option<LGlobal> {
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
    pub(crate) fn scan_init_value(
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
    pub(crate) fn eat_aggregate_zero(&mut self) -> bool {
        self.eat_word("zeroinitializer") || self.eat_word("undef") || self.eat_word("poison")
    }

    /// Parse `<{ T, T, … }>` (a packed struct type), resolving named fields;
    /// restores the position on any mismatch.
    pub(crate) fn packed_struct_type(&mut self) -> Option<Vec<LType>> {
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
}
