use super::*;

impl Parser {
    pub(crate) fn ty(&mut self) -> Result<MType> {
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
                // A function-pointer type, possibly higher-ranked / qualified:
                // `for<'a> unsafe extern "C" fn(&'a T, U) -> R` (e.g. a vtable
                // entry). Consume the binder/qualifiers, the `fn(args)`, and any
                // `-> ret`, opaquely.
                if w == "for" {
                    self.skip_balanced_angle(); // the `for<'a>` binder
                    return self.ty();
                }
                if w == "unsafe" || w == "extern" {
                    if w == "extern" {
                        if let Tok::Str(_) = self.peek() {
                            self.pos += 1; // the ABI string, e.g. `"C"`
                        }
                    }
                    return self.ty();
                }
                if w == "fn" {
                    if self.eat_punct('(') {
                        self.skip_balanced_paren();
                    }
                    if self.peek() == &Tok::Arrow {
                        self.pos += 1;
                        let _ = self.ty()?;
                    }
                    return Ok(MType::Other);
                }
                // A named type may be a qualified path with generic arguments
                // (`core::option::Option<i32>`, `Vec<T>`); consume the whole path
                // tail so the type lowers to `Other`, not a parse error. The inner
                // element types are not needed (the aggregate is opaque-size; a
                // field access carries its own type ascription).
                // An interior-mutable wrapper (`Cell`/`UnsafeCell`/`Mutex`/…) in the path — the
                // first segment or any tail segment — flags the type so the aliasing model does
                // not track a shared borrow of it (interior mutability writes through `&`).
                let mut interior = is_interior_mut_name(&w);
                interior |= self.skip_path_tail_interior();
                let ty = if interior { MType::InteriorMut } else { int_type(&w).unwrap_or(MType::Other) };
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
            // The never type `!` (e.g. a `-> !` diverging return).
            Tok::Punct('!') => {
                self.pos += 1;
                Ok(MType::Unit)
            }
            _ => Ok(MType::Other),
        }
    }

    pub(crate) fn skip_balanced_paren(&mut self) {
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
    pub(crate) fn skip_balanced_braces(&mut self) {
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
    pub(crate) fn skip_balanced_angle(&mut self) {
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
    pub(crate) fn skip_trait_bounds(&mut self) {
        loop {
            // A higher-ranked binder (`for<'a>`) prefixes the trait, not a trait
            // itself: consume the `<…>` and fall through to the real trait
            // (`dyn for<'a> core::ops::Fn(&'a T) -> R`). Without this, `for` was
            // taken as the trait name and the binder stopped the scan, leaving
            // the trait path unconsumed and desyncing the parser.
            if matches!(self.peek(), Tok::Word(w) if w == "for") {
                self.pos += 1;
                if self.peek() == &Tok::Punct('<') {
                    self.skip_balanced_angle();
                }
            }
            if matches!(self.peek(), Tok::Word(_)) {
                self.pos += 1;
                self.skip_path_tail();
                // `Fn`/`FnMut`/`FnOnce` sugar — `Fn(Args) -> R` — has a
                // parenthesised argument list and an optional return type.
                if self.eat_punct('(') {
                    self.skip_balanced_paren();
                    if self.peek() == &Tok::Arrow {
                        self.pos += 1;
                        let _ = self.ty();
                    }
                }
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
    pub(crate) fn skip_path_tail(&mut self) {
        let _ = self.skip_path_tail_interior();
    }

    /// As [`skip_path_tail`], returning whether any consumed path segment is an interior-mutable
    /// wrapper name (so `std::cell::Cell<i32>` is detected from its `Cell` tail segment).
    pub(crate) fn skip_path_tail_interior(&mut self) -> bool {
        let mut interior = false;
        loop {
            match self.peek() {
                Tok::Punct('<') => self.skip_balanced_angle(),
                Tok::Punct(':') if self.peek2() == &Tok::Punct(':') => {
                    self.pos += 2; // `::`
                    match self.peek().clone() {
                        Tok::Punct('<') => self.skip_balanced_angle(), // turbofish
                        Tok::Word(w) => {
                            interior |= is_interior_mut_name(&w);
                            self.pos += 1; // a path segment
                        }
                        _ => {}
                    }
                }
                _ => break,
            }
        }
        interior
    }
}
