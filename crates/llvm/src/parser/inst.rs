use super::*;

impl Parser {
    pub(crate) fn instruction(&mut self) -> Result<InstOrPhi> {
        // Assignment form: `%dst = <op> ...`.
        if matches!(self.peek(), Tok::Local(_)) && matches!(self.peek2(), Tok::Punct('=')) {
            let dst = self.local()?;
            self.expect_punct('=')?;
            return self.rhs(Some(dst));
        }
        // Void form: `store ...` / `call ...`.
        self.rhs(None)
    }

    pub(crate) fn rhs(&mut self, dst: Option<String>) -> Result<InstOrPhi> {
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
                let ordering = self.parse_atomic_ordering();
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
                    ordering,
                }
            }
            "store" => {
                let atomic = self.skip_memory_qualifiers();
                let ty = self.ltype()?;
                let val = self.value()?;
                self.expect_punct(',')?;
                let _pty = self.ltype()?;
                let ptr = self.value()?;
                let ordering = self.parse_atomic_ordering();
                let align = self.maybe_align().unwrap_or(0);
                LInst::Store {
                    ty,
                    val,
                    ptr,
                    align,
                    atomic,
                    ordering,
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
                self.parse_atomic_ordering();
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
                self.parse_atomic_ordering(); // consumes both orderings
                LInst::AtomicRmw {
                    dst: need_dst()?,
                    ty,
                    ptr,
                    tuple: true,
                }
            }
            "fence" => LInst::Fence { ordering: self.parse_atomic_ordering() },
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
                    // Capture the no-wrap flags (`nsw`/`nuw`); skip `exact`/`disjoint`
                    // which carry no memory-safety obligation here.
                    let (mut nsw, mut nuw) = (false, false);
                    while let Tok::Word(w) = self.peek() {
                        match w.as_str() {
                            "nsw" => nsw = true,
                            "nuw" => nuw = true,
                            "exact" | "disjoint" => {}
                            _ => break,
                        }
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
                        nsw,
                        nuw,
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

    pub(crate) fn gep(&mut self, dst: String) -> Result<LInst> {
        // Flags: `inbounds`, `nuw`, `nusw` in any combination.
        while self.eat_word("inbounds") || self.eat_word("nuw") || self.eat_word("nusw") {}
        // Capture the aggregate's *name* (from the unresolved type) before resolving it — the
        // struct name is otherwise substituted away, and it is the key into the DWARF struct.
        let base_raw = self.ltype_raw()?;
        let struct_name = if let LType::Named(n) = &base_raw { Some(n.clone()) } else { None };
        let base_ty = self.resolve_named(&base_raw, 0)?;
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
                    struct_name,
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
    pub(crate) fn callee_name(&mut self) -> Result<String> {
        match self.peek() {
            Tok::Local(n) => {
                let name = format!("<indirect via %{n}>");
                self.pos += 1;
                Ok(name)
            }
            _ => self.global(),
        }
    }

    pub(crate) fn call(&mut self, dst: Option<String>) -> Result<LInst> {
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
            let mut intel = false;
            while matches!(self.peek(), Tok::Word(w)
                if matches!(w.as_str(), "sideeffect" | "alignstack" | "inteldialect" | "unwind"))
            {
                if matches!(self.peek(), Tok::Word(w) if w == "inteldialect") {
                    intel = true;
                }
                self.pos += 1;
            }
            // The template and constraint strings (each a quoted `Word`), separated
            // by a comma; tolerate either being absent. The template text is kept for the
            // register-dataflow semantic decode (below).
            let mut template = String::new();
            if let Tok::Word(t) = self.peek() {
                template = t.clone();
                self.pos += 1;
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
            // Precise memory operands (`=*m`/`m`/…): appended as `|w<i>` (written) / `|r<i>`
            // (read) so the lowering emits a real access obligation on the pointer argument —
            // catching a UAF/OOB/null through an asm memory operand — on top of the sound
            // clobber/nomem classification.
            let mut name = if asm_may_write_memory(&constraints) {
                "<inline asm>".to_string()
            } else {
                "<inline asm nomem>".to_string()
            };
            for (arg, is_write) in asm_memory_operands(&constraints) {
                name.push_str(&format!("|{}{arg}", if is_write { 'w' } else { 'r' }));
            }
            // Register-dataflow semantic decode: for a recognized single-instruction template
            // whose output is a *provable* function of its inputs (a copy/`mov`, or a `xor r,r`
            // zero idiom), append `|sem…` so the lowering binds the output register to that value
            // instead of an opaque havoc. Only unambiguous, always-correct idioms are recognized;
            // anything else stays havoc'd (sound). See `asm_reg_semantic`.
            if let Some(sem) = asm_reg_semantic(&template, &constraints, intel) {
                name.push_str(&sem);
            }
            name
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

    pub(crate) fn phi(&mut self, dst: String) -> Result<LPhi> {
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

    pub(crate) fn pred(&mut self) -> Result<LPred> {
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
