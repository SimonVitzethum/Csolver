//! # csolver-mir — Rust MIR frontend
//!
//! Lowers a practical subset of **textual Rust MIR** (as emitted by `rustc
//! --emit=mir` / `-Zunpretty=mir`) into MSIR, in pure Rust — no `rustc` linkage,
//! mirroring how [`csolver_llvm`] consumes `.ll` text rather than linking LLVM.
//!
//! MIR is the richest input for memory safety: the bounds/overflow checks rustc
//! inserts are **explicit terminators** (`assert(Lt(i, len)) -> success: bb`),
//! so a checked index `s[i]` is *proved* in bounds precisely because the check
//! is present — the panic edge sharpens the obligation. The lowering turns an
//! `assert` into a `CondBr` whose success edge carries the guard and whose
//! failure edge diverges to an `unreachable` panic block; a sized reference
//! parameter (`&[T; N]`, `&T`, `&mut T`) becomes a contracted region; and an
//! index/deref place becomes a `PtrOffset` + `Load`/`Store`.
//!
//! Anything outside the modelled subset (a `call`, an unmodelled rvalue, a
//! slice's symbolic length) is surfaced — the affected function is recorded as
//! unanalyzed (reported `UNKNOWN`) rather than silently mis-modelled.

mod lexer;
mod lower;
mod parser;

use csolver_core::Result;
use csolver_ir::{Frontend, Module};

/// Input to the MIR frontend: a textual MIR dump and a module name.
#[derive(Debug, Clone)]
pub struct MirInput {
    /// The MIR source text (`rustc --emit=mir` output).
    pub source: String,
    /// A name for the resulting module.
    pub name: String,
}

/// The Rust MIR frontend.
#[derive(Debug, Default, Clone, Copy)]
pub struct MirFrontend;

impl Frontend for MirFrontend {
    type Input = MirInput;

    fn name(&self) -> &'static str {
        "mir"
    }

    fn lower(&self, input: MirInput) -> Result<Module> {
        let (bodies, failed) = parser::parse_module(&input.source)?;
        Ok(lower::lower_module(&bodies, &failed, &input.name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A real `rustc`-MIR shape of `fn get(s: &[i32; 8], i: usize) -> i32 { s[i] }`:
    /// the bounds-check `assert` guards the indexed load.
    const GET: &str = r#"
fn get(_1: &[i32; 8], _2: usize) -> i32 {
    debug s => _1;
    debug i => _2;
    let mut _0: i32;
    let mut _3: bool;
    bb0: {
        _3 = Lt(_2, const 8_usize);
        assert(move _3, "index out of bounds: the length is {} but the index is {}", const 8_usize, _2) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = (*_1)[_2];
        return;
    }
}
"#;

    #[test]
    fn parses_and_lowers_a_checked_index() {
        let module = MirFrontend
            .lower(MirInput { source: GET.into(), name: "get".into() })
            .expect("the MIR frontend lowers the body");
        assert_eq!(module.functions.len(), 1);
        assert!(module.unanalyzed.is_empty());
        let f = &module.functions[0];
        assert_eq!(f.name, "get");
        // A region contract was recorded for the `&[i32; 8]` parameter.
        assert!(module.param_contracts.contains_key(&(csolver_ir::FuncId(0), 0)));
        // The indexed load lowered to a PtrOffset + Load in bb1.
        let bb1 = f.block(csolver_ir::BlockId(1)).expect("bb1");
        assert!(bb1.insts.iter().any(|i| matches!(i, csolver_ir::Inst::PtrOffset { .. })));
        assert!(bb1.insts.iter().any(|i| matches!(i, csolver_ir::Inst::Load { .. })));
    }

    /// Checked arithmetic is modelled by its result: `_3 = AddWithOverflow(_1,
    /// _2); _4 = move (_3.0)` makes `_4` the actual sum `_1 + _2` (an `Add`
    /// instruction), not an opaque unknown — so a checked value used downstream
    /// keeps its meaning. The overflow flag `_3.1` stays opaque.
    const CHECKED: &str = r#"
fn add(_1: u32, _2: u32) -> u32 {
    let mut _0: u32;
    let mut _3: (u32, bool);
    bb0: {
        _3 = AddWithOverflow(copy _1, copy _2);
        assert(!move (_3.1: bool), "overflow", copy _1, copy _2) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = move (_3.0: u32);
        return;
    }
}
"#;

    #[test]
    fn models_checked_arithmetic_result() {
        let module = MirFrontend
            .lower(MirInput { source: CHECKED.into(), name: "add".into() })
            .expect("lower");
        let f = &module.functions[0];
        // The result of the checked add became a real `Add` instruction…
        let has_add = f.blocks.iter().flat_map(|b| &b.insts).any(|i| {
            matches!(i, csolver_ir::Inst::Assign { value: csolver_ir::RValue::Bin { op: csolver_ir::BinOp::Add, .. }, .. })
        });
        assert!(has_add, "the checked add's result is a real Add, not opaque");
        // …and `_0 = move (_3.0)` forwards that result (no `Undef`).
        let bb1 = f.block(csolver_ir::BlockId(1)).expect("bb1");
        let forwards = bb1.insts.iter().any(|i| matches!(
            i,
            csolver_ir::Inst::Assign { dst, value: csolver_ir::RValue::Use(csolver_ir::Operand::Reg(_)), .. }
                if *dst == csolver_ir::RegId(0)
        ));
        assert!(forwards, "_0 forwards the checked result register, not Undef");
    }
}
