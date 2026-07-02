//! # csolver-llvm — LLVM-IR frontend
//!
//! Lowers a practical subset of textual LLVM IR (`.ll`) into MSIR, so the
//! audited MSIR analysis core can verify code compiled from Rust without any
//! change. The structural work is PHI elimination (PHIs become MSIR block
//! parameters; see [`lower`]).
//!
//! ## Supported subset
//!
//! `define`d functions; `void`/`iN`/`ptr`/`[N x T]` types (and legacy `T*`);
//! `alloca`, `load`, `store`, `getelementptr` (pointer-arith and array forms),
//! the integer binary ops, `icmp`, the integer/pointer casts, `call`, `phi`;
//! and the `ret`/`br`/`unreachable` terminators. Constructs outside the subset
//! (vectors, exceptions, `switch`, metadata, complex GEPs, …) are reported as
//! [`csolver_core::Error::Unsupported`] so the caller degrades to `UNKNOWN`
//! rather than silently mis-modelling them — the sound default.
//!
//! ## Soundness obligation
//!
//! The lowering must refine the LLVM semantics (every concrete `.ll` execution
//! is a concrete MSIR execution). The mapping is opcode-local and documented in
//! [`lower`]; see `Verification/`.

mod lexer;
mod lower;
mod parser;

pub use lower::lower_module;
pub use parser::{parse_module, LModule};

use csolver_core::Result;
use csolver_ir::{Frontend, Module};

/// LLVM-IR source input.
#[derive(Debug, Clone)]
pub struct LlvmInput {
    /// The textual `.ll` module.
    pub source: String,
    /// A name for diagnostics (e.g. the file name).
    pub name: String,
}

/// The LLVM-IR frontend.
#[derive(Debug, Default, Clone, Copy)]
pub struct LlvmFrontend;

impl Frontend for LlvmFrontend {
    type Input = LlvmInput;

    fn name(&self) -> &'static str {
        "llvm"
    }

    fn lower(&self, input: LlvmInput) -> Result<Module> {
        let parsed = parse_module(&input.source)?;
        lower_module(&parsed, &input.name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// End-to-end: a `.ll` with a guarded `[8 x i32]` store parses, lowers, and
    /// has the expected MSIR shape (1 function, 4 blocks, an alloc + a gep + a
    /// store).
    #[test]
    fn lowers_guarded_store() {
        let src = r#"
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
        let module = LlvmFrontend
            .lower(LlvmInput {
                source: src.into(),
                name: "m".into(),
            })
            .expect("lower");
        assert_eq!(module.functions.len(), 1);
        let f = &module.functions[0];
        assert_eq!(f.name, "make_and_store");
        assert_eq!(f.blocks.len(), 4);

        // The body block holds the pointer arithmetic and the store.
        let has_gep = f
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .any(|i| matches!(i, csolver_ir::Inst::PtrOffset { .. }));
        let has_store = f
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .any(|i| matches!(i, csolver_ir::Inst::Store { .. }));
        assert!(has_gep && has_store);
    }

    /// Regression: `fn(ptr align 4, i64 %i)` where `%i` indexes the pointer is an
    /// *index* argument, not a slice — the pointer must not get a `ParamElements`
    /// contract sized by the index (which refuted every access, a false FAIL that
    /// the MIR frontend, having the array type, proves PASS).
    #[test]
    fn index_arg_is_not_mistaken_for_a_slice_length() {
        let src = r#"
define i32 @get(ptr align 4 %a, i64 %i) {
entry:
  %p = getelementptr inbounds i32, ptr %a, i64 %i
  %v = load i32, ptr %p, align 4
  ret i32 %v
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        assert!(
            module.param_contracts.is_empty(),
            "an index argument must not become a slice length: {:?}",
            module.param_contracts
        );
    }
}
