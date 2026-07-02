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

    /// rustc's checked arithmetic (`x + 1` in debug) is a `{iN, i1}`
    /// `llvm.sadd.with.overflow` + `extractvalue`; field 0 must recover the
    /// addition (so a later use as an index/bound can be reasoned about), field 1
    /// (the overflow flag) stays opaque.
    #[test]
    fn checked_arithmetic_recovers_the_operation() {
        let src = r#"
define i32 @add_one(i32 %x) {
start:
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %x, i32 1)
  %s = extractvalue { i32, i1 } %0, 0
  %o = extractvalue { i32, i1 } %0, 1
  br i1 %o, label %panic, label %ok
ok:
  ret i32 %s
panic:
  ret i32 0
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        let has_add = module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.insts)
            .any(|i| {
                matches!(i, csolver_ir::Inst::Assign {
                    value: csolver_ir::RValue::Bin { op: csolver_ir::BinOp::Add, .. }, ..
                })
            });
        assert!(has_add, "checked-add field 0 must recover the addition");
    }

    /// A panic-unwind cleanup path (`landingpad` + `insertvalue` + `resume`, with a
    /// `personality`) carries no memory-safety content and must not drop the whole
    /// function — before, every real obligation was dropped with it. rustc emits
    /// this in every monomorphised library function that can unwind.
    #[test]
    fn unwind_cleanup_does_not_drop_the_function() {
        let src = r#"
define i32 @f(i32 %x) personality ptr @rust_eh_personality {
start:
  %s = add i32 %x, 1
  ret i32 %s
cleanup:
  %e = landingpad { ptr, i32 }
          cleanup
  %a = insertvalue { ptr, i32 } %e, i32 0, 1
  resume { ptr, i32 } %a
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        assert!(
            module.unanalyzed.is_empty(),
            "an unwind-cleanup path must not drop the function: {:?}",
            module.unanalyzed
        );
        assert_eq!(module.functions.len(), 1);
    }

    /// `invoke` (a call with an unwind edge) plus a `getelementptr`/`inttoptr`
    /// constant-expression argument — both pervasive in rustc IR. The function must
    /// lower (not be dropped), and the invoke must branch to *both* its normal and
    /// unwind-cleanup successors (so the cleanup path is analysed, not ignored).
    #[test]
    fn invoke_and_const_expr_do_not_drop_the_function() {
        let src = r#"
define i32 @f(ptr %p) personality ptr @rust_eh_personality {
start:
  %r = invoke i32 @g(ptr %p, ptr inttoptr (i64 7 to ptr)) to label %ok unwind label %cleanup
ok:
  ret i32 %r
cleanup:
  %e = landingpad { ptr, i32 } cleanup
  resume { ptr, i32 } %e
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        assert!(
            module.unanalyzed.is_empty(),
            "invoke + const-expr must not drop the function: {:?}",
            module.unanalyzed
        );
        let f = &module.functions[0];
        // The invoke's block branches to both successors (CondBr), not just the
        // normal one — the unwind edge is modelled.
        let start = f.blocks.iter().find(|b| b.id == csolver_ir::BlockId(0)).unwrap();
        assert!(
            matches!(start.term, csolver_ir::Terminator::CondBr { .. }),
            "invoke must branch to both its normal and unwind successors"
        );
    }

    /// Floating-point types and ops (`float`/`double`, `uitofp`, `fmul`, hex float
    /// constants) carry no memory-safety content — before, an `float` return type
    /// alone dropped the whole function (rustc emits this in every `f32`/`f64`
    /// routine). The function must analyse; its *memory* operation (the safe
    /// `alloca [4 x i8]` + store) must still be checked, and the float value stays
    /// opaque (so nothing about it can be mis-proven).
    #[test]
    fn float_types_and_ops_do_not_drop_the_function() {
        let src = r#"
define float @scale(i32 %x) {
start:
  %u = alloca [4 x i8], align 4
  store i32 %x, ptr %u, align 4
  %v = load i32, ptr %u, align 4
  %f = uitofp i32 %v to float
  %r = fmul float %f, 0x3E70000000000000
  ret float %r
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        assert!(
            module.unanalyzed.is_empty(),
            "a float-using function must not be dropped: {:?}",
            module.unanalyzed
        );
        // The store/load into the local `[4 x i8]` alloca are real memory ops that
        // must survive lowering (proving the float ops did not eat them).
        let f = &module.functions[0];
        let stores = f
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .filter(|i| matches!(i, csolver_ir::Inst::Store { .. }))
            .count();
        assert_eq!(stores, 1, "the store into the alloca must be preserved");
    }

    /// `sret([N x i8])` marks a caller-provided N-byte return buffer (rustc's ABI
    /// for returning aggregates — pervasive). It must become a `dereferenceable`-
    /// style size contract, and must *never* be paired with the next integer
    /// parameter by the slice heuristic: that sized the buffer by an arbitrary
    /// runtime value and refuted every store into it — a false FAIL on
    /// `RangeInclusive::new` and friends (a certain-wrong verdict, the worst kind).
    #[test]
    fn sret_buffer_gets_a_size_contract_not_a_slice_pairing() {
        let src = r#"
define void @new(ptr sret([24 x i8]) align 8 %_0, i64 %start1, i64 %end) {
start:
  store i64 %start1, ptr %_0, align 8
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %end, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_0, i64 16
  store i8 0, ptr %1, align 8
  ret void
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        let contracts: Vec<_> = module.param_contracts.values().collect();
        assert_eq!(contracts.len(), 1, "the sret param must carry exactly one contract");
        assert!(
            matches!(contracts[0].size, csolver_ir::SizeSpec::Bytes(24)),
            "sret([24 x i8]) must be a 24-byte contract, not a slice pairing: {:?}",
            contracts[0].size
        );
    }
}
