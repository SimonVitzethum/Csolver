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

mod debuginfo;
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

    /// Regression: an integer **wider than 128 bits** (kernel crypto / SIMD
    /// big-integers, e.g. `i256`) must lower without panicking. The 128-bit concrete
    /// value domain cannot hold it, so such a constant becomes an opaque `Undef` — a
    /// sound over-approximation — instead of aborting the whole (whole-program) run.
    #[test]
    fn wide_integer_constant_lowers_to_undef_not_panic() {
        let src = r#"
define i256 @wide() {
entry:
  %x = add i256 5, 1
  ret i256 %x
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("a >128-bit integer must lower, not panic");
        assert_eq!(module.functions.len(), 1);
        // The add's operands (an `i256` constant) degraded to the opaque unknown.
        let has_undef = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .any(|i| matches!(
                i,
                csolver_ir::Inst::Assign {
                    value: csolver_ir::RValue::Bin { lhs, rhs, .. }, ..
                } if matches!(lhs, csolver_ir::Operand::Const(csolver_ir::Const::Undef))
                    || matches!(rhs, csolver_ir::Operand::Const(csolver_ir::Const::Undef))
            ));
        assert!(has_undef, "a >128-bit int constant should lower to Undef");
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

    /// `select i1 %c, ptr %a, ptr %b` lowers to `RValue::Select` (not an opaque
    /// value), so the executor keeps both pointers as a provenance join and proves an
    /// access through the result in-bounds for each alternative.
    #[test]
    fn pointer_select_lowers_to_rvalue_select() {
        let src = r#"
define ptr @pick(i1 %c, ptr %a, ptr %b) {
e:
  %p = select i1 %c, ptr %a, ptr %b
  ret ptr %p
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        let has_select = module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.insts)
            .any(|i| matches!(i, csolver_ir::Inst::Assign { value: csolver_ir::RValue::Select { .. }, .. }));
        assert!(has_select, "select must lower to RValue::Select, not an opaque value");
    }

    /// Acquire/release atomic helpers, when they appear as out-of-line calls, lower to the
    /// corresponding weak-memory barrier: a `*_release` to a write barrier (orders prior stores
    /// before it), a `*_acquire` to a read barrier (orders subsequent loads after it).
    #[test]
    fn acquire_release_atomics_lower_to_barriers() {
        use csolver_ir::Inst;
        let src = "\
            declare void @atomic_set_release(ptr, i32)\ndeclare i32 @smp_load_acquire(ptr)\n\
            define void @f(ptr %p) {\nb:\n\
              call void @atomic_set_release(ptr %p, i32 1)\n\
              %v = call i32 @smp_load_acquire(ptr %p)\n  ret void\n}\n";
        let m = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        let kinds: Vec<u8> = m
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.insts)
            .filter_map(|i| match i {
                Inst::Barrier { kind } => Some(*kind),
                _ => None,
            })
            .collect();
        assert!(kinds.contains(&1), "a `*_release` call is a write barrier (kind 1): {kinds:?}");
        assert!(kinds.contains(&2), "an `*_acquire` call is a read barrier (kind 2): {kinds:?}");
    }

    /// Register-only inline asm (`rdtsc`, no memory clobber) lowers to the
    /// non-clobbering `<inline asm nomem>` marker; a memory-clobbering asm (`mfence`
    /// with `~{memory}`) keeps the havoc-ing `<inline asm>` marker.
    #[test]
    fn inline_asm_memory_effect_is_decided_from_constraints() {
        let src = r#"
define i32 @uses_asm(ptr %p) {
b:
  %t = call i32 asm sideeffect "rdtsc", "={ax}"()
  call void asm sideeffect "mfence", "~{memory}"()
  %u = call i32 asm "movl $1, $0", "=r,*m"(ptr %p)
  ret i32 %t
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        let names: Vec<&str> = module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.insts)
            .filter_map(|i| match i {
                csolver_ir::Inst::Call { callee: csolver_ir::Callee::Symbol(s), .. } => Some(s.as_str()),
                _ => None,
            })
            .collect();
        assert!(names.contains(&"<inline asm nomem>"), "rdtsc is register-only: {names:?}");
        assert!(names.contains(&"<inline asm>"), "mfence clobbers memory: {names:?}");
        // The `=r,*m` output-memory asm must be havoc'd (writes through %p), not nomem.
        assert_eq!(names.iter().filter(|n| **n == "<inline asm>").count(), 2, "{names:?}");
    }

    /// Register-dataflow semantic decode: a plain `mov $1, $0` copies its input to the output
    /// register (an `Assign`, not an opaque havoc call), and a `xor $0, $0` zeroes it. A template
    /// that is not a recognized pure-value idiom stays a havoc call (no `Assign` bound).
    #[test]
    fn inline_asm_register_dataflow_is_decoded() {
        use csolver_ir::{Inst, Operand, RValue};
        let lower = |src: &str| {
            LlvmFrontend
                .lower(LlvmInput { source: src.into(), name: "m".into() })
                .expect("lower")
        };
        let assigns = |m: &csolver_ir::Module| -> Vec<RValue> {
            m.functions
                .iter()
                .flat_map(|f| &f.blocks)
                .flat_map(|b| &b.insts)
                .filter_map(|i| match i {
                    Inst::Assign { value, .. } => Some(value.clone()),
                    _ => None,
                })
                .collect()
        };
        // Copy: the output is bound to a copy of the input argument.
        let copy = lower("define i32 @f(i32 %x) {\nb:\n  %y = call i32 asm \"movl $1, $0\", \"=r,r\"(i32 %x)\n  ret i32 %y\n}\n");
        assert!(
            assigns(&copy).iter().any(|v| matches!(v, RValue::Use(Operand::Reg(_)))),
            "`movl $1,$0` binds the output to a copy of its input"
        );
        // Zero idiom: the output is bound to the constant 0.
        let zero = lower("define i64 @g() {\nb:\n  %z = call i64 asm \"xor $0, $0\", \"=r\"()\n  ret i64 %z\n}\n");
        assert!(
            assigns(&zero).iter().any(|v| matches!(v,
                RValue::Use(Operand::Const(csolver_ir::Const::Int(bv))) if bv.is_zero())),
            "`xor $0,$0` binds the output to 0: {:?}", assigns(&zero)
        );
        // Unrecognized template: no semantic Assign (stays an opaque havoc call).
        let opaque = lower("define i32 @h(i32 %x) {\nb:\n  %y = call i32 asm \"frobnicate $1, $0\", \"=r,r\"(i32 %x)\n  ret i32 %y\n}\n");
        assert!(assigns(&opaque).is_empty(), "an unrecognized template is not decoded");
    }

    /// Full register-dataflow arithmetic: an in-place `add`/`sub`/… on a read-write destination is
    /// decoded to the corresponding `BinOp` over its incoming value and the source — handling both
    /// the pre-canonical `+r` form and clang's canonical matching-constraint `=r,0,r` form, and both
    /// AT&T (`src,dst`) and Intel (`dst,src`) dialects. `neg`/`not` decode to their unary identities.
    #[test]
    fn inline_asm_arithmetic_dataflow_is_decoded() {
        use csolver_ir::{BinOp, Inst, RValue};
        let binop = |src: &str| -> Option<BinOp> {
            let m = LlvmFrontend
                .lower(LlvmInput { source: src.into(), name: "m".into() })
                .expect("lower");
            m.functions
                .iter()
                .flat_map(|f| &f.blocks)
                .flat_map(|b| &b.insts)
                .find_map(|i| match i {
                    Inst::Assign { value: RValue::Bin { op, .. }, .. } => Some(*op),
                    _ => None,
                })
        };
        // `+r` form, AT&T: `addl $1, $0` → Add.
        assert_eq!(
            binop("define i32 @a(i32 %x, i32 %y) {\nb:\n  %z = call i32 asm \"addl $1, $0\", \"+r,r\"(i32 %x, i32 %y)\n  ret i32 %z\n}\n"),
            Some(BinOp::Add), "`addl` on a +r destination decodes to Add"
        );
        // Canonical matching-constraint form: `subl $2, $0`, `=r,0,r` → Sub (dst is the left operand).
        assert_eq!(
            binop("define i32 @s(i32 %x, i32 %y) {\nb:\n  %z = call i32 asm \"subl $2, $0\", \"=r,0,r\"(i32 %x, i32 %y)\n  ret i32 %z\n}\n"),
            Some(BinOp::Sub), "`subl` in the canonical =r,0,r form decodes to Sub"
        );
        // Intel dialect: `and $0, $1` (dst first) → And.
        assert_eq!(
            binop("define i32 @n(i32 %x, i32 %y) {\nb:\n  %z = call i32 asm inteldialect \"and $0, $1\", \"+r,r\"(i32 %x, i32 %y)\n  ret i32 %z\n}\n"),
            Some(BinOp::And), "Intel-dialect `and $0,$1` decodes to And"
        );
        // Unary `not $0` (`+r`) → Xor (with all-ones).
        assert_eq!(
            binop("define i32 @t(i32 %x) {\nb:\n  %z = call i32 asm \"not $0\", \"+r\"(i32 %x)\n  ret i32 %z\n}\n"),
            Some(BinOp::Xor), "`not` decodes to Xor with all-ones"
        );
        // Shift: `shll $1, $0` → Shl.
        assert_eq!(
            binop("define i32 @l(i32 %x, i32 %y) {\nb:\n  %z = call i32 asm \"shll $1, $0\", \"+r,r\"(i32 %x, i32 %y)\n  ret i32 %z\n}\n"),
            Some(BinOp::Shl), "`shll` decodes to Shl"
        );
        // Multi-statement template reducing to one real instruction (a leading nop) is decoded.
        assert_eq!(
            binop("define i32 @mm(i32 %x, i32 %y) {\nb:\n  %z = call i32 asm \"nop; addl $1, $0\", \"+r,r\"(i32 %x, i32 %y)\n  ret i32 %z\n}\n"),
            Some(BinOp::Add), "a `nop; addl` template decodes the single real instruction"
        );
        // Two real instructions cannot be tracked → stays opaque (no Bin Assign).
        assert_eq!(
            binop("define i32 @mm2(i32 %x, i32 %y) {\nb:\n  %z = call i32 asm \"addl $1, $0; addl $1, $0\", \"+r,r\"(i32 %x, i32 %y)\n  ret i32 %z\n}\n"),
            None, "a genuinely multi-instruction template stays opaque (sound)"
        );
    }

    /// An indirect call through a loaded function pointer lowers to `Callee::Indirect`
    /// (carrying the dispatch register), NOT an opaque `Symbol` — the prerequisite for
    /// devirtualization to fire on real LLVM/C code (regression: it used to become
    /// `Callee::Symbol("<indirect via %n>")`, so devirt never ran on the kernel scan).
    #[test]
    fn indirect_call_lowers_to_callee_indirect() {
        let src = r#"
define void @dispatch(ptr %ops) {
b:
  %fp = load ptr, ptr %ops, align 8
  call void %fp()
  ret void
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        let has_indirect = module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.insts)
            .any(|i| matches!(i, csolver_ir::Inst::Call { callee: csolver_ir::Callee::Indirect(_), .. }));
        assert!(has_indirect, "an indirect call must lower to Callee::Indirect, not an opaque Symbol");
    }

    /// A constant ops-struct global's function-pointer fields are extracted with
    /// correct byte offsets (padded struct layout) and resolved to defined
    /// functions, so an indirect load-then-call through them can be devirtualised.
    #[test]
    fn ops_struct_devirt_table_is_extracted_with_offsets() {
        // `{ ptr, i32, [4 x i8], ptr, ptr }`: @fa@0, @fb@16, @fc@24. @ext is an
        // undefined symbol and must be dropped from the table.
        let src = r#"
@MYOPS = constant { ptr, i32, [4 x i8], ptr, ptr } { ptr @fa, i32 42, [4 x i8] zeroinitializer, ptr @fb, ptr @fc }, align 8
@OTHER = constant { ptr } { ptr @ext }, align 8
define i32 @fa(i32 %x) {
b:
  ret i32 %x
}
define i32 @fb(i32 %x) {
b:
  ret i32 %x
}
define i32 @fc() {
b:
  ret i32 0
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        let table = module
            .global_fn_ptrs
            .get("MYOPS")
            .expect("MYOPS devirt table present");
        let by_off: std::collections::HashMap<u64, &str> = table
            .iter()
            .map(|(off, fid)| (*off, module.function(*fid).unwrap().name.as_str()))
            .collect();
        assert_eq!(by_off.get(&0).copied(), Some("fa"));
        assert_eq!(by_off.get(&16).copied(), Some("fb"));
        assert_eq!(by_off.get(&24).copied(), Some("fc"));
        assert_eq!(table.len(), 3, "no phantom fields");
        // An undefined target resolves to nothing → the global has no table.
        assert!(!module.global_fn_ptrs.contains_key("OTHER"));
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

    /// An integer parameter that merely sits next to a pointer (`fn(&mut State,
    /// skipped: u64)`) is not a slice length: it neither indexes the pointer nor
    /// appears in a comparison. Pairing it sized the pointee by an arbitrary
    /// runtime value — refuting real field accesses (false FAIL, seen on memchr's
    /// `PrefilterState::update`) and able to *prove* an OOB against the phantom
    /// size (false PASS). No contract may be emitted.
    #[test]
    fn adjacent_integer_param_is_not_a_slice_length() {
        let src = r#"
define void @update(ptr align 4 %self, i64 %skipped) {
start:
  %a = load i32, ptr %self, align 4
  %p = getelementptr inbounds i8, ptr %self, i64 4
  store i32 %a, ptr %p, align 4
  ret void
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        assert!(
            module.param_contracts.is_empty(),
            "no length evidence — no slice contract: {:?}",
            module.param_contracts
        );

        // hashbrown's shape: the integer is *compared* against a loaded field
        // but never bounds anything that indexes the pointer — a mask, not a
        // length. Comparison alone must not pair (it sized `*self` by the mask
        // and refuted a real field access). The control: the same comparison
        // against a value that *does* index the pointer is the genuine
        // bounds-checked-slice pattern and must still pair.
        let mask = r#"
define void @move_next(ptr align 8 %self, i64 %bucket_mask) {
start:
  %f = getelementptr inbounds i8, ptr %self, i64 8
  %v = load i64, ptr %f, align 8
  %c = icmp ule i64 %v, %bucket_mask
  ret void
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: mask.into(), name: "m".into() })
            .expect("lower");
        assert!(
            module.param_contracts.is_empty(),
            "a compared-but-never-indexing mask is not a length: {:?}",
            module.param_contracts
        );

        let slice = r#"
define i8 @get(ptr align 1 %s, i64 %len, i64 %i) {
start:
  %c = icmp ult i64 %i, %len
  br i1 %c, label %ok, label %out
ok:
  %p = getelementptr inbounds i8, ptr %s, i64 %i
  %v = load i8, ptr %p, align 1
  ret i8 %v
out:
  ret i8 0
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: slice.into(), name: "m".into() })
            .expect("lower");
        assert_eq!(
            module.param_contracts.len(),
            1,
            "the bounds-checked-index pattern still pairs: {:?}",
            module.param_contracts
        );
    }

    /// Named struct types (`%"core::fmt::rt::Argument<'_>" = type { … }`) must
    /// resolve — including a definition that lexically *follows* its use — and a
    /// `gep %"T", ptr, i64 N` must stride by the struct's *padded* size, not a
    /// placeholder (a wrong stride misplaces every subsequent access: verdicts,
    /// not cosmetics). `%"Outer"` = `{ ptr, %"Inner" }` with `%"Inner"` =
    /// `{ i32, i64 }` (16 B padded) → 24 bytes.
    #[test]
    fn named_struct_types_resolve_with_correct_stride() {
        let src = r#"
%"Outer" = type { ptr, %"Inner" }

define ptr @nth(ptr %base, i64 %i) {
start:
  %p = getelementptr inbounds %"Outer", ptr %base, i64 %i
  ret ptr %p
}

%"Inner" = type { i32, i64 }
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        assert!(module.unanalyzed.is_empty(), "named types must resolve: {:?}", module.unanalyzed);
        let elem = module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.insts)
            .find_map(|i| match i {
                csolver_ir::Inst::PtrOffset { elem, .. } => Some(elem.clone()),
                _ => None,
            })
            .expect("the gep lowers to a PtrOffset");
        assert_eq!(
            elem.size_bytes(&csolver_ir::DataLayout::LP64),
            Some(24),
            "gep stride must be the padded struct size"
        );
    }

    /// A multi-line `switch` case table, a float literal as a call argument, and
    /// an *indirect* call through a function pointer — each dropped whole
    /// functions before. The indirect callee lowers to `Callee::Indirect` on its
    /// dispatch register (so it can be devirtualized); an unresolved target still
    /// gets the unknown-callee havoc semantics.
    #[test]
    fn switch_table_float_args_and_indirect_calls_parse() {
        let src = r#"
define i32 @f(i64 %x, ptr %fp) {
start:
  switch i64 %x, label %d [
    i64 0, label %a
    i64 1, label %b
  ]
a:
  %r = call float @g(float 2.000000e+00, float 0x3E70000000000000)
  br label %d
b:
  %s = call i32 %fp(i64 %x)
  ret i32 %s
d:
  ret i32 0
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        assert!(module.unanalyzed.is_empty(), "must all parse: {:?}", module.unanalyzed);
        let has_indirect = module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.insts)
            .any(|i| matches!(i, csolver_ir::Inst::Call { callee: csolver_ir::Callee::Indirect(_), .. }));
        assert!(has_indirect, "the indirect call lowers to Callee::Indirect on its register");
    }

    /// `load atomic` / `store volatile` must lower as *real* accesses — an opaque
    /// placeholder would silently drop their memory obligations (an unchecked
    /// OOB store would then be a false PASS one level up). Packed structs are
    /// rejected (padded layout would oversize them — phantom in-bounds bytes).
    #[test]
    fn atomic_volatile_accesses_keep_their_obligations() {
        let src = r#"
define i32 @f(ptr %p, i32 %v) {
start:
  store atomic i32 %v, ptr %p seq_cst, align 4
  %a = load atomic i32, ptr %p acquire, align 4
  %b = load volatile i32, ptr %p, align 4
  ret i32 %b
}
"#;
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        assert!(module.unanalyzed.is_empty(), "{:?}", module.unanalyzed);
        let f = &module.functions[0];
        let loads = f.blocks.iter().flat_map(|b| &b.insts)
            .filter(|i| matches!(i, csolver_ir::Inst::Load { .. })).count();
        let stores = f.blocks.iter().flat_map(|b| &b.insts)
            .filter(|i| matches!(i, csolver_ir::Inst::Store { .. })).count();
        assert_eq!((loads, stores), (2, 1), "every qualified access stays a checked access");

        let packed = LlvmFrontend.lower(LlvmInput {
            source: "define void @g(ptr %p) {\nstart:\n  %v = load <{ i8, i32 }>, ptr %p\n  ret void\n}\n".into(),
            name: "m".into(),
        });
        let dropped = packed.map(|m| !m.unanalyzed.is_empty()).unwrap_or(true);
        assert!(dropped, "a packed struct must be rejected, not padded");
    }
}
