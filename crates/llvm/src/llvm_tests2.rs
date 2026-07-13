use super::*;

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
