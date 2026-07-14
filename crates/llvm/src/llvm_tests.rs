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
            Inst::Barrier { kind, .. } => Some(*kind),
            _ => None,
        })
        .collect();
    assert!(kinds.contains(&1), "a `*_release` call is a write barrier (kind 1): {kinds:?}");
    assert!(kinds.contains(&2), "an `*_acquire` call is a read barrier (kind 2): {kinds:?}");
}

#[test]
fn inlined_atomic_ordering_lowers_to_barriers() {
    use csolver_ir::Inst;
    // The INLINED message-passing idiom: `store atomic release` (producer publish) and
    // `load atomic acquire` (consumer). The ordering keyword used to be discarded; now
    // each emits the fence it guarantees (release → write barrier BEFORE the store,
    // acquire → read barrier AFTER the load, seq_cst → full), so the weak-memory pass
    // sees the ordering instead of falsely flagging a missing barrier.
    let src = "\
        define void @f(ptr %p, ptr %q) {\nb:\n\
          store atomic i32 1, ptr %p release, align 4\n\
          %v = load atomic i32, ptr %q acquire, align 4\n\
          store atomic i32 2, ptr %p seq_cst, align 4\n  ret void\n}\n";
    let m = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("lower");
    let seq: Vec<&Inst> = m
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.insts)
        .collect();
    let kinds: Vec<u8> = seq.iter().filter_map(|i| match i {
        Inst::Barrier { kind, .. } => Some(*kind),
        _ => None,
    }).collect();
    assert!(kinds.contains(&1), "release store → write barrier (kind 1): {kinds:?}");
    assert!(kinds.contains(&2), "acquire load → read barrier (kind 2): {kinds:?}");
    assert!(kinds.contains(&0), "seq_cst store → full barrier (kind 0): {kinds:?}");
    // A release write barrier precedes its store; an acquire read barrier follows its load.
    let bpos = seq.iter().position(|i| matches!(i, Inst::Barrier { kind: 1, .. })).unwrap();
    let spos = seq.iter().position(|i| matches!(i, Inst::Store { .. })).unwrap();
    assert!(bpos < spos, "write barrier is emitted before the release store");
}

/// `rcu_assign_pointer` is an `smp_store_release` publish: it lowers to a **write barrier**
/// (kind 1) so the producer's prior data stores are ordered before the pointer is published
/// (the message-passing producer side) — the weak-memory pass then does not demand an `smp_wmb`.
#[test]
fn rcu_assign_pointer_lowers_to_a_write_barrier() {
    use csolver_ir::Inst;
    let src = "\
        declare void @rcu_assign_pointer(ptr, ptr)\n\
        define void @publish(ptr %gp, ptr %obj) {\nb:\n\
          call void @rcu_assign_pointer(ptr %gp, ptr %obj)\n  ret void\n}\n";
    let m = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("lower");
    let has_wbarrier = m
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.insts)
        .any(|i| matches!(i, Inst::Barrier { kind: 1, .. }));
    assert!(has_wbarrier, "rcu_assign_pointer publishes with release (write-barrier) ordering");
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

#[test]
fn const_expr_bitcast_fn_pointer_is_recovered_for_devirt() {
    // A constant ops-struct holding a function pointer wrapped in a `bitcast` const-expr
    // (a common vtable/ops-table shape) must keep the `@handler` symbol so an indirect
    // call loaded from it can devirtualise — not be dropped as an opaque constant.
    let src = "\
        @ops = constant { ptr } { ptr bitcast (ptr @handler to ptr) }\n\
        define void @handler() {\nb:\n  ret void\n}\n";
    let m = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("lower");
    // The module's global function-pointer table records @handler at the field offset.
    let has = m.global_fn_ptrs.values().any(|fields| fields.iter().any(|(_, fid)| {
        m.functions.iter().any(|f| f.id == *fid && f.name == "handler")
    }));
    assert!(has, "the bitcast-wrapped @handler is recovered as a fn-ptr field: {:?}", m.global_fn_ptrs);
}

