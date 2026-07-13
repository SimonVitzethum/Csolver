use super::*;

const SRC: &str = r#"
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

#[test]
fn parses_the_sample() {
    let m = parse_module(SRC).expect("parse");
    assert_eq!(m.funcs.len(), 1);
    let f = &m.funcs[0];
    assert_eq!(f.name, "make_and_store");
    assert_eq!(f.params.len(), 1);
    assert_eq!(f.params[0].ty, LType::Int(64));
    assert_eq!(f.params[0].name, "i");
    assert_eq!(f.blocks.len(), 4);
    assert_eq!(f.blocks[0].label, "entry");
    // entry: alloca + icmp, then a conditional branch.
    assert_eq!(f.blocks[0].insts.len(), 2);
    assert!(matches!(f.blocks[0].term, LTerm::CondBr(..)));
    // body: gep + store.
    let body = f.blocks.iter().find(|b| b.label == "body").unwrap();
    assert!(matches!(body.insts[0], LInst::Gep { .. }));
    assert!(matches!(body.insts[1], LInst::Store { .. }));
}

#[test]
fn scans_single_integer_metadata_nodes() {
    let m = scan_meta_ints("!126 = !{i64 8}\n!7 = !{i32 4}\n!9 = !{}\n!5 = !{!1, !2}\n");
    assert_eq!(m.get(&126), Some(&8));
    assert_eq!(m.get(&7), Some(&4));
    // An empty tuple and a multi-element tuple are not single integers.
    assert_eq!(m.get(&9), None);
    assert_eq!(m.get(&5), None);
}

#[test]
fn parses_variadic_function() {
    // `...` is the trailing variadic marker; the fixed params are kept and the
    // function is analyzed rather than dropped whole.
    let src = "define i64 @sum(i32 %0, ...) {\nentry:\n  ret i64 0\n}\n";
    let m = parse_module(src).expect("parse");
    assert_eq!(m.unanalyzed.len(), 0, "variadic fn must not be dropped");
    assert_eq!(
        m.funcs[0].params.len(),
        1,
        "only the fixed i32 param is kept"
    );
}

#[test]
fn numbers_unlabeled_entry_block_as_phi_predecessor() {
    // The entry block is unlabeled; its implicit LLVM number is the parameter
    // count (2 here → `%2`), and a later phi names it as a predecessor. It must
    // resolve — otherwise the whole function is dropped.
    let src = r#"
define i64 @f(ptr %0, i32 %1) {
  %3 = icmp sgt i32 %1, 0
  br i1 %3, label %4, label %5
4:
  br label %5
5:
  %6 = phi i64 [ 0, %2 ], [ 7, %4 ]
  ret i64 %6
}
"#;
    let m = parse_module(src).expect("parse");
    assert_eq!(
        m.unanalyzed.len(),
        0,
        "entry-referencing phi must not drop the fn"
    );
    // The entry block is labeled with its implicit number "2".
    assert_eq!(m.funcs[0].blocks[0].label, "2");
}

#[test]
fn parses_variadic_call_with_explicit_function_type() {
    // A variadic call prints the full function type before the callee:
    // `call i64 (i32, ...) @f(...)`. The caller must not be dropped (which
    // would erase the call sites every contract synthesis depends on).
    let src = r#"
define i64 @caller() {
entry:
  %r = call i64 (i32, ...) @printf_like(i32 0, i64 1, i64 2)
  ret i64 %r
}
"#;
    let m = parse_module(src).expect("parse");
    assert_eq!(
        m.unanalyzed.len(),
        0,
        "variadic call must not drop the caller"
    );
    // The call parsed with its fixed + variadic arguments and callee.
    let call = m.funcs[0].blocks[0].insts.iter().find_map(|i| match i {
        LInst::Call { callee, args, .. } => Some((callee.clone(), args.len())),
        _ => None,
    });
    assert_eq!(call, Some(("printf_like".to_string(), 3)));
}

#[test]
fn captures_load_align_metadata() {
    let src = r#"
define i64 @f(ptr %p) {
entry:
  %v = load ptr, ptr %p, align 8, !nonnull !0, !align !1
  %w = load i64, ptr %p, align 8
  ret i64 %w
}
!0 = !{}
!1 = !{i64 16}
"#;
    let m = parse_module(src).expect("parse");
    let f = &m.funcs[0];
    // The pointer load records its `!align 16` guarantee; the plain load does not.
    let mut loads = f.blocks[0].insts.iter().filter_map(|i| match i {
        LInst::Load { align_meta, .. } => Some(*align_meta),
        _ => None,
    });
    assert_eq!(loads.next(), Some(Some(16)));
    assert_eq!(loads.next(), Some(None));
}
