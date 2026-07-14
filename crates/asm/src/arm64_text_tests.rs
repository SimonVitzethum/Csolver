use super::*;
use csolver_ir::Inst;

fn insts_of(m: &Module) -> Vec<&Inst> {
    m.functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| &b.insts)
        .collect()
}

#[test]
fn decodes_a_leaf_with_frame_and_memory() {
    // A typical clang prologue/body/epilogue.
    let src = "\
\t.globl f
f:
\tsub\tsp, sp, #16
\tstr\tw0, [sp, #12]
\tldr\tw8, [sp, #12]
\tadd\tsp, sp, #16
\tret
";
    let m = decode(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let insts = insts_of(&m);
    assert!(insts.iter().any(|i| matches!(
        i,
        Inst::Alloc {
            region: RegionKind::Stack,
            ..
        }
    )));
    assert!(insts.iter().any(|i| matches!(i, Inst::Store { .. })));
    assert!(insts.iter().any(|i| matches!(i, Inst::Load { .. })));
}

#[test]
fn conditional_branch_builds_a_cfg() {
    // cmp w0,#0 ; b.eq .L ; ... ; .L: ret
    let src = "\
f:
\tcmp\tw0, #0
\tb.eq\t.LBB0_2
\tmov\tw1, #1
.LBB0_2:
\tret
";
    let m = decode(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let f = &m.functions[0];
    assert!(f.blocks.len() >= 2);
    assert!(matches!(
        f.blocks[0].term,
        csolver_ir::Terminator::CondBr { .. }
    ));
}

#[test]
fn cbz_builds_a_conditional_branch() {
    let src = "f:\n\tcbz\tx0, .L\n\tmov\tx1, #7\n.L:\n\tret\n";
    let m = decode(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    assert!(matches!(
        m.functions[0].blocks[0].term,
        csolver_ir::Terminator::CondBr { .. }
    ));
}

#[test]
fn ldp_stp_pair_two_accesses() {
    // stp/ldp x29,x30,[sp,#16] — the standard frame-record save/restore.
    let src = "\
f:
\tsub\tsp, sp, #32
\tstp\tx29, x30, [sp, #16]
\tldp\tx29, x30, [sp, #16]
\tadd\tsp, sp, #32
\tret
";
    let m = decode(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let insts = insts_of(&m);
    assert!(
        insts
            .iter()
            .filter(|i| matches!(i, Inst::Store { .. }))
            .count()
            >= 2,
        "stp = two stores"
    );
    assert!(
        insts
            .iter()
            .filter(|i| matches!(i, Inst::Load { .. }))
            .count()
            >= 2,
        "ldp = two loads"
    );
}

#[test]
fn adrp_add_materializes_a_global_pointer() {
    // adrp x0, gvar ; add x0, x0, :lo12:gvar ; ldr w1, [x0] — a global load.
    let src = "\
f:
\tadrp\tx0, gvar
\tadd\tx0, x0, :lo12:gvar
\tldr\tw1, [x0]
\tret
";
    let m = decode(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let has_sym = insts_of(&m).iter().any(
        |i| matches!(i, Inst::Assign { value: RValue::Use(Operand::Const(Const::Symbol(s))), .. } if s == "gvar"),
    );
    assert!(has_sym, "adrp resolves to the @gvar symbol pointer");
}

#[test]
fn indexed_load_with_lsl_scale() {
    // ldr x1, [x0, x2, lsl #3] — a scaled-index (8-byte) pointer access.
    let src = "f:\n\tldr\tx1, [x0, x2, lsl #3]\n\tret\n";
    let m = decode(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    assert!(insts_of(&m)
        .iter()
        .any(|i| matches!(i, Inst::PtrOffset { .. })));
    assert!(insts_of(&m).iter().any(|i| matches!(i, Inst::Load { .. })));
}

#[test]
fn bl_is_an_opaque_call_and_analysis_continues() {
    // `bl helper` returns and falls through — an Inst::Call binding x0, not a stop.
    let src = "f:\n\tmov\tx0, #1\n\tbl\thelper\n\tadd\tx0, x0, #2\n\tret\n";
    let m = decode(src);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts = insts_of(&m);
    assert!(insts.iter().any(
        |i| matches!(i, Inst::Call { callee: csolver_ir::Callee::Symbol(s), .. } if s == "helper")
    ));
    // The post-call `add` is still lowered (analysis did not stop at the call).
    assert!(
        insts
            .iter()
            .filter(|i| matches!(i, Inst::Assign { .. }))
            .count()
            >= 2
    );
}

#[test]
fn unknown_mnemonic_drops_the_function() {
    let m = decode("f:\n\tfmov\td0, x1\n\tret\n");
    assert!(m.functions.is_empty());
    assert_eq!(m.unanalyzed.len(), 1);
}
