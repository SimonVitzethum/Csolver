use super::*;
use crate::{detect, Architecture, Syntax};
use csolver_ir::{Callee, Inst, RegId};

// ==========================================================================
// AT&T syntax
// ==========================================================================

#[test]
fn att_decodes_a_leaf_function() {
    let src = "\
\t.text
\t.globl max
\t.type max,@function
max:
\tmovl\t%esi, %eax
\tcmpl\t%esi, %edi
\tcmovgl\t%edi, %eax
\tretq
\t.size max, .-max
";
    let m = decode_att(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    assert_eq!(m.functions.len(), 1);
    assert_eq!(m.functions[0].name, "max");
}

#[test]
fn att_loop_with_memory_and_branches() {
    let src = "\
sum:
\txorl\t%eax, %eax
\ttestq\t%rsi, %rsi
\tjle\t.LBB1_3
\txorl\t%ecx, %ecx
.LBB1_2:
\taddq\t(%rdi,%rcx,8), %rax
\tincq\t%rcx
\tcmpq\t%rcx, %rsi
\tjne\t.LBB1_2
.LBB1_3:
\tretq
";
    let m = decode_att(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let f = &m.functions[0];
    assert!(f.blocks.len() >= 3, "loop CFG has multiple blocks");
    assert!(f
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .any(|i| matches!(i, Inst::Load { .. })));
}

#[test]
fn att_sub_rsp_allocates_a_stack_frame() {
    let src = "\
f:
\tsubq\t$16, %rsp
\tmovl\t$1, (%rsp)
\tmovl\t(%rsp), %eax
\taddq\t$16, %rsp
\tretq
";
    let m = decode_att(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    assert!(has_stack_frame(&m));
}

#[test]
fn att_unknown_mnemonic_drops_the_function() {
    let m = decode_att("f:\n\tvfmadd\t%xmm0, %xmm1\n\tretq\n");
    assert!(m.functions.is_empty());
    assert_eq!(m.unanalyzed.len(), 1);
}

#[test]
fn att_prologue_push_pop_and_call() {
    // The standard `push rbp; mov rbp,rsp; sub rsp; call helper; pop rbp; ret`
    // frame decodes end-to-end (push/pop no longer drop the function). The `sub
    // rsp` frame is still a precise stack region; `call` is an opaque Inst::Call.
    let src = "\
f:
\tpushq\t%rbp
\tmovq\t%rsp, %rbp
\tsubq\t$16, %rsp
\tcall\thelper
\taddq\t$16, %rsp
\tpopq\t%rbp
\tretq
";
    let m = decode_att(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let insts: Vec<_> = m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .collect();
    assert!(
        insts.iter().any(|i| matches!(
            i,
            Inst::Alloc {
                region: RegionKind::Stack,
                ..
            }
        )),
        "sub rsp → stack frame"
    );
    assert!(insts
        .iter()
        .any(|i| matches!(i, Inst::Call { callee: Callee::Symbol(s), .. } if s == "helper")));
}

#[test]
fn frame_pointer_idiom_builds_one_open_frame() {
    // `push rbp; mov rbp, rsp; sub rsp, 16` → a single frame region with a
    // symbolic (open-above) size bound into rsp (reg 4), and rbp (reg 5) bound to
    // rsp + 16 (the top of the local area).
    let src = "f:\n\tpushq\t%rbp\n\tmovq\t%rsp, %rbp\n\tsubq\t$16, %rsp\n\tretq\n";
    let m = decode_att(src);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts: Vec<_> = m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .collect();
    // The frame Alloc's count is a register (symbolic), not a constant — this is
    // what marks the region `assumed` (open above) in the executor.
    assert!(
        insts.iter().any(|i| matches!(
            i,
            Inst::Alloc { dst, region: RegionKind::Stack, count: Operand::Reg(_), .. } if *dst == RegId(4)
        )),
        "frame region: symbolic-size stack Alloc into rsp"
    );
    // rbp (reg 5) = rsp + 16 (a PtrOffset placing rbp at the top of the locals).
    assert!(
        insts.iter().any(|i| matches!(
            i,
            Inst::PtrOffset { dst, base: Operand::Reg(b), .. } if *dst == RegId(5) && *b == RegId(4)
        )),
        "rbp bound to rsp + N"
    );
}

#[test]
fn att_indirect_call() {
    let m = decode_att("f:\n\tcall\t*%rax\n\tretq\n");
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    assert!(m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .any(|i| matches!(
            i,
            Inst::Call {
                callee: Callee::Indirect(_),
                ..
            }
        )));
}

// ==========================================================================
// Intel syntax
// ==========================================================================

#[test]
fn intel_decodes_a_leaf_function() {
    // The Intel-syntax counterpart of `att_decodes_a_leaf_function` (dst, src order).
    let src = "\
\t.intel_syntax noprefix
\t.globl max
max:
\tmov\teax, esi
\tcmp\tedi, esi
\tcmovg\teax, edi
\tret
";
    let m = decode_intel(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    assert_eq!(m.functions[0].name, "max");
}

#[test]
fn intel_memory_load_store_and_frame() {
    // sub rsp, 16 ; mov dword ptr [rsp], 1 ; mov eax, dword ptr [rsp] ; add rsp,16 ; ret
    let src = "\
f:
\tsub\trsp, 16
\tmov\tdword ptr [rsp], 1
\tmov\teax, dword ptr [rsp]
\tadd\trsp, 16
\tret
";
    let m = decode_intel(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    assert!(has_stack_frame(&m));
    let insts: Vec<_> = m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .collect();
    assert!(
        insts.iter().any(|i| matches!(i, Inst::Store { .. })),
        "store to [rsp]"
    );
    assert!(
        insts.iter().any(|i| matches!(i, Inst::Load { .. })),
        "load from [rsp]"
    );
}

#[test]
fn intel_indexed_load_in_a_loop() {
    // add rax, qword ptr [rdi + rcx*8]  — a scaled-index pointer access.
    let src = "\
sum:
\txor\teax, eax
\ttest\trsi, rsi
\tjle\t.LBB0_2
\txor\tecx, ecx
.LBB0_1:
\tadd\trax, qword ptr [rdi + rcx*8]
\tinc\trcx
\tcmp\trcx, rsi
\tjne\t.LBB0_1
.LBB0_2:
\tret
";
    let m = decode_intel(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let f = &m.functions[0];
    assert!(f.blocks.len() >= 3);
    // The indexed access lowers to a PtrOffset (index*scale) then a Load.
    let insts: Vec<_> = f.blocks.iter().flat_map(|b| &b.insts).collect();
    assert!(insts.iter().any(|i| matches!(i, Inst::PtrOffset { .. })));
    assert!(insts.iter().any(|i| matches!(i, Inst::Load { .. })));
}

#[test]
fn intel_rip_relative_is_a_symbol_pointer() {
    // lea rax, [rip + gvar] — a global-symbol pointer.
    let src = "f:\n\tlea\trax, [rip + gvar]\n\tmov\tecx, dword ptr [rax]\n\tret\n";
    let m = decode_intel(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let has_sym = m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .any(|i| matches!(i, Inst::Assign { value: RValue::Use(Operand::Const(Const::Symbol(s))), .. } if s == "gvar"));
    assert!(has_sym, "RIP-relative access resolves to the @gvar symbol");
}

#[test]
fn intel_negative_displacement() {
    // mov dword ptr [rbp - 4], edi — a frame-local store at a negative offset.
    let src = "f:\n\tmov\tdword ptr [rbp - 4], edi\n\tret\n";
    let m = decode_intel(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    assert!(m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .any(|i| matches!(i, Inst::Store { .. })));
}

#[test]
fn intel_prologue_push_call_pop() {
    let src = "\
.intel_syntax noprefix
f:
\tpush\trbp
\tmov\trbp, rsp
\tsub\trsp, 16
\tcall\thelper
\tadd\trsp, 16
\tpop\trbp
\tret
";
    let m = decode_intel(src);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let insts: Vec<_> = m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .collect();
    assert!(
        insts.iter().any(|i| matches!(
            i,
            Inst::Alloc {
                region: RegionKind::Stack,
                ..
            }
        )),
        "sub rsp → stack frame"
    );
    assert!(insts
        .iter()
        .any(|i| matches!(i, Inst::Call { callee: Callee::Symbol(s), .. } if s == "helper")));
}

// ==========================================================================
// Auto-detection
// ==========================================================================

#[test]
fn detect_distinguishes_syntaxes_and_arch() {
    assert_eq!(
        detect("f:\n\tmovq\t%rax, %rbx\n\tretq\n"),
        (Architecture::X86_64, Syntax::Att)
    );
    assert_eq!(
        detect(".intel_syntax noprefix\nf:\n\tmov\trax, rbx\n\tret\n"),
        (Architecture::X86_64, Syntax::Intel)
    );
    assert_eq!(
        detect("f:\n\tmov\trax, qword ptr [rbx]\n\tret\n").1,
        Syntax::Intel
    );
    assert_eq!(
        detect("f:\n\tldp\tx29, x30, [sp]\n\tret\n").0,
        Architecture::AArch64
    );
}

// ==========================================================================
// helpers
// ==========================================================================

fn has_stack_frame(m: &Module) -> bool {
    m.functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| &b.insts)
        .any(|i| {
            matches!(
                i,
                Inst::Alloc {
                    region: RegionKind::Stack,
                    ..
                }
            )
        })
}

#[test]
fn reg_names_alias_sub_registers() {
    assert_eq!(reg_number("rax"), Some(0));
    assert_eq!(reg_number("eax"), Some(0));
    assert_eq!(reg_number("dil"), Some(7));
    assert_eq!(reg_number("r10d"), Some(10));
    assert_eq!(reg_number("r15"), Some(15));
    assert_eq!(reg_number("xmm0"), None);
    assert_eq!(reg_width("rax"), 64);
    assert_eq!(reg_width("eax"), 32);
    assert_eq!(reg_width("r8d"), 32);
    assert_eq!(reg_width("al"), 8);
}
