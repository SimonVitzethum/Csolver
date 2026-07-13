use super::*;

#[test]
fn decodes_a_leaf_function() {
    // max: movl %esi,%eax; cmpl %esi,%edi; cmovgl %edi,%eax; retq
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
fn decodes_a_loop_with_memory_and_branches() {
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
    // The `addq (%rdi,%rcx,8), %rax` emits a load.
    assert!(f.blocks.iter().flat_map(|b| &b.insts).any(|i| matches!(i, Inst::Load { .. })));
}

#[test]
fn sub_rsp_allocates_a_stack_frame() {
    // subq $16,%rsp allocates the frame; the store/load to (%rsp) are then checked
    // against it. Assert an Alloc{Stack} is emitted and the frame teardown is a no-op.
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
    let has_frame = m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .any(|i| matches!(i, Inst::Alloc { region: RegionKind::Stack, .. }));
    assert!(has_frame, "`sub $N,%rsp` must allocate a stack frame");
}

#[test]
fn unknown_mnemonic_drops_the_function() {
    let src = "f:\n\tpushq\t%rbp\n\tretq\n";
    let m = decode_att(src);
    assert!(m.functions.is_empty());
    assert_eq!(m.unanalyzed.len(), 1);
}

#[test]
fn reg_names_alias_sub_registers() {
    assert_eq!(reg_number("rax"), Some(0));
    assert_eq!(reg_number("eax"), Some(0));
    assert_eq!(reg_number("dil"), Some(7));
    assert_eq!(reg_number("r10d"), Some(10));
    assert_eq!(reg_number("r15"), Some(15));
    assert_eq!(reg_number("xmm0"), None);
}
