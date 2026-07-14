use super::*;
use csolver_ir::Terminator;

#[test]
fn decodes_xor_eax_eax_ret() {
    // 31 c0  xor eax, eax ; c3  ret
    let m = decode_function("f", &[0x31, 0xc0, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "fully decoded");
    let f = &m.functions[0];
    assert_eq!(f.blocks[0].insts.len(), 1); // the xor -> assign 0
    matches!(f.blocks[0].term, Terminator::Return(_));
}

#[test]
fn unsupported_opcode_marks_unanalyzed() {
    // 0x0f is a two-byte-opcode escape we do not decode.
    let m = decode_function("f", &[0x0f, 0x05]);
    assert!(m.functions.is_empty());
    assert_eq!(m.unanalyzed.len(), 1);
}

#[test]
fn decodes_endbr_nop_cmov_and_alu_mem() {
    // f3 0f 1e fa  endbr64
    // 0f 1f 00     nop dword [rax]        (multi-byte nop)
    // 0f 4f c7     cmovg eax, edi         (reg-reg cmov -> dst becomes unknown)
    // 48 03 07     add rax, [rdi]         (alu r, r/m memory)
    // 03 c1        add eax, ecx           (alu r, r/m reg)
    // c3           ret
    let code = [
        0xf3, 0x0f, 0x1e, 0xfa, 0x0f, 0x1f, 0x00, 0x0f, 0x4f, 0xc7, 0x48, 0x03, 0x07, 0x03, 0xc1,
        0xc3,
    ];
    let m = decode_function("f", &code);
    assert!(
        m.unanalyzed.is_empty(),
        "must fully decode: {:?}",
        m.unanalyzed
    );
    assert_eq!(m.functions.len(), 1);
    // The `add rax, [rdi]` emits a Load (a memory obligation the analysis sees).
    let has_load = m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .any(|i| matches!(i, Inst::Load { .. }));
    assert!(has_load, "the memory-operand ALU form must emit a load");
}

#[test]
fn rip_relative_resolves_to_a_global_symbol() {
    // 8b 05 00000000  mov eax, [rip+disp32] ; c3 ret. The resolver maps the disp32
    // at function offset 2 to the global `g`, so the access uses `@g` as its base.
    let code = [0x8b, 0x05, 0x00, 0x00, 0x00, 0x00, 0xc3];
    let m = decode_function_reloc("f", &code, &|pos| (pos == 2).then(|| ("g".to_string(), 0)), &|_| None);
    assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
    let has_sym = m.functions[0].blocks.iter().flat_map(|b| &b.insts).any(|i| {
        matches!(i, Inst::Assign { value: RValue::Use(Operand::Const(csolver_ir::Const::Symbol(s))), .. } if s == "g")
    });
    assert!(
        has_sym,
        "a resolved RIP-relative access must materialize the global symbol"
    );
}

#[test]
fn rip_relative_unresolved_still_decodes() {
    // Without a relocation the RIP-relative access becomes an opaque sentinel — the
    // function must still decode (previously it dropped whole).
    let code = [0x8b, 0x05, 0x00, 0x00, 0x00, 0x00, 0xc3];
    let m = decode_function("f", &code);
    assert!(
        m.unanalyzed.is_empty(),
        "unresolved RIP-relative must decode, not drop: {:?}",
        m.unanalyzed
    );
}

/// endbr64 opens almost every CET-built kernel function; without it the whole
/// function dropped at byte 0.
#[test]
fn endbr_at_entry_does_not_drop_the_function() {
    let m = decode_function("f", &[0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xc0, 0xc3]);
    assert!(
        m.unanalyzed.is_empty(),
        "endbr64 entry must not drop: {:?}",
        m.unanalyzed
    );
}

#[test]
fn decodes_a_store_through_a_register() {
    // 48 89 37  mov [rdi], rsi  ; c3 ret   (REX.W, ModRM 0x37 = mod 00 reg rsi rm rdi)
    let m = decode_function("f", &[0x48, 0x89, 0x37, 0xc3]);
    assert!(m.unanalyzed.is_empty());
    let insts = &m.functions[0].blocks[0].insts;
    // `[rdi]` lowers to a PtrOffset (rdi + 0) followed by a Store.
    assert!(matches!(insts[0], Inst::PtrOffset { .. }));
    assert!(matches!(insts[1], Inst::Store { .. }));
}

#[test]
fn decodes_alu_read_modify_write_on_memory() {
    // 01 07  add [rdi], eax  ; c3 ret   (ModRM 0x07 = mod 00 reg eax rm rdi)
    // Previously declined ("ALU with a memory operand"); now a load-modify-store so the
    // memory access carries its in-bounds/permission obligations.
    let m = decode_function("f", &[0x01, 0x07, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "fully decoded: {:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    assert!(matches!(insts[0], Inst::PtrOffset { .. }), "address of [rdi]");
    assert!(matches!(insts[1], Inst::Load { .. }), "read-modify-write reads first");
    assert!(matches!(insts[2], Inst::Assign { .. }), "combine with the register");
    assert!(matches!(insts[3], Inst::Store { .. }), "and writes the result back");
}

#[test]
fn decodes_memory_operand_forms_that_were_previously_declined() {
    // Each of these reads (and some write) memory; previously the whole instruction was
    // declined, so the access went unmodelled. Now the load/store carries its obligations.
    let has = |code: &[u8], want: &dyn Fn(&Inst) -> bool| {
        let m = decode_function("f", &[code, &[0xc3]].concat());
        assert!(m.unanalyzed.is_empty(), "decoded {code:?}: {:?}", m.unanalyzed);
        assert!(m.functions[0].blocks[0].insts.iter().any(want), "expected inst in {code:?}");
    };
    // cmp [rdi], eax (39 07) — a load feeding the flags.
    has(&[0x39, 0x07], &|i| matches!(i, Inst::Load { .. }));
    // add [rdi], 5 (83 07 05) — a read-modify-write (load + store).
    has(&[0x83, 0x07, 0x05], &|i| matches!(i, Inst::Store { .. }));
    // inc dword [rdi] (ff 07) — a read-modify-write.
    has(&[0xff, 0x07], &|i| matches!(i, Inst::Store { .. }));
    // xchg [rdi], eax (87 07) — an atomic swap: barrier + load + store.
    has(&[0x87, 0x07], &|i| matches!(i, Inst::Barrier { .. }));
    has(&[0x87, 0x07], &|i| matches!(i, Inst::Store { .. }));
    // cmovne eax, [rdi] (0f 45 07) — the source load is checked.
    has(&[0x0f, 0x45, 0x07], &|i| matches!(i, Inst::Load { .. }));
}

#[test]
fn decodes_a_stack_frame_and_its_access() {
    // 48 83 ec 10        sub rsp, 16        (allocate a 16-byte frame)
    // 89 44 24 08        mov [rsp+8], eax   (store within the frame)
    // 48 83 c4 10        add rsp, 16
    // c3                 ret
    let code = [
        0x48, 0x83, 0xec, 0x10, 0x89, 0x44, 0x24, 0x08, 0x48, 0x83, 0xc4, 0x10, 0xc3,
    ];
    let m = decode_function("f", &code);
    assert!(m.unanalyzed.is_empty(), "fully decoded: {:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    // sub rsp,16 -> Alloc Stack; [rsp+8] -> PtrOffset + Store; add rsp -> noop.
    assert!(matches!(
        insts[0],
        Inst::Alloc {
            region: RegionKind::Stack,
            ..
        }
    ));
    assert!(matches!(insts[1], Inst::PtrOffset { .. }));
    assert!(matches!(insts[2], Inst::Store { .. }));
}

#[test]
fn reconstructs_a_conditional_branch() {
    // sub rsp,16 ; cmp edi,0 ; jne +4 ; mov [rsp+8],eax ; add rsp,16 ; ret
    let code = [
        0x48, 0x83, 0xec, 0x10, 0x83, 0xff, 0x00, 0x75, 0x04, 0x89, 0x44, 0x24, 0x08, 0x48, 0x83,
        0xc4, 0x10, 0xc3,
    ];
    let m = decode_function("f", &code);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let f = &m.functions[0];
    assert_eq!(f.blocks.len(), 3, "entry + store + join");
    assert!(
        matches!(f.blocks[0].term, Terminator::CondBr { .. }),
        "entry branches"
    );
}

#[test]
fn reconstructs_a_loop_back_edge() {
    // xor eax,eax ; .loop: add eax,1 ; cmp eax,4 ; jne .loop ; ret
    let code = [
        0x31, 0xc0, // xor eax, eax
        0x83, 0xc0, 0x01, // add eax, 1   (.loop)
        0x83, 0xf8, 0x04, // cmp eax, 4
        0x75, 0xf8, // jne -8 (.loop)
        0xc3, // ret
    ];
    let m = decode_function("f", &code);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let f = &m.functions[0];
    // The loop body block branches back to itself (a back-edge).
    let loop_body = &f.blocks[1];
    assert!(matches!(
        loop_body.term,
        Terminator::CondBr { then_blk, .. } if then_blk == loop_body.id
    ));
}

#[test]
fn decodes_indexed_addressing_and_lea() {
    // mov [rsp + rcx*4], eax  = 89 04 8c   (SIB scale 4, index rcx, base rsp)
    let m = decode_function("f", &[0x89, 0x04, 0x8c, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    assert!(
        matches!(insts[0], Inst::PtrOffset { .. }),
        "index*scale offset"
    );
    assert!(matches!(insts[1], Inst::Store { .. }));

    // lea rax, [rsp + rcx*4]  = 48 8d 04 8c   (compute address, no access)
    let m2 = decode_function("g", &[0x48, 0x8d, 0x04, 0x8c, 0xc3]);
    assert!(m2.unanalyzed.is_empty(), "{:?}", m2.unanalyzed);
    let insts = &m2.functions[0].blocks[0].insts;
    assert!(
        matches!(insts.last(), Some(Inst::Assign { .. })),
        "lea assigns the address"
    );
}

#[test]
fn decodes_movsxd_reg_reg() {
    // 48 63 d8  movsxd rbx, eax  (REX.W movsxd)
    let m = decode_function("f", &[0x48, 0x63, 0xd8, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_push_pop() {
    // 50  push rax ; 58  pop rbx ; c3  ret  (no REX.W → 32-bit ops)
    let m = decode_function("f", &[0x50, 0x58, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    // push rax: Alloc + Store
    assert!(matches!(insts[0], Inst::Alloc { .. }));
    assert!(matches!(insts[1], Inst::Store { .. }));
    // pop rbx: Load
    assert!(matches!(insts[2], Inst::Load { .. }));
}

#[test]
fn decodes_push_imm32() {
    // 68 78 56 34 12  push 0x12345678 ; c3  ret
    let m = decode_function("f", &[0x68, 0x78, 0x56, 0x34, 0x12, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_mov_rm_imm32() {
    // c7 c0 2a 00 00 00  mov eax, 42 ; c3 ret   (ModRM 0xc0 = mod 11 reg 000 rm 000)
    let m = decode_function("f", &[0xc7, 0xc0, 0x2a, 0x00, 0x00, 0x00, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    assert!(matches!(insts[0], Inst::Assign { .. }));
}

#[test]
fn decodes_xchg_rax_reg() {
    // 48 91  xchg rax, rcx  (REX.W + xchg rax,rcx)
    let m = decode_function("f", &[0x48, 0x91, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    assert_eq!(insts.len(), 3, "xchg needs temp");
}

#[test]
fn decodes_cdqe() {
    // 48 98  cdqe ; c3 ret
    let m = decode_function("f", &[0x48, 0x98, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_cqo() {
    // 48 99  cqo ; c3 ret
    let m = decode_function("f", &[0x48, 0x99, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_shift_imm8() {
    // 48 c1 e0 03  shl rax, 3  (REX.W, ModRM 0xe0 = mod 11 reg 100 rm 000)
    let m = decode_function("f", &[0x48, 0xc1, 0xe0, 0x03, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    assert!(matches!(insts[0], Inst::Assign { .. }));
}

#[test]
fn decodes_setcc() {
    // 0f 94 c0  sete al ; c3 ret   (sete sets byte to 0/1 based on ZF)
    let m = decode_function("f", &[0x0f, 0x94, 0xc0, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_movzx_byte() {
    // 0f b6 c3  movzx eax, bl ; c3 ret
    let m = decode_function("f", &[0x0f, 0xb6, 0xc3, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_movsx_word() {
    // 0f bf c3  movsx eax, bx ; c3 ret
    let m = decode_function("f", &[0x0f, 0xbf, 0xc3, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_mov_rm8_imm8() {
    // c6 c0 2a  mov al, 42 ; c3 ret
    let m = decode_function("f", &[0xc6, 0xc0, 0x2a, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    assert!(matches!(insts[0], Inst::Assign { .. }));
}

#[test]
fn decodes_inc_reg() {
    // 48 ff c0  inc rax  (REX.W, Group 5 /0)
    let m = decode_function("f", &[0x48, 0xff, 0xc0, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    assert!(matches!(insts[0], Inst::Assign { .. }));
}

#[test]
fn decodes_dec_reg() {
    // 48 ff c8  dec rax  (REX.W, Group 5 /1)
    let m = decode_function("f", &[0x48, 0xff, 0xc8, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_push_reg_rexw() {
    // 50  push rax  (already 64-bit without REX)
    // 41 57  push r15  (REX.B + 0x57)
    let m = decode_function("f", &[0x50, 0x41, 0x57, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

#[test]
fn decodes_neg_not_via_group3() {
    // f6 d8  neg al   (Group 3 /3, r/m8)
    let m = decode_function("f", &[0xf6, 0xd8, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
}

// ========================================================================
// Typed instruction decoder tests (decode_instruction)
// ========================================================================

#[test]
fn typed_nop() {
    let d = decode_instruction(&[0x90], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Nop);
    assert_eq!(d.length, 1);
}

#[test]
fn typed_ret() {
    let d = decode_instruction(&[0xc3], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Ret);
    assert_eq!(d.length, 1);
}

#[test]
fn typed_mov_eax_imm() {
    // mov eax, 0x12345678
    let d = decode_instruction(&[0xb8, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Imm(0x12345678)
        )
    );
    assert!(!d.prefixes.rex);
    assert_eq!(d.length, 5);
}

#[test]
fn typed_mov_rax_imm64() {
    // mov rax, 0x123456789abcdef0  (REX.W)
    let d = decode_instruction(
        &[0x48, 0xb8, 0xf0, 0xde, 0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12],
        0,
    )
    .unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RAX, Width::Q),
            X86Operand::Imm(0x123456789abcdef0),
        )
    );
    assert!(d.prefixes.rex);
    assert!(d.prefixes.rex_w);
    assert_eq!(d.length, 10);
}

#[test]
fn typed_mov_rdi_imm() {
    // mov edi, 0x7f (0xbf + imm32)
    let d = decode_instruction(&[0xbf, 0x7f, 0x00, 0x00, 0x00], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(X86Operand::Reg(Reg::RDI, Width::D), X86Operand::Imm(0x7f))
    );
}

#[test]
fn typed_xor_eax_eax() {
    // xor eax, eax  = 31 c0  (reg form, encodes to Mov(rax, 0))
    let d = decode_instruction(&[0x31, 0xc0], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0))
    );
    assert_eq!(d.length, 2);
}

#[test]
fn typed_xor_rax_rax() {
    // xor rax, rax = 48 31 c0  (REX.W)
    let d = decode_instruction(&[0x48, 0x31, 0xc0], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(X86Operand::Reg(Reg::RAX, Width::Q), X86Operand::Imm(0))
    );
    assert!(d.prefixes.rex_w);
}

#[test]
fn typed_add_reg_reg() {
    // add eax, ecx = 01 c8
    let d = decode_instruction(&[0x01, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Add(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RCX, Width::D),
        )
    );
}

#[test]
fn typed_sub_reg_reg() {
    // sub eax, edx = 29 d0
    let d = decode_instruction(&[0x29, 0xd0], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Sub(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RDX, Width::D),
        )
    );
}

#[test]
fn typed_and_reg_reg() {
    // and eax, ecx = 21 c8
    let d = decode_instruction(&[0x21, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::And(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RCX, Width::D),
        )
    );
}

#[test]
fn typed_or_reg_reg() {
    // or eax, ecx = 09 c8
    let d = decode_instruction(&[0x09, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Or(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RCX, Width::D),
        )
    );
}

#[test]
fn typed_mov_reg_reg() {
    // mov eax, ecx = 89 c8  (r/m, r  → reg form since mod=11)
    let d = decode_instruction(&[0x89, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RCX, Width::D),
        )
    );
}

#[test]
fn typed_mov_reg_from_reg() {
    // mov eax, ecx = 8b c8  (r, r/m  → reg form)
    let d = decode_instruction(&[0x8b, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RCX, Width::D),
            X86Operand::Reg(Reg::RAX, Width::D),
        )
    );
}

#[test]
fn typed_mov_reg_mem() {
    // mov eax, [rdi] = 8b 07  (ModRM 0x07: mod=00, reg=000, rm=111)
    // Wait: 0x07 = 00 000 111 → mode=0, reg=0 (eax), rm=7 (rdi)
    let d = decode_instruction(&[0x8b, 0x07], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RDI),
        index: None,
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Mem(expected_mem, Width::D),
        )
    );
    assert_eq!(d.length, 2);
}

#[test]
fn typed_mov_mem_reg() {
    // mov [rdi], eax = 89 07  (ModRM 0x07: mode=0, reg=000, rm=111)
    let d = decode_instruction(&[0x89, 0x07], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RDI),
        index: None,
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Mem(expected_mem, Width::D),
            X86Operand::Reg(Reg::RAX, Width::D),
        )
    );
}

#[test]
fn typed_lea() {
    // lea eax, [rdi] = 8d 07  (ModRM 0x07)
    let d = decode_instruction(&[0x8d, 0x07], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RDI),
        index: None,
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Lea(Reg::RAX, Width::D, expected_mem)
    );
}

#[test]
fn typed_lea_indexed() {
    // lea rax, [rsp + rcx*4] = 48 8d 04 8c
    let d = decode_instruction(&[0x48, 0x8d, 0x04, 0x8c], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RSP),
        index: Some((Reg::RCX, 4)),
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Lea(Reg::RAX, Width::Q, expected_mem)
    );
}

#[test]
fn unmodeled_opcode_bridges_instead_of_dropping() {
    use csolver_ir::{Callee, Inst};
    // `addps xmm0, xmm1` (0f 58 c1) is decoded by the rich typed decoder but not by
    // the byte→MSIR decoder. Sandwiched before `ret`, the function used to drop whole;
    // now it decodes: the unmodeled instruction becomes an opaque call + register havoc.
    let m = decode_function("f", &[0x0f, 0x58, 0xc1, 0xc3]);
    assert!(
        m.unanalyzed.is_empty(),
        "bridged, not dropped: {:?}",
        m.unanalyzed
    );
    let has_havoc_call = m.functions[0].blocks.iter().flat_map(|b| &b.insts).any(
        |i| matches!(i, Inst::Call { callee: Callee::Symbol(s), .. } if s == "<x86 unmodeled>"),
    );
    assert!(
        has_havoc_call,
        "the unmodeled instruction is an opaque havoc call"
    );
}

#[test]
fn unmodeled_control_flow_still_drops() {
    // A control-flow opcode the byte decoder does not handle must NOT be skipped as a
    // havoc (a wrong CFG could be unsound). `jmp r/m` indirect (ff /4) — if unmodeled,
    // it re-raises rather than bridging. (ff e0 = jmp rax.)
    let m = decode_function("f", &[0xff, 0xe0]);
    // Either handled precisely OR dropped — but never silently havoc'd as data-processing.
    let bridged = m.functions.first().is_some_and(|f| {
        f.blocks.iter().flat_map(|b| &b.insts).any(
            |i| matches!(i, csolver_ir::Inst::Call { callee: csolver_ir::Callee::Symbol(s), .. } if s == "<x86 unmodeled>"),
        )
    });
    assert!(!bridged, "control-flow must not be bridged as a data havoc");
}

#[test]
fn recursive_descent_skips_unreachable_trailing_bytes() {
    // `xor eax,eax; ret;` followed by unreachable garbage (0xff 0xff 0xff). A linear
    // sweep would decode the garbage after the ret and drop the whole function; the
    // recursive-descent decode stops at the ret and never touches it — so it decodes.
    let m = decode_function("f", &[0x31, 0xc0, 0xc3, 0xff, 0xff, 0xff]);
    assert!(
        m.unanalyzed.is_empty(),
        "unreachable trailing bytes must not drop the function: {:?}",
        m.unanalyzed
    );
    assert_eq!(m.functions.len(), 1);
}

#[test]
fn direct_call_decodes_as_opaque_and_continues() {
    use csolver_ir::{Callee, Inst};
    // `call rel32 (e8 ..); xor eax,eax (31 c0); ret (c3)` — a function with a call must
    // DECODE (opaque call + fall-through), not drop or stop at the call.
    let m = decode_function("f", &[0xe8, 0x00, 0x00, 0x00, 0x00, 0x31, 0xc0, 0xc3]);
    assert!(
        m.unanalyzed.is_empty(),
        "a call must not drop the function: {:?}",
        m.unanalyzed
    );
    let insts: Vec<_> = m.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .collect();
    assert!(
        insts.iter().any(|i| matches!(
            i,
            Inst::Call {
                callee: Callee::Symbol(_),
                ..
            }
        )),
        "call → opaque Inst::Call"
    );
    // The post-call `xor eax,eax` is still analysed (fall-through past the call).
    assert!(
        insts.iter().any(|i| matches!(i, Inst::Assign { .. })),
        "instructions after the call are decoded"
    );
}
