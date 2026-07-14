use super::*;

#[test]
fn typed_jne_rel8() {
    // jne +4 = 75 04
    let d = decode_instruction(&[0x75, 0x04], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Jcc(Condition::NE, 4));
    assert_eq!(d.length, 2);
}

#[test]
fn typed_je_rel8_negative() {
    // je -8 = 74 f8
    let d = decode_instruction(&[0x74, 0xf8], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Jcc(Condition::E, -8));
}

#[test]
fn typed_jmp_rel8() {
    // jmp -2 = eb fe
    let d = decode_instruction(&[0xeb, 0xfe], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Jmp(X86Operand::Rel(-2)));
    assert_eq!(d.length, 2);
}

#[test]
fn typed_jmp_rel32() {
    // jmp +0x12345678 = e9 78 56 34 12
    let d = decode_instruction(&[0xe9, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Jmp(X86Operand::Rel(0x12345678)));
    assert_eq!(d.length, 5);
}

#[test]
fn typed_jcc_two_byte() {
    // je +0x12345678 = 0f 84 78 56 34 12
    let d = decode_instruction(&[0x0f, 0x84, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Jcc(Condition::E, 0x12345678));
    assert_eq!(d.length, 6);
}

#[test]
fn typed_jcc_two_byte_jle() {
    // jle +0x100 = 0f 8e 00 01 00 00
    let d = decode_instruction(&[0x0f, 0x8e, 0x00, 0x01, 0x00, 0x00], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Jcc(Condition::LE, 0x100));
}

#[test]
fn typed_cmp_reg_reg() {
    // cmp eax, ecx = 39 c8  (r/m, r)
    let d = decode_instruction(&[0x39, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Cmp(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RCX, Width::D),
        )
    );
}

#[test]
fn typed_cmp_reg_reg_r() {
    // cmp eax, ecx = 3b c1  (r, r/m)
    let d = decode_instruction(&[0x3b, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Cmp(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RCX, Width::D),
        )
    );
}

#[test]
fn typed_cmp_eax_imm() {
    // cmp eax, 0x7f = 3d 7f 00 00 00
    let d = decode_instruction(&[0x3d, 0x7f, 0x00, 0x00, 0x00], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Cmp(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0x7f))
    );
}

#[test]
fn typed_test_reg_reg() {
    // test eax, ecx = 85 c8
    let d = decode_instruction(&[0x85, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Test(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RCX, Width::D),
        )
    );
}

#[test]
fn typed_add_imm8() {
    // add eax, 1 = 83 c0 01  (Group 1, /0 = add, imm8)
    let d = decode_instruction(&[0x83, 0xc0, 0x01], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Add(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(1))
    );
}

#[test]
fn typed_sub_imm8() {
    // sub eax, 1 = 83 e8 01  (Group 1, /5 = sub, imm8)
    let d = decode_instruction(&[0x83, 0xe8, 0x01], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Sub(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(1))
    );
}

#[test]
fn typed_cmp_imm8() {
    // cmp eax, 0 = 83 f8 00  (Group 1, /7 = cmp, imm8)
    let d = decode_instruction(&[0x83, 0xf8, 0x00], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Cmp(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0))
    );
}

#[test]
fn typed_and_imm8() {
    // and eax, 0x0f = 83 e0 0f  (Group 1, /4 = and, imm8)
    let d = decode_instruction(&[0x83, 0xe0, 0x0f], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::And(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0x0f))
    );
}

#[test]
fn typed_rip_relative_mov() {
    // mov rax, [rip + 0x12345678] = 48 8b 05 78 56 34 12
    // ModRM 0x05: mod=00, reg=000 (rax), rm=101 → RIP-relative
    let d = decode_instruction(&[0x48, 0x8b, 0x05, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
    let expected_mem = Mem {
        base: None,
        index: None,
        disp: 0x12345678,
    };
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RAX, Width::Q),
            X86Operand::Mem(expected_mem, Width::Q),
        )
    );
}

#[test]
fn typed_movzx() {
    // movzx eax, byte [rdi] = 0f b6 07
    let d = decode_instruction(&[0x0f, 0xb6, 0x07], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RDI),
        index: None,
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Movzx(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Mem(expected_mem, Width::B),
        )
    );
}

#[test]
fn typed_movzx_reg() {
    // movzx eax, cl = 0f b6 c1
    let d = decode_instruction(&[0x0f, 0xb6, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movzx(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Reg(Reg::RCX, Width::B),
        )
    );
}

#[test]
fn typed_movsx() {
    // movsx eax, byte [rdi] = 0f be 07
    let d = decode_instruction(&[0x0f, 0xbe, 0x07], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RDI),
        index: None,
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Movsx(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Mem(expected_mem, Width::B),
        )
    );
}

#[test]
fn typed_error_truncated_opcode() {
    let r = decode_instruction(&[], 0);
    assert!(r.is_err());
}

#[test]
fn typed_error_truncated_modrm() {
    let r = decode_instruction(&[0x89], 0);
    assert!(r.is_err());
}

#[test]
fn typed_error_unsupported_opcode() {
    // 0x06 (PUSH ES) is invalid in 64-bit mode — not decoded.
    let r = decode_instruction(&[0x06], 0);
    assert!(r.is_err());
    assert!(r.unwrap_err().to_string().contains("unsupported"));
}

#[test]
fn typed_error_unsupported_two_byte() {
    // 0F 06 (CLTS) is not handled → unsupported
    let r = decode_instruction(&[0x0f, 0x06], 0);
    assert!(r.is_err());
    assert!(r.unwrap_err().to_string().contains("unsupported"));
}

#[test]
fn typed_lock_prefix_is_consumed() {
    // LOCK is a 1-byte prefix; the typed decoder now consumes it and decodes the rest,
    // rather than declining the instruction. (`f0 90` — the prefix then a NOP.)
    let d = decode_instruction(&[0xf0, 0x90], 0).expect("lock prefix is consumed");
    assert_eq!(d.instruction, Instruction::Nop);
    assert_eq!(d.length, 2, "prefix + opcode");
}

#[test]
fn typed_acccepts_rep_prefix() {
    // REP prefix is accepted and ignored
    let d = decode_instruction(&[0xf3, 0x90], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Nop);
}

#[test]
fn typed_prefix_66_not_rex() {
    // 0x66 0x90 = nop with 16-bit operand size override
    let d = decode_instruction(&[0x66, 0x90], 0).unwrap();
    assert!(d.prefixes.operand_size);
    assert!(!d.prefixes.rex);
    assert_eq!(d.instruction, Instruction::Nop);
}
