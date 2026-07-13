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
    assert_eq!(
        d.instruction,
        Instruction::Jmp(X86Operand::Rel(0x12345678))
    );
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
fn typed_error_lock_prefix() {
    let r = decode_instruction(&[0xf0, 0x90], 0);
    assert!(r.is_err());
    assert!(r.unwrap_err().to_string().contains("LOCK"));
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

#[test]
fn typed_with_segment_override() {
    // FS segment override (0x64) + nop = 64 90
    let d = decode_instruction(&[0x64, 0x90], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Nop);
}

#[test]
fn typed_offset_propagation() {
    // nop ; ret at offset 1
    let d = decode_instruction(&[0x90, 0xc3], 1).unwrap();
    assert_eq!(d.instruction, Instruction::Ret);
    assert_eq!(d.offset, 1);
}

#[test]
fn typed_rex_b_extends_rm() {
    // mov r8, imm32  = 41 b8 2a 00 00 00  (REX.B on 0xb8)
    let d = decode_instruction(&[0x41, 0xb8, 0x2a, 0x00, 0x00, 0x00], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(X86Operand::Reg(Reg::R8, Width::D), X86Operand::Imm(0x2a))
    );
}

#[test]
fn typed_rex_b_extends_rm_in_mov() {
    // mov r8, ecx  = 41 89 c8  (REX.B=1 extends ModRM.rm rax→r8)
    // 0x89 = mov r/m, r, ModRM 0xc8: mode=11, reg=001(rcx), rm=000
    // rm=000 + REX.B=1 → r8
    let d = decode_instruction(&[0x41, 0x89, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::R8, Width::D),
            X86Operand::Reg(Reg::RCX, Width::D),
        )
    );
}

#[test]
fn typed_lea_r8_indexed() {
    // lea r8d, [rsp + rcx*4]  = 44 8d 04 8c  (REX.R=1, REX.W=0 → width=D)
    let d = decode_instruction(&[0x44, 0x8d, 0x04, 0x8c], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RSP),
        index: Some((Reg::RCX, 4)),
        disp: 0,
    };
    assert_eq!(d.instruction, Instruction::Lea(Reg::R8, Width::D, expected_mem));
}

#[test]
fn typed_displacement_mem() {
    // mov eax, [rdi + 0x1234] = 8b 87 34 12 00 00  (ModRM 0x87: mode=10, reg=000, rm=111)
    let d = decode_instruction(&[0x8b, 0x87, 0x34, 0x12, 0x00, 0x00], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RDI),
        index: None,
        disp: 0x1234,
    };
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Mem(expected_mem, Width::D),
        )
    );
}

#[test]
fn typed_sib_base_index() {
    // mov eax, [rax + rcx]  = 8b 04 08  (SIB scale 1, index rcx, base rax)
    let d = decode_instruction(&[0x8b, 0x04, 0x08], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RAX),
        index: Some((Reg::RCX, 1)),
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Mem(expected_mem, Width::D),
        )
    );
}

#[test]
fn typed_sib_scale8() {
    // mov eax, [rdi + rdx*8]  = 8b 04 d7  (SIB scale 8 = 3<<6, index rdx=010, base rdi=111)
    let d = decode_instruction(&[0x8b, 0x04, 0xd7], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RDI),
        index: Some((Reg::RDX, 8)),
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RAX, Width::D),
            X86Operand::Mem(expected_mem, Width::D),
        )
    );
}

#[test]
fn typed_error_memory_alu_unsupported() {
    // add [rax], ecx = 01 08  (mod=00, reg=001→rcx, rm=000→rax)
    let r = decode_instruction(&[0x01, 0x08], 0);
    assert!(r.is_err());
    assert!(r.unwrap_err().to_string().contains("memory operand"));
}

#[test]
fn typed_error_unsupported_group1_op() {
    // 83 d0 01 → adc eax, 1  (Group 1, /2 = adc, unsupported)
    let r = decode_instruction(&[0x83, 0xd0, 0x01], 0);
    assert!(r.is_err());
    assert!(r.unwrap_err().to_string().contains("unsupported group-1"));
}

#[test]
fn typed_conditional_count() {
    // Verify all 16 conditions decode
    for cc in 0..=15u8 {
        let code = [0x70 | (cc & 0xf), 0x00];  // jo .. jg +0
        let d = decode_instruction(&code, 0).unwrap();
        if let Instruction::Jcc(c, 0) = d.instruction {
            assert!(matches!(
                c,
                Condition::O | Condition::NO | Condition::B | Condition::AE
                    | Condition::E | Condition::NE | Condition::BE | Condition::A
                    | Condition::S | Condition::NS | Condition::P | Condition::NP
                    | Condition::L | Condition::GE | Condition::LE | Condition::G
            ));
        } else {
            panic!("unexpected instruction for cc={cc}");
        }
    }
}

#[test]
fn typed_rex_r_affects_reg_field() {
    // mov rdi, r9  = 4c 89 cf  (REX.W=1, REX.R=1, REX.X=1, REX.B=0)
    // 0x89 = mov r/m, r, ModRM 0xcf: mode=11, reg=001(rcx), rm=111(rdi)
    // reg = 001 + REX.R → 1001 = r9
    // rm = 111 + REX.B → 0111 = rdi
    // REX.W=1 → width = Q
    let d = decode_instruction(&[0x4c, 0x89, 0xcf], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::RDI, Width::Q),
            X86Operand::Reg(Reg::R9, Width::Q),
        )
    );
}

#[test]
fn typed_rex_b_affects_rm_field() {
    // mov r15, eax  = 41 89 c7  (REX.B=1 extends ModRM.rm rdi→r15)
    // 0x89 = mov r/m, r, ModRM 0xc7: mode=11, reg=000(eax), rm=111
    // rm=111 + REX.B=1 → 1111 = r15
    let d = decode_instruction(&[0x41, 0x89, 0xc7], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mov(
            X86Operand::Reg(Reg::R15, Width::D),
            X86Operand::Reg(Reg::RAX, Width::D),
        )
    );
}

// ========================================================================
// Comprehensive negative / adversarial tests
// ========================================================================

pub(super) const TRUNCATED_OPS: &[(&[u8], &str)] = &[
    // opcode without immediate
    (&[0xb8], "mov eax, imm32 truncated"),
    (&[0x48, 0xb8], "mov rax, imm64 truncated"),
    (&[0xbf], "mov edi, imm32 truncated"),
    // opcode without ModRM
    (&[0x89], "mov r/m, r truncated ModRM"),
    (&[0x8b], "mov r, r/m truncated ModRM"),
    (&[0x31], "xor r/m, r truncated ModRM"),
    (&[0x01], "add r/m, r truncated ModRM"),
    (&[0x29], "sub r/m, r truncated ModRM"),
    (&[0x39], "cmp r/m, r truncated ModRM"),
    (&[0x3b], "cmp r, r/m truncated ModRM"),
    (&[0x85], "test r/m, r truncated ModRM"),
    (&[0x63], "movsxd truncated ModRM"),
    (&[0x87], "xchg r/m, r truncated ModRM"),
    // push/pop with imm
    (&[0x6a], "push imm8 truncated"),
    (&[0x68], "push imm32 truncated"),
    // mov r/m, imm
    (&[0xc6], "mov r/m, imm8 truncated ModRM"),
    (&[0xc7], "mov r/m, imm32 truncated ModRM"),
    // Group 1 imm8 without imm8
    (&[0x83, 0xc0], "add imm8 truncated"),
    (&[0x83, 0xe8], "sub imm8 truncated"),
    (&[0x83, 0xf8], "cmp imm8 truncated"),
    // Group 2 shift with imm8 (opcode 0xc1)
    (&[0xc1], "group2 shift truncated ModRM"),
    (&[0xc1, 0xe0], "group2 shift imm8 truncated"),
    // Group 3 (0xf6 /0xf7)
    (&[0xf6], "group3 truncated ModRM"),
    (&[0xf7], "group3 32bit truncated ModRM"),
    // Group 4 (0xfe inc/dec r/m8)
    (&[0xfe], "group4 truncated ModRM"),
    // Group 5 (0xff inc/dec/jmp/call r/m)
    (&[0xff], "group5 truncated ModRM"),
    // ModRM without SIB (ModRM.rm=4 triggers SIB)
    (&[0x8b, 0x04], "SIB required but truncated"),
    // ModRM with mode=01 requires disp8
    (&[0x8b, 0x4f], "ModRM mod=01 requires disp8"),
    // ModRM with mode=10 requires disp32
    (&[0x8b, 0x8f], "ModRM mod=10 requires disp32"),
    // jcc rel8 without imm
    (&[0x70], "jcc rel8 truncated"),
    (&[0x75], "jne rel8 truncated"),
    // jmp rel8/rel32 without imm
    (&[0xeb], "jmp rel8 truncated"),
    (&[0xe9], "jmp rel32 truncated"),
    // 0x0f without second opcode
    (&[0x0f], "two-byte escape truncated"),
    // 0x0f jcc rel32 without rel32
    (&[0x0f, 0x84], "0F jcc rel32 truncated"),
    // 0x0f movzx without ModRM
    (&[0x0f, 0xb6], "movzx truncated ModRM"),
    (&[0x0f, 0xb7], "movzx word truncated ModRM"),
    // 0x0f movsx without ModRM
    (&[0x0f, 0xbe], "movsx truncated ModRM"),
    (&[0x0f, 0xbf], "movsx word truncated ModRM"),
    // 0x0f setcc without ModRM
    (&[0x0f, 0x90], "setcc truncated ModRM"),
    (&[0x0f, 0x9c], "setcc setl truncated ModRM"),
    // RIP-relative requires disp32
    (&[0x8b, 0x05], "RIP-relative disp32 truncated"),
    // disp32 with SIB and no base
    (&[0x8b, 0x04, 0x25], "SIB mod=00 base=5 disp32 truncated"),
    // Prefix chain truncated
    (&[0x66, 0x90], "0x66 prefix nop works (positive) not truncated"),
];
