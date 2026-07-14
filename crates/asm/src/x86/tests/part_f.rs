use super::*;

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
    assert_eq!(
        d.instruction,
        Instruction::Lea(Reg::R8, Width::D, expected_mem)
    );
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
fn typed_memory_alu_decodes() {
    // add [rax], ecx = 01 08  (mod=00, reg=001→rcx, rm=000→rax) — now decoded, not declined.
    let d = decode_instruction(&[0x01, 0x08], 0).expect("memory-destination add decodes");
    assert_eq!(d.length, 2);
    assert!(matches!(d.instruction, Instruction::Add(X86Operand::Mem(..), X86Operand::Reg(..))));
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
        let code = [0x70 | (cc & 0xf), 0x00]; // jo .. jg +0
        let d = decode_instruction(&code, 0).unwrap();
        if let Instruction::Jcc(c, 0) = d.instruction {
            assert!(matches!(
                c,
                Condition::O
                    | Condition::NO
                    | Condition::B
                    | Condition::AE
                    | Condition::E
                    | Condition::NE
                    | Condition::BE
                    | Condition::A
                    | Condition::S
                    | Condition::NS
                    | Condition::P
                    | Condition::NP
                    | Condition::L
                    | Condition::GE
                    | Condition::LE
                    | Condition::G
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
    (
        &[0x66, 0x90],
        "0x66 prefix nop works (positive) not truncated",
    ),
];
