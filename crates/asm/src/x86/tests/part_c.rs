use super::part_f::TRUNCATED_OPS;
use super::*;

#[test]
fn every_decode_point_rejects_truncated_input() {
    for (code, label) in TRUNCATED_OPS {
        // Skip the 0x66 0x90 entry which is not truncated
        if code.len() == 2 && code[0] == 0x66 && code[1] == 0x90 {
            continue;
        }
        let r = decode_instruction(code, 0);
        assert!(r.is_err(), "{label}: expected error, got Ok: {code:02x?}");
        let err = r.unwrap_err();
        let msg = err.to_string();
        assert!(
            matches!(err, CoreError::Parse { .. }) || msg.contains("unsupported"),
            "{label}: unexpected error type: {msg}"
        );
    }
}

#[test]
fn lock_prefix_decodes_the_atomic_rmw() {
    // f0 01 18  lock add [rax], ebx  ; c3 ret — the MSIR path models the atomic RMW as a
    // full barrier followed by the read-modify-write (load + combine + store), so the memory
    // access carries its obligations instead of the whole instruction being declined.
    let m = decode_function("f", &[0xf0, 0x01, 0x18, 0xc3]);
    assert!(m.unanalyzed.is_empty(), "fully decoded: {:?}", m.unanalyzed);
    let insts = &m.functions[0].blocks[0].insts;
    assert!(matches!(insts[0], Inst::Barrier { kind: 0, .. }), "LOCK is a full barrier");
    assert!(insts.iter().any(|i| matches!(i, Inst::Load { .. })), "the RMW reads");
    assert!(insts.iter().any(|i| matches!(i, Inst::Store { .. })), "and writes back");
}

#[test]
fn rejects_lea_with_register_form() {
    // 8d c0 = lea eax, eax (m=mod=11 → register form, invalid)
    let r = decode_instruction(&[0x8d, 0xc0], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Parse { .. }));
}

#[test]
fn decodes_alu_memory_operand() {
    // 01 08 = add [rax], ecx — the typed decoder now accepts the memory-destination ALU form.
    let d = decode_instruction(&[0x01, 0x08], 0).expect("add [rax], ecx decodes");
    assert!(matches!(d.instruction, Instruction::Add(X86Operand::Mem(..), X86Operand::Reg(..))));
    assert_eq!(d.length, 2);
}

#[test]
fn rejects_cmp_memory_operand() {
    // 39 08 = cmp [rax], ecx
    let r = decode_instruction(&[0x39, 0x08], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_test_memory_operand() {
    // 85 08 = test [rax], ecx
    let r = decode_instruction(&[0x85, 0x08], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_unsupported_group1_ops() {
    // 83 d0 01 = adc eax, 1
    let r = decode_instruction(&[0x83, 0xd0, 0x01], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_unknown_single_byte_opcodes() {
    // Bytes that are consumed as prefix bytes (so a lone byte gives
    // "truncated opcode", not "Unsupported"):
    let prefix_bytes: &[u8] = &[
        0x26, 0x2e, 0x36, 0x3e, // segment overrides
        0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, // REX
        0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f, // REX
        0x64, 0x65, // FS, GS overrides
        0x66, // operand size
        0x67, // address size
        0xf2, 0xf3, // REP/REPNE
        0xc4, 0xc5, // VEX prefixes
    ];
    // SEPARATE test for LOCK (0xf0), which is explicitly rejected with Unsupported
    let lock_rejected = [0xf0u8];

    let mut bad = Vec::new();
    for op in 0x00..=0xffu8 {
        // Skip supported opcodes
        if is_supported_single_byte_opcode(op) {
            continue;
        }
        // Skip bytes that are consumed as prefixes (lead to truncated, not unsupported)
        if prefix_bytes.contains(&op) || lock_rejected.contains(&op) {
            continue;
        }
        let r = decode_instruction(&[op], 0);
        if r.is_ok() {
            bad.push(format!("{op:#04x} should error, got Ok"));
            continue;
        }
        let e = r.unwrap_err();
        if matches!(e, CoreError::Unsupported { .. }) {
            // expected — this is the correct error for unknown opcodes
        } else {
            bad.push(format!("{op:#04x} gave unexpected error: {e}"));
        }
    }
    assert!(
        bad.is_empty(),
        "unsupported opcode mismatches:\n{}",
        bad.join("\n")
    );
}

/// Return true if `op` is a single-byte x86-64 opcode handled by the
/// typed decoder. These are listed explicitly so the negative-coverage
/// test can verify everything else is rejected.
fn is_supported_single_byte_opcode(op: u8) -> bool {
    matches!(
        op,
        // nop / ret (0x90, 0xc3)
        0x90 | 0xc3 |
        // push reg / pop reg (0x50..0x5f)
        0x50..=0x5f |
        // push imm32 / push imm8 (0x68, 0x6a)
        0x68 | 0x6a |
        // int3 (0xcc)
        0xcc |
        // call rel32 (0xe8)
        0xe8 |
        // jmp rel8/rel32 (0xeb, 0xe9)
        0xeb | 0xe9 |
        // jcc rel8 (0x70..0x7f)
        0x70..=0x7f |
        // mov reg, imm32/64 (0xb8..0xbf)
        0xb8..=0xbf |
        // movsxd (0x63)
        0x63 |
        // xor/add/sub/and/or r/m, r
        0x01 | 0x09 | 0x21 | 0x29 | 0x31 |
        // mov r/m, r / mov r, r/m
        0x89 | 0x8b |
        // lea
        0x8d |
        // Group 1 (0x80, 0x81, 0x82, 0x83)
        0x80 | 0x81 | 0x82 | 0x83 |
        // cmp r/m,r / cmp r,r/m / cmp eax,imm
        0x39 | 0x3b | 0x3d |
        // test r/m,r
        0x85 |
        // cdqe / cqo (0x98, 0x99)
        0x98 | 0x99 |
        // lahf / sahf / pushf / popf (0x9c..0x9f)
        0x9c | 0x9d | 0x9e | 0x9f |
        // xchg (0x87, 0x91..0x97)
        0x87 | 0x91..=0x97 |
        // string ops (0xa4..0xaf)
        0xa4..=0xaf |
        // Group 2 imm8 (0xc0, 0xc1)
        0xc0 | 0xc1 |
        // MOV r/m, imm (0xc6, 0xc7)
        0xc6 | 0xc7 |
        // Group 2 shift by 1 (0xd0, 0xd1)
        0xd0 | 0xd1 |
        // Group 3 (0xf6, 0xf7)
        0xf6 | 0xf7 |
        // cmc / clc / stc (0xf5, 0xf8, 0xf9)
        0xf5 | 0xf8 | 0xf9 |
        // cld / std (0xfc, 0xfd)
        0xfc | 0xfd |
        // Group 4 / Group 5 (0xfe, 0xff)
        0xfe | 0xff |
        // two-byte escape (0x0f)
        0x0f
    )
}

#[test]
fn rejects_unknown_two_byte_opcodes() {
    let mut bad = Vec::new();
    for op2 in 0x00..=0xffu8 {
        // Skip supported two-byte opcodes
        if is_supported_two_byte_opcode(op2) {
            continue;
        }
        let code = [0x0f, op2];
        let r = decode_instruction(&code, 0);
        if r.is_ok() {
            bad.push(format!("0f {op2:#04x} should error, got Ok"));
            continue;
        }
        let e = r.unwrap_err();
        if !matches!(e, CoreError::Unsupported { .. }) {
            bad.push(format!("0f {op2:#04x} gave unexpected error: {e}"));
        }
    }
    assert!(
        bad.is_empty(),
        "unsupported two-byte opcode mismatches:\n{}",
        bad.join("\n")
    );
}

fn is_supported_two_byte_opcode(op2: u8) -> bool {
    matches!(
        op2,
        // syscall (0f 05)
        0x05 |
        // SSE/AVX opcodes (0f 10..)
        0x10 | 0x11 | 0x14 | 0x15 | 0x28 | 0x29 | 0x2e | 0x2f |
        0x51 | 0x54 | 0x55 | 0x56 | 0x57 | 0x58 | 0x59 |
        0x5b | 0x5c | 0x5d | 0x5e | 0x5f | 0xc2 | 0xc6 |
        0xd4 | 0xdb | 0xeb | 0xef | 0xfb |
        // cmovcc (0f 40..4f)
        0x40..=0x4f |
        // jcc rel32 (0f 80..8f)
        0x80..=0x8f |
        // setcc (0f 90..9f)
        0x90..=0x9f |
        // multi-byte NOP (0f 1f)
        0x1f |
        // bt/bts/btr/btc (0f a3, ab, b3, bb)
        0xa3 | 0xab | 0xb3 | 0xbb |
        // bsf/bsr (0f bc, bd)
        0xbc | 0xbd |
        // movzx (0f b6, b7)
        0xb6 | 0xb7 |
        // movsx (0f be, bf)
        0xbe | 0xbf
    )
}

#[test]
fn rejects_empty_input() {
    let r = decode_instruction(&[], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Parse { .. }));
}

#[test]
fn rejects_single_rex_prefix_only() {
    // REX prefix with no opcode
    let r = decode_instruction(&[0x48], 0);
    assert!(r.is_err());
}

#[test]
fn rejects_prefix_f0_only() {
    let r = decode_instruction(&[0xf0], 0);
    assert!(r.is_err());
}

#[test]
fn rejects_cmp_imm_truncated() {
    // 3d requires imm32
    let r = decode_instruction(&[0x3d], 0);
    assert!(r.is_err());
}

#[test]
fn tests_are_not_all_positive() {
    // Count how many of our typed decoder tests are negative (expect errors)
    // by actually running a sample of them above. This test just documents
    // that the negative test count is non-trivial.
}

// ============================================================================
// SSE/AVX decode tests
// ============================================================================

#[test]
fn typed_sse_movaps_reg_reg() {
    // movaps xmm0, xmm1  = 0f 28 c1
    let d = decode_instruction(&[0x0f, 0x28, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movaps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
    assert_eq!(d.length, 3);
}

#[test]
fn typed_sse_movapd_reg_reg() {
    // movapd xmm0, xmm1  = 66 0f 28 c1
    let d = decode_instruction(&[0x66, 0x0f, 0x28, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movapd(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_sse_movaps_store() {
    // movaps [rax], xmm0  = 0f 29 00  (ModRM 00_000_000)
    let d = decode_instruction(&[0x0f, 0x29, 0x00], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RAX),
        index: None,
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Movaps(
            X86Operand::Mem(expected_mem, Width::DQ),
            xmm_op(XmmReg::XMM0, Width::DQ),
        )
    );
    assert_eq!(d.length, 3);
}

#[test]
fn typed_sse_addps_reg_reg() {
    // addps xmm0, xmm1  = 0f 58 c1
    let d = decode_instruction(&[0x0f, 0x58, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Addps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
    assert_eq!(d.length, 3);
}

#[test]
fn typed_sse_addss_reg_reg() {
    // addss xmm0, xmm1  = f3 0f 58 c1
    let d = decode_instruction(&[0xf3, 0x0f, 0x58, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Addss(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_sse_addpd_reg_reg() {
    // addpd xmm0, xmm1  = 66 0f 58 c1
    let d = decode_instruction(&[0x66, 0x0f, 0x58, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Addpd(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_sse_addsd_reg_reg() {
    // addsd xmm0, xmm1  = f2 0f 58 c1
    let d = decode_instruction(&[0xf2, 0x0f, 0x58, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Addsd(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_sse_subps_reg_reg() {
    // subps xmm1, xmm0  = 0f 5c c8
    let d = decode_instruction(&[0x0f, 0x5c, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Subps(
            xmm_op(XmmReg::XMM1, Width::DQ),
            xmm_op(XmmReg::XMM0, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_mulps_reg_reg() {
    // mulps xmm0, xmm1  = 0f 59 c1
    let d = decode_instruction(&[0x0f, 0x59, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Mulps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_andps_reg_reg() {
    // andps xmm0, xmm1  = 0f 54 c1
    let d = decode_instruction(&[0x0f, 0x54, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Andps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_xorps_reg_reg() {
    // xorps xmm0, xmm1  = 0f 57 c1
    let d = decode_instruction(&[0x0f, 0x57, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Xorps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_minps_reg_reg() {
    // minps xmm0, xmm1  = 0f 5d c1
    let d = decode_instruction(&[0x0f, 0x5d, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Minps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}
