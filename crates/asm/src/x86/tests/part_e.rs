use super::*;

#[test]
fn typed_vex_movaps_reg_reg() {
    // vmovaps %xmm1, %xmm0  = c5 f8 28 c1  (2-byte VEX: mmmmm=0F, pp=none, W=0)
    let d = decode_instruction(&[0xc5, 0xf8, 0x28, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movaps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_vex_addps_reg_reg() {
    // vaddps %xmm2, %xmm0, %xmm0  = c5 f8 58 c2  (the vvvv third operand,
    // xmm0 here, is not representable in the 2-operand Addps and is dropped)
    let d = decode_instruction(&[0xc5, 0xf8, 0x58, 0xc2], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Addps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM2, Width::DQ),
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_vex_movapd_2byte() {
    // vmovapd %xmm1, %xmm0  = c5 f9 28 c1  (2-byte VEX, pp=66)
    let d = decode_instruction(&[0xc5, 0xf9, 0x28, 0xc1], 0).unwrap();
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
fn typed_vex_0f38_pmulld() {
    // vpmulld %xmm2, %xmm0, %xmm0  = c4 e2 79 40 c2  (3-byte VEX, map 0F38, pp=66)
    let d = decode_instruction(&[0xc4, 0xe2, 0x79, 0x40, 0xc2], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Pmulld(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM2, Width::DQ),
        )
    );
    assert_eq!(d.length, 5);
}

#[test]
fn typed_vex_0f3a_roundps() {
    // vroundps $1, %xmm1, %xmm0  = c4 e3 79 08 c1 01  (3-byte VEX, map 0F3A, pp=66)
    let d = decode_instruction(&[0xc4, 0xe3, 0x79, 0x08, 0xc1, 0x01], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Roundps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
            1,
        )
    );
    assert_eq!(d.length, 6);
}

#[test]
fn typed_vex_0f3a_palignr() {
    // vpalignr $3, %xmm1, %xmm0, %xmm0  = c4 e3 79 0f c1 03
    let d = decode_instruction(&[0xc4, 0xe3, 0x79, 0x0f, 0xc1, 0x03], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Palignr(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
            3,
        )
    );
    assert_eq!(d.length, 6);
}

// --- Extended registers (xmm8..15). These exercise the VEX.R/VEX.B
//     extension bits — the class of bug the previous decoder got wrong. ---

#[test]
fn typed_vex_2byte_rexr_dst() {
    // vmovaps %xmm1, %xmm8  = c5 78 28 c1  (2-byte VEX.~R=0 → reg extended)
    let d = decode_instruction(&[0xc5, 0x78, 0x28, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movaps(
            xmm_op(XmmReg::XMM8, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_vex_2byte_rexr_store_src() {
    // vmovaps %xmm9, %xmm0  = c5 78 29 c8  (store form; reg=xmm9 via VEX.~R=0)
    let d = decode_instruction(&[0xc5, 0x78, 0x29, 0xc8], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movaps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM9, Width::DQ),
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_vex_3byte_rexr_and_rexb() {
    // vmovaps %xmm9, %xmm8  = c4 41 78 28 c1  (3-byte: VEX.~R=0 → reg=xmm8,
    // VEX.~B=0 → rm=xmm9). Threading VEX.B is exactly what was broken before.
    let d = decode_instruction(&[0xc4, 0x41, 0x78, 0x28, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movaps(
            xmm_op(XmmReg::XMM8, Width::DQ),
            xmm_op(XmmReg::XMM9, Width::DQ),
        )
    );
    assert_eq!(d.length, 5);
}

#[test]
fn typed_vex_0f38_rexb_rm() {
    // vpmulld %xmm9, %xmm0, %xmm0  = c4 c2 79 40 c1  (rm=xmm9 via VEX.~B=0)
    let d = decode_instruction(&[0xc4, 0xc2, 0x79, 0x40, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Pmulld(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM9, Width::DQ),
        )
    );
    assert_eq!(d.length, 5);
}

// --- SSE error cases ---

#[test]
fn typed_sse_truncated_modrm() {
    // 0f 10 with no ModRM byte → truncated
    let r = decode_instruction(&[0x0f, 0x10], 0);
    assert!(r.is_err());
}

#[test]
fn typed_unsupported_two_byte_sse() {
    // 0F 0x12 is not currently handled → unsupported
    let r = decode_instruction(&[0x0f, 0x12, 0xc1], 0);
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn typed_syscall() {
    let d = decode_instruction(&[0x0f, 0x05], 0).unwrap();
    assert_eq!(d.instruction, Instruction::Syscall);
    assert_eq!(d.length, 2);
}

// ========================================================================
// Negative: ModRM /digit and mode edge cases
// ========================================================================

#[test]
fn rejects_group2_imm8_unsupported_digit() {
    // 0xc1 /6 eax, 3 → group-2 reserved /digit
    let r = decode_instruction(&[0xc1, 0xf0, 0x03], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_group2_shift1_unsupported_digit() {
    // 0xd1 /6 eax → group-2 shift-by-1 reserved /digit
    let r = decode_instruction(&[0xd1, 0xf0], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_group2_imm8_unsupported_digit_byte() {
    // 0xc0 /6 al, 3 → group-2 reserved /digit (byte variant)
    let r = decode_instruction(&[0xc0, 0xf0, 0x03], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_group3_memory_operand() {
    // 0xf7 /0 [rax] → test [rax], imm32 — memory form unsupported
    let r = decode_instruction(&[0xf7, 0x00, 0x01, 0x00, 0x00, 0x00], 0);
    assert!(r.is_err());
    assert!(r
        .unwrap_err()
        .to_string()
        .contains("group-3 with a memory operand"));
}

#[test]
fn rejects_group3_unsupported_digit() {
    // 0xf7 /1 eax → group-3 reserved /digit
    let r = decode_instruction(&[0xf7, 0xc8], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_group4_memory_operand() {
    // 0xfe /0 [rax] → inc byte [rax] — memory form unsupported
    let r = decode_instruction(&[0xfe, 0x00], 0);
    assert!(r.is_err());
    assert!(r.unwrap_err().to_string().contains("memory operand"));
}

#[test]
fn rejects_group4_unsupported_digit() {
    // 0xfe /6 al → group-4 reserved /digit
    // ModRM: 0xe0 = 11 110 000 → mode=11, reg=6, rm=0 (al)
    let r = decode_instruction(&[0xfe, 0xe0], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_group5_memory_operand() {
    // 0xff /4 [rax] → jmp [rax] — memory form unsupported
    let r = decode_instruction(&[0xff, 0x20], 0);
    assert!(r.is_err());
    assert!(r.unwrap_err().to_string().contains("memory operand"));
}

#[test]
fn rejects_group5_unsupported_digit() {
    // 0xff /3 eax → lcall eax — unsupported
    let r = decode_instruction(&[0xff, 0xd8], 0);
    assert!(r.is_err());
    assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
}

#[test]
fn rejects_baseless_disp32_sib_truncated() {
    // mov eax, [sib: mod=00, base=5] requires a disp32.
    // SIB byte: 0x25 = 00 100 101 → mod=00, index_field=4 (no index), base_field=5
    // The typed decoder reads disp32 even in the base-less case, so this is just a truncation test.
    let r = decode_instruction(&[0x8b, 0x04, 0x25], 0);
    assert!(r.is_err());
}

#[test]
fn rejects_xchg_memory_form() {
    // 0x87 /r only supports register form in our decoder.
    // 87 00 = xchg [rax], eax — unsupported memory operand
    let r = decode_instruction(&[0x87, 0x00], 0);
    assert!(r.is_err());
    assert!(r.unwrap_err().to_string().contains("memory operand"));
}
