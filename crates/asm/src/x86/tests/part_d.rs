use super::*;

#[test]
fn typed_sse_maxps_reg_reg() {
    // maxps xmm0, xmm1  = 0f 5f c1
    let d = decode_instruction(&[0x0f, 0x5f, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Maxps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_sqrtps_reg_reg() {
    // sqrtps xmm0, xmm1  = 0f 51 c1
    let d = decode_instruction(&[0x0f, 0x51, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Sqrtps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_shufps_reg_reg() {
    // shufps xmm0, xmm1, 0  = 0f c6 c1 00
    let d = decode_instruction(&[0x0f, 0xc6, 0xc1, 0x00], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Shufps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
            0,
        )
    );
    assert_eq!(d.length, 4);
}

#[test]
fn typed_sse_cmpps_reg_reg() {
    // cmpps xmm0, xmm1, 0  = 0f c2 c1 00
    let d = decode_instruction(&[0x0f, 0xc2, 0xc1, 0x00], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Cmpps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
            0,
        )
    );
}

#[test]
fn typed_sse_ucomiss_reg_reg() {
    // ucomiss xmm0, xmm1  = 0f 2e c1
    let d = decode_instruction(&[0x0f, 0x2e, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Ucomiss(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_comisd_reg_reg() {
    // comisd xmm0, xmm1  = 66 0f 2f c1
    let d = decode_instruction(&[0x66, 0x0f, 0x2f, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Comisd(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_unpcklps_reg_reg() {
    // unpcklps xmm0, xmm1  = 0f 14 c1
    let d = decode_instruction(&[0x0f, 0x14, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Unpcklps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_unpckhpd_reg_reg() {
    // unpckhpd xmm0, xmm1  = 66 0f 15 c1
    let d = decode_instruction(&[0x66, 0x0f, 0x15, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Unpckhpd(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_cvtdq2ps_reg_reg() {
    // cvtdq2ps xmm0, xmm1  = 0f 5b c1
    let d = decode_instruction(&[0x0f, 0x5b, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Cvtdq2ps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_cvtps2dq_reg_reg() {
    // cvtps2dq xmm0, xmm1  = 66 0f 5b c1
    let d = decode_instruction(&[0x66, 0x0f, 0x5b, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Cvtps2dq(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_movups_reg_reg() {
    // movups xmm0, xmm1  = 0f 10 c1
    let d = decode_instruction(&[0x0f, 0x10, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movups(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_movupd_reg_reg() {
    // movupd xmm0, xmm1  = 66 0f 10 c1 — a distinct 16-byte unaligned move,
    // NOT the 8-byte movsd it used to be mis-decoded as.
    let d = decode_instruction(&[0x66, 0x0f, 0x10, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movupd(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_movupd_store() {
    // movupd [rdi], xmm2  = 66 0f 11 17
    let d = decode_instruction(&[0x66, 0x0f, 0x11, 0x17], 0).unwrap();
    assert!(matches!(
        d.instruction,
        Instruction::Movupd(X86Operand::Mem(..), _)
    ));
}

#[test]
fn typed_sse_movss_reg_reg() {
    // movss xmm0, xmm1  = f3 0f 10 c1
    let d = decode_instruction(&[0xf3, 0x0f, 0x10, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Movss(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_paddq_reg_reg() {
    // paddq xmm0, xmm1  = 66 0f d4 c1
    let d = decode_instruction(&[0x66, 0x0f, 0xd4, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Paddq(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_por_reg_reg() {
    // por xmm0, xmm1  = 66 0f eb c1
    let d = decode_instruction(&[0x66, 0x0f, 0xeb, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Por(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_pxor_reg_reg() {
    // pxor xmm0, xmm1  = 66 0f ef c1
    let d = decode_instruction(&[0x66, 0x0f, 0xef, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Pxor(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_pand_reg_reg() {
    // pand xmm0, xmm1  = 66 0f db c1
    let d = decode_instruction(&[0x66, 0x0f, 0xdb, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Pand(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_psubq_reg_reg() {
    // psubq xmm0, xmm1  = 66 0f fb c1
    let d = decode_instruction(&[0x66, 0x0f, 0xfb, 0xc1], 0).unwrap();
    assert_eq!(
        d.instruction,
        Instruction::Psubq(
            xmm_op(XmmReg::XMM0, Width::DQ),
            xmm_op(XmmReg::XMM1, Width::DQ),
        )
    );
}

// --- SSE with memory operand ---

#[test]
fn typed_sse_movaps_load_from_mem() {
    // movaps xmm0, [rax]  = 0f 28 00  (ModRM 00_000_000)
    let d = decode_instruction(&[0x0f, 0x28, 0x00], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RAX),
        index: None,
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Movaps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            X86Operand::Mem(expected_mem, Width::DQ),
        )
    );
}

#[test]
fn typed_sse_addps_load_from_mem() {
    // addps xmm0, [rax]  = 0f 58 00
    let d = decode_instruction(&[0x0f, 0x58, 0x00], 0).unwrap();
    let expected_mem = Mem {
        base: Some(Reg::RAX),
        index: None,
        disp: 0,
    };
    assert_eq!(
        d.instruction,
        Instruction::Addps(
            xmm_op(XmmReg::XMM0, Width::DQ),
            X86Operand::Mem(expected_mem, Width::DQ),
        )
    );
}

// --- VEX-encoded SSE (2-byte VEX prefix C5) ---

// --- VEX-encoded SSE. All byte vectors below are real assembler output
//     (`llvm-mc -triple=x86_64 --show-encoding`). ---
