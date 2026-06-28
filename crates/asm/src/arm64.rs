//! A minimal AArch64 (ARM64) machine-code decoder → MSIR.
//!
//! AArch64 instructions are fixed 32-bit little-endian words decoded by field
//! extraction (no prefixes or ModR/M). This decodes a *small, growing* subset
//! and lowers a straight-line function to MSIR, mirroring the x86-64 frontend so
//! the audited analysis core verifies an ARM binary with no source. Registers
//! `x0..x30`/`sp` become MSIR `RegId`s (the encoding number); a `[base, #off]`
//! access becomes a `PtrOffset` + `Load`/`Store`.
//!
//! ## Soundness by graceful degradation
//! Any unrecognized encoding makes the *whole function* `unanalyzed` (reported
//! `UNKNOWN`), never guessed at — so the decoder can only be incomplete, never
//! unsound (a silently mis-modelled instruction could fabricate a false `PASS`).

use csolver_core::RegionKind;
use csolver_ir::{
    BasicBlock, BinOp, BlockId, FuncId, Function, Inst, Module, Operand, RValue, RegId, Terminator,
    Type,
};

/// The stack-pointer register number in `add`/`sub` immediate and load/store
/// (where register 31 denotes `sp`, not the zero register).
const SP: u8 = 31;

fn reg(num: u8) -> RegId {
    RegId(num as u32)
}

fn temp_reg(pos: usize) -> RegId {
    RegId(1000 + pos as u32)
}

/// Decode a straight-line AArch64 function into a one-function [`Module`]. On any
/// unsupported encoding the function is recorded as `unanalyzed` (⇒ `UNKNOWN`).
pub fn decode_function(name: &str, code: &[u8]) -> Module {
    let mut m = Module::new("bin");
    match decode_block(code) {
        Ok(insts) => {
            let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
            bb.insts = insts;
            m.functions.push(Function {
                id: FuncId(0),
                name: name.into(),
                params: arg_registers(),
                ret_ty: Type::Unit,
                blocks: vec![bb],
                entry: BlockId(0),
            });
        }
        Err(reason) => m.unanalyzed.push((name.into(), reason)),
    }
    m
}

/// The AArch64 PCS integer argument registers `x0..x7`, modelled as parameters so
/// each input register is a stable symbol (a guard can then constrain a later
/// access, as on x86).
fn arg_registers() -> Vec<(RegId, Type)> {
    (0u8..8).map(|r| (reg(r), Type::int(64))).collect()
}

fn decode_block(code: &[u8]) -> Result<Vec<Inst>, String> {
    if !code.len().is_multiple_of(4) {
        return Err("arm64: code length is not a multiple of 4".into());
    }
    let mut insts = Vec::new();
    let mut pos = 0;
    while pos + 4 <= code.len() {
        let word = u32::from_le_bytes([code[pos], code[pos + 1], code[pos + 2], code[pos + 3]]);
        let (decoded, is_ret) = decode_one(word, pos)?;
        insts.extend(decoded);
        pos += 4;
        if is_ret {
            break;
        }
    }
    Ok(insts)
}

/// Decode one 32-bit instruction `word` at byte offset `pos`. Returns its MSIR
/// and whether it is a `ret`.
fn decode_one(word: u32, pos: usize) -> Result<(Vec<Inst>, bool), String> {
    // RET {Xn} — `1101011 0010 11111 0000 00 Rn 00000`; the common `ret` (x30).
    if word & 0xffff_fc1f == 0xd65f_0000 {
        return Ok((Vec::new(), true));
    }

    // ADD/SUB (immediate): bits[28:24] == 10001.
    if (word >> 24) & 0x1f == 0b1_0001 {
        let sf = (word >> 31) & 1;
        let is_sub = (word >> 30) & 1 == 1;
        let shift12 = (word >> 22) & 1 == 1;
        let mut imm = (word >> 10) & 0xfff;
        if shift12 {
            imm <<= 12;
        }
        let rn = ((word >> 5) & 0x1f) as u8;
        let rd = (word & 0x1f) as u8;
        let width = if sf == 1 { 64 } else { 32 };
        let ty = Type::int(width);
        // `sub sp, sp, #N` allocates the stack frame; `add sp, sp, #N` tears it
        // down (a no-op for the analysis).
        if rd == SP && rn == SP {
            return if is_sub {
                Ok((
                    vec![Inst::Alloc {
                        dst: reg(SP),
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, imm as u128),
                        align: 16,
                    }],
                    false,
                ))
            } else {
                Ok((Vec::new(), false))
            };
        }
        let op = if is_sub { BinOp::Sub } else { BinOp::Add };
        return Ok((
            vec![Inst::Assign {
                dst: reg(rd),
                ty,
                value: RValue::Bin { op, lhs: Operand::Reg(reg(rn)), rhs: Operand::int(width, imm as u128) },
            }],
            false,
        ));
    }

    // LDR/STR (immediate, unsigned offset), integer: bits[29:24] == 111001.
    if (word >> 24) & 0x3f == 0b11_1001 {
        let size = (word >> 30) & 3; // 0=byte..3=8 bytes
        let opc = (word >> 22) & 3; // 00=STR, 01=LDR (unsigned)
        let imm12 = (word >> 10) & 0xfff;
        let rn = ((word >> 5) & 0x1f) as u8;
        let rt = (word & 0x1f) as u8;
        let access = 1u64 << size; // bytes
        let byte_off = imm12 as u64 * access; // unsigned offset is scaled
        let ty = Type::int((8 * access) as u32);
        let width = (8 * access) as u32;
        let ptr = temp_reg(pos);
        let off = Inst::PtrOffset {
            dst: ptr,
            base: Operand::Reg(reg(rn)),
            index: Operand::int(64, byte_off as u128),
            elem: Type::int(8),
        };
        return match opc {
            0 => {
                // STR Rt, [Rn, #off]; register 31 here is the zero register.
                let value = if rt == 31 { Operand::int(width, 0) } else { Operand::Reg(reg(rt)) };
                Ok((vec![off, Inst::Store { ty, ptr: Operand::Reg(ptr), value, align: 1 }], false))
            }
            1 => {
                // LDR Rt, [Rn, #off]; loading into the zero register is a discard.
                let dst = if rt == 31 { temp_reg(pos + 1) } else { reg(rt) };
                Ok((vec![off, Inst::Load { dst, ty, ptr: Operand::Reg(ptr), align: 1 }], false))
            }
            _ => Err("arm64: unsupported load/store variant".into()),
        };
    }

    Err(format!("arm64: unsupported instruction {word:#010x}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `sub sp,sp,#16 ; str w0,[sp,#8] ; add sp,sp,#16 ; ret`.
    const FRAME: [u8; 16] = [
        0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16
        0xe0, 0x0b, 0x00, 0xb9, // str w0, [sp, #8]
        0xff, 0x43, 0x00, 0x91, // add sp, sp, #16
        0xc0, 0x03, 0x5f, 0xd6, // ret
    ];

    #[test]
    fn decodes_a_stack_frame_and_its_access() {
        let m = decode_function("f", &FRAME);
        assert!(m.unanalyzed.is_empty(), "fully decoded: {:?}", m.unanalyzed);
        let insts = &m.functions[0].blocks[0].insts;
        assert!(matches!(insts[0], Inst::Alloc { region: RegionKind::Stack, .. }));
        assert!(matches!(insts[1], Inst::PtrOffset { .. }));
        assert!(matches!(insts[2], Inst::Store { .. }));
    }

    #[test]
    fn unsupported_instruction_is_unanalyzed() {
        // A NEON/FP word we do not decode.
        let m = decode_function("f", &[0x00, 0x00, 0x00, 0x00]);
        assert!(m.functions.is_empty());
        assert_eq!(m.unanalyzed.len(), 1);
    }

    #[test]
    fn rejects_misaligned_code() {
        let m = decode_function("f", &[0xc0, 0x03, 0x5f]); // 3 bytes
        assert_eq!(m.unanalyzed.len(), 1);
    }
}
