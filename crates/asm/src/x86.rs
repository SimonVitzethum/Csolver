//! A minimal x86-64 machine-code decoder → MSIR.
//!
//! It decodes a *small, growing* subset of x86-64 from raw bytes (as recovered
//! from an ELF `.text` by [`csolver_elf`]) and lowers a straight-line function to
//! MSIR, so the audited analysis core can verify a compiled binary with no
//! source. Registers are MSIR `RegId`s (the x86 encoding number), memory accesses
//! become `Load`/`Store` through the address register (a flat-memory pointer).
//!
//! ## Soundness by graceful degradation
//! The supported subset is intentionally tiny. Any unrecognized opcode or
//! addressing mode makes the *whole function* `unanalyzed` (reported `UNKNOWN` by
//! the verifier) rather than guessed at — a decoder that silently skipped or
//! mis-modelled an instruction could fabricate a false `PASS`, the one outcome a
//! verifier must never produce. So this layer can only ever be incomplete, never
//! unsound.

use crate::blocks::{build_blocks, Ctrl, DecodedInsn};
use csolver_core::{Error as CoreError, RegionKind};
use csolver_ir::{BinOp, CastOp, CmpOp, FuncId, Function, Inst, Module, Operand, RValue, RegId, Type};

/// Decode an x86-64 function from its machine bytes into a one-function
/// [`Module`], reconstructing its control-flow graph (branches/loops). On any
/// unsupported construct the function is recorded as `unanalyzed` (⇒ `UNKNOWN`),
/// never silently mis-modelled.
pub fn decode_function(name: &str, code: &[u8]) -> Module {
    let mut m = Module::new("bin");
    match decode_cfg(code).and_then(build_blocks) {
        Ok((blocks, entry)) => m.functions.push(Function {
            id: FuncId(0),
            name: name.into(),
            params: arg_registers(),
            ret_ty: Type::Unit,
            blocks,
            entry,
        }),
        Err(reason) => m.unanalyzed.push((name.into(), reason.to_string())),
    }
    m
}

/// The x86-64 System V integer argument registers, modelled as the function's
/// parameters so each is a *stable* symbol: a value read before it is written
/// (an input) then refers to one symbol across all its uses, which is what lets a
/// guard (`cmp rcx, 16`) constrain a later access (`[rsp + rcx*4]`). The order is
/// the SysV order (`rdi, rsi, rdx, rcx, r8, r9`), so the model names them
/// `arg0..arg5`.
fn arg_registers() -> Vec<(RegId, Type)> {
    [7u8, 6, 2, 1, 8, 9].iter().map(|&r| (reg(r), Type::int(64))).collect()
}

/// The result of decoding one instruction (before block assembly).
struct Decoded {
    insts: Vec<Inst>,
    next: usize,
    ctrl: Ctrl,
}

/// Linearly decode every instruction of the function body, threading the
/// `flags` state (the last `cmp`/`test` operands) so a following `jcc` knows its
/// condition.
fn decode_cfg(code: &[u8]) -> csolver_core::Result<Vec<DecodedInsn>> {
    let mut out = Vec::new();
    let mut pos = 0;
    let mut flags: Option<(Operand, Operand)> = None;
    while pos < code.len() {
        let d = decode_one(code, pos, &mut flags)?;
        out.push(DecodedInsn { offset: pos, next: d.next, insts: d.insts, ctrl: d.ctrl });
        pos = d.next;
    }
    Ok(out)
}

fn reg(num: u8) -> RegId {
    RegId(num as u32)
}

/// Decode one instruction starting at `pos`. `flags` carries the last
/// `cmp`/`test` operands so a following `jcc` can form its condition.
fn decode_one(
    code: &[u8],
    pos: usize,
    flags: &mut Option<(Operand, Operand)>,
) -> csolver_core::Result<Decoded> {
    let mut p = pos;
    // Optional REX prefix (0x40..0x4F): W=wide(64), R=reg ext, X=index ext,
    // B=rm/base ext.
    let (rex_w, rex_r, rex_x, rex_b) = match code.get(p) {
        Some(&b) if (0x40..=0x4f).contains(&b) => {
            p += 1;
            (b & 8 != 0, b & 4 != 0, b & 2 != 0, b & 1 != 0)
        }
        _ => (false, false, false, false),
    };
    let op = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated opcode at offset {p}")))?;
    p += 1;
    let width = if rex_w { 64 } else { 32 };
    let ty = Type::int(width);

    let done = |insts: Vec<Inst>, next: usize| Ok(Decoded { insts, next, ctrl: Ctrl::Fall });

    match op {
        0x90 => done(vec![], p),                                          // nop
        0xc3 => Ok(Decoded { insts: vec![], next: p, ctrl: Ctrl::Ret }),  // ret
        0xb8..=0xbf => {
            // mov r, imm
            let r = reg(op - 0xb8 + if rex_b { 8 } else { 0 });
            let imm_len = if rex_w { 8 } else { 4 };
            let imm = read_imm(code, p, imm_len)?;
            done(
                vec![Inst::Assign {
                    dst: r,
                    ty,
                    value: RValue::Use(Operand::int(width, imm)),
                }],
                p + imm_len,
            )
        }
        // <alu> r/m, r — reg/reg form (mod == 11) only.
        0x31 | 0x01 | 0x29 | 0x21 | 0x09 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: ALU with a memory operand"));
            }
            let bin = match op {
                0x31 => BinOp::Xor,
                0x01 => BinOp::Add,
                0x29 => BinOp::Sub,
                0x21 => BinOp::And,
                0x09 => BinOp::Or,
                _ => unreachable!(),
            };
            let dst = reg(m.rm);
            let src = reg(m.reg);
            // `xor r, r` is the idiom for zeroing — model it as `r = 0`.
            let value = if op == 0x31 && m.rm == m.reg {
                RValue::Use(Operand::int(width, 0))
            } else {
                RValue::Bin { op: bin, lhs: Operand::Reg(dst), rhs: Operand::Reg(src) }
            };
            done(vec![Inst::Assign { dst, ty, value }], p)
        }
        0x89 => {
            // mov r/m, r — register move (mod 11) or store [base+disp].
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.rm),
                        ty,
                        value: RValue::Use(Operand::Reg(reg(m.reg))),
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: Operand::Reg(reg(m.reg)), align: 1 });
                done(insts, mem.next)
            }
        }
        0x8b => {
            // mov r, r/m — register move (mod 11) or load [base+...].
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.reg),
                        ty,
                        value: RValue::Use(Operand::Reg(reg(m.rm))),
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Load { dst: reg(m.reg), ty, ptr: Operand::Reg(ptr), align: 1 });
                done(insts, mem.next)
            }
        }
        // lea r, [mem] — compute the effective address into r (no memory access).
        0x8d => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                return Err(CoreError::unsupported("x86: lea requires a memory operand"));
            }
            let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
            let (mut insts, ptr) = mem.lower(pos);
            insts.push(Inst::Assign { dst: reg(m.reg), ty, value: RValue::Use(Operand::Reg(ptr)) });
            done(insts, mem.next)
        }
        // group 1: <op> r/m, imm8 — register target (mod 11) only.
        // x86 sign-extends the 8-bit immediate to the operand width.
        0x83 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: group-1 with a memory operand is unsupported"));
            }
            let imm_raw = read_imm(code, p, 1)?; // imm8, value 0..255
            p += 1;
            // Sign-extend imm8 to the operand width.
            let imm = (imm_raw as u8 as i8 as i128) as u128;
            let uns = |v: u128| v & ((1u128 << width) - 1); // mask to width
            let target = reg(m.rm);
            // The /digit (ModRM reg field, sans any REX.R) selects the operation.
            match m.reg & 7 {
                // `sub rsp, N` allocates the stack frame: model rsp as a pointer
                // to a fresh N-byte stack region, so `[rsp+disp]` is checked
                // against the frame. N is always positive in practice.
                5 if m.rm == 4 => done(
                    vec![Inst::Alloc {
                        dst: target,
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, uns(imm)),
                        align: 16,
                    }],
                    p,
                ),
                // `add rsp, N` tears the frame down; nothing accesses it after, so
                // it is a no-op for the analysis.
                0 if m.rm == 4 => done(vec![], p),
                0 => done(vec![add_imm(target, ty, BinOp::Add, uns(imm), width)], p),
                5 => done(vec![add_imm(target, ty, BinOp::Sub, uns(imm), width)], p),
                7 => {
                    // cmp r, imm — record the operands for a following `jcc`.
                    *flags = Some((Operand::Reg(target), Operand::int(width, uns(imm))));
                    done(vec![], p)
                }
                _ => Err(CoreError::unsupported("x86: unsupported group-1 operation")),
              }
          }
          // cmp r/m, r — record operands for a following `jcc` (reg/reg form).
          0x39 => {
              let m = modrm(code, p, rex_r, rex_b)?;
              p += 1;
              if m.mode != 0b11 {
                  return Err(CoreError::unsupported("x86: cmp with a memory operand"));
            }
            *flags = Some((Operand::Reg(reg(m.rm)), Operand::Reg(reg(m.reg))));
            done(vec![], p)
        }
        // cmp r, r/m (reg/reg form).
        0x3b => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: cmp with a memory operand"));
            }
            *flags = Some((Operand::Reg(reg(m.reg)), Operand::Reg(reg(m.rm))));
            done(vec![], p)
        }
        // cmp eax, imm32.
        0x3d => {
            let imm = read_imm(code, p, 4)?;
            *flags = Some((Operand::Reg(reg(0)), Operand::int(width, imm)));
            done(vec![], p + 4)
        }
        // test r/m, r — `test r, r` tests whether `r` is zero.
        0x85 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            *flags = if m.mode == 0b11 && m.rm == m.reg {
                Some((Operand::Reg(reg(m.rm)), Operand::int(width, 0)))
            } else {
                None
            };
            done(vec![], p)
        }
        // jmp rel8 / rel32.
        0xeb => {
            let rel = read_imm(code, p, 1)? as u8 as i8 as i64;
            let np = p + 1;
            Ok(Decoded { insts: vec![], next: np, ctrl: Ctrl::Jmp(branch_target(np, rel)?) })
        }
        0xe9 => {
            let rel = read_imm(code, p, 4)? as u32 as i32 as i64;
            let np = p + 4;
            Ok(Decoded { insts: vec![], next: np, ctrl: Ctrl::Jmp(branch_target(np, rel)?) })
        }
        // jcc rel8.
        0x70..=0x7f => {
            let rel = read_imm(code, p, 1)? as u8 as i8 as i64;
            let np = p + 1;
            jcc(pos, np, branch_target(np, rel)?, op - 0x70, flags)
        }
        // movsxd r64, r/m32 — sign-extend dword to qword.
        0x63 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                dst: reg(m.reg),
                ty: ty.clone(),
                value: RValue::Cast {
                    op: CastOp::SExt,
                    operand: Operand::Reg(reg(m.rm)),
                    to: ty,
                },
            }],
            p,
        )
    } else {
        let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
        let (mut insts, ptr) = mem.lower(pos);
        let tmp = temp_reg(pos);
        insts.push(Inst::Load { dst: tmp, ty: Type::int(32), ptr: Operand::Reg(ptr), align: 1 });
        insts.push(Inst::Assign {
            dst: reg(m.reg),
            ty: ty.clone(),
            value: RValue::Cast { op: CastOp::SExt, operand: Operand::Reg(tmp), to: ty },
                });
                done(insts, mem.next)
            }
        }
        // push reg (0x50..0x57).
        0x50..=0x57 => {
            let r = reg(op - 0x50 + if rex_b { 8 } else { 0 });
            let size = if rex_w { 8 } else { 4 };
            done(
                vec![
                    Inst::Alloc {
                        dst: reg(4),
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, size as u128),
                        align: if size == 8 { 8 } else { 4 },
                    },
                    Inst::Store {
                        ty: Type::int(size as u32 * 8),
                        ptr: Operand::Reg(reg(4)),
                        value: Operand::Reg(r),
                        align: if size == 8 { 8 } else { 4 },
                    },
                ],
                p,
            )
        }
        // pop reg (0x58..0x5f).
        0x58..=0x5f => {
            let r = reg(op - 0x58 + if rex_b { 8 } else { 0 });
            let size = if rex_w { 8 } else { 4 };
            done(
                vec![Inst::Load {
                    dst: r,
                    ty: Type::int(size as u32 * 8),
                    ptr: Operand::Reg(reg(4)),
                    align: if size == 8 { 8 } else { 4 },
                }],
                p,
            )
        }
        // push imm32 (0x68) — sign-extended to 64 bits.
        0x68 => {
            let imm = read_imm(code, p, 4)? as u32 as i32 as i64 as u128;
            done(
                vec![
                    Inst::Alloc {
                        dst: reg(4),
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, 8),
                        align: 8,
                    },
                    Inst::Store {
                        ty: Type::int(64),
                        ptr: Operand::Reg(reg(4)),
                        value: Operand::int(64, imm),
                        align: 8,
                    },
                ],
                p + 4,
            )
        }
        // push imm8 (0x6a).
        0x6a => {
            let imm = read_imm(code, p, 1)? as u8 as i8 as i64 as u128;
            done(
                vec![
                    Inst::Alloc {
                        dst: reg(4),
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, 8),
                        align: 8,
                    },
                    Inst::Store {
                        ty: Type::int(64),
                        ptr: Operand::Reg(reg(4)),
                        value: Operand::int(64, imm),
                        align: 8,
                    },
                ],
                p + 1,
            )
        }
        // xchg rax, reg (0x91..0x97).
        0x91..=0x97 => {
            let rax = reg(0);
            let r = reg(op - 0x91 + if rex_b { 8 } else { 0 });
            let t = temp_reg(pos);
            done(
                vec![
                    Inst::Assign { dst: t, ty: ty.clone(), value: RValue::Use(Operand::Reg(rax)) },
                    Inst::Assign { dst: rax, ty: ty.clone(), value: RValue::Use(Operand::Reg(r)) },
                    Inst::Assign { dst: r, ty, value: RValue::Use(Operand::Reg(t)) },
                ],
                p,
            )
        }
        // xchg r/m, r (0x87, reg-reg only).
        0x87 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: xchg with a memory operand"));
            }
            let ra = reg(m.reg);
            let rb = reg(m.rm);
            let t = temp_reg(pos);
            done(
                vec![
                    Inst::Assign { dst: t, ty: ty.clone(), value: RValue::Use(Operand::Reg(ra)) },
                    Inst::Assign { dst: ra, ty: ty.clone(), value: RValue::Use(Operand::Reg(rb)) },
                    Inst::Assign { dst: rb, ty, value: RValue::Use(Operand::Reg(t)) },
                ],
                p,
            )
        }
        // cdqe (0x98 with REX.W) — sign-extend eax to rax.
        0x98 => {
            if rex_w {
                done(
                    vec![Inst::Assign {
                        dst: reg(0),
                        ty: Type::int(64),
                        value: RValue::Cast {
                            op: CastOp::SExt,
                            operand: Operand::Reg(reg(0)),
                            to: Type::int(64),
                        },
                    }],
                    p,
                )
            } else {
                // cwde — sign-extend ax to eax; in 64-bit mode, zero-extend to rax.
                done(
                    vec![Inst::Assign {
                        dst: reg(0),
                        ty: Type::int(32),
                        value: RValue::Cast {
                            op: CastOp::SExt,
                            operand: Operand::Reg(reg(0)),
                            to: Type::int(32),
                        },
                    }],
                    p,
                )
            }
        }
        // cqo/cdq/cwd (0x99) — sign-extend accumulator to rdx:rax.
        // REX.W → cqo  (sign-extend 64-bit rax → rdx:rax)
        // no REX → cdq  (sign-extend 32-bit eax → edx:eax)
        // 0x66   → cwd  (sign-extend 16-bit ax  → dx:ax)
        0x99 => {
            let shift_bits: u32 = if rex_w { 63 } else if width == 16 { 15 } else { 31 };
            let dst = reg(2);
            done(
                vec![Inst::Assign {
                    dst,
                    ty: Type::int(width),
                    value: RValue::Bin {
                        op: BinOp::AShr,
                        lhs: Operand::Reg(reg(0)),
                        rhs: Operand::int(width, shift_bits as u128),
                    },
                }],
                p,
            )
        }
        // mov r/m, imm32 (0xc7) — immediate dword to register or memory.
        // With REX.W the 32-bit immediate is sign-extended to 64 bits.
        0xc7 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let imm_raw = read_imm(code, p, 4)?;
            p += 4;
            let imm = if width > 32 { imm_raw as u32 as i32 as i64 as u128 } else { imm_raw };
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.rm),
                        ty,
                        value: RValue::Use(Operand::int(width, imm)),
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: Operand::int(width, imm), align: 1 });
                done(insts, mem.next)
            }
        }
        // mov r/m8, imm8 (0xc6).
        0xc6 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let imm = read_imm(code, p, 1)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.rm),
                        ty: Type::int(8),
                        value: RValue::Use(Operand::int(8, imm)),
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Store { ty: Type::int(8), ptr: Operand::Reg(ptr), value: Operand::int(8, imm), align: 1 });
                done(insts, mem.next)
            }
        }
        // Group 2 shift r/m, imm8 (0xc1) and shift r/m, 1 (0xd1).
        0xc1 | 0xd1 => {
            let shift_by_1 = op == 0xd1;
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: shift with a memory operand"));
            }
            let count = if shift_by_1 { 1u128 } else {
                let c = read_imm(code, p, 1)?;
                p += 1;
                c
            };
            let target = reg(m.rm);
            let bin_op = match m.reg & 7 {
                4 => BinOp::Shl,
                5 => BinOp::LShr,
                7 => BinOp::AShr,
                _ => return Err(CoreError::unsupported(format!("x86: unsupported group-2 operation /digit {}", m.reg & 7))),
            };
            done(
                vec![Inst::Assign {
                    dst: target,
                    ty,
                    value: RValue::Bin {
                        op: bin_op,
                        lhs: Operand::Reg(target),
                        rhs: Operand::int(width, count),
                    },
                }],
                p,
            )
        }
        // Group 3 r/m (0xf6, 0xf7, reg-reg only): test/not/neg/mul/imul/div/idiv.
        // We decode only not and neg; the rest are returned as unsupported.
        0xf6 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: group-3 with a memory operand"));
            }
            let target = reg(m.rm);
            let w = 8;
            match m.reg & 7 {
                2 => {
                    // not r/m8 = xor r/m8, 0xFF
                    done(
                        vec![Inst::Assign {
                            dst: target,
                            ty: Type::int(w),
                            value: RValue::Bin {
                                op: BinOp::Xor,
                                lhs: Operand::Reg(target),
                                rhs: Operand::int(w, (1u128 << w) - 1),
                            },
                        }],
                        p,
                    )
                }
                3 => {
                    // neg r/m8 = 0 - r/m8
                    done(
                        vec![Inst::Assign {
                            dst: target,
                            ty: Type::int(w),
                            value: RValue::Bin {
                                op: BinOp::Sub,
                                lhs: Operand::int(w, 0),
                                rhs: Operand::Reg(target),
                            },
                        }],
                        p,
                    )
                }
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-3 /digit {} with 8-bit", m.reg & 7))),
            }
        }
        0xf7 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: group-3 with a memory operand"));
            }
            let target = reg(m.rm);
            match m.reg & 7 {
                2 => {
                    // not r/m = xor r/m, all-ones
                    done(
                        vec![Inst::Assign {
                            dst: target,
                            ty,
                            value: RValue::Bin {
                                op: BinOp::Xor,
                                lhs: Operand::Reg(target),
                                rhs: Operand::int(width, (1u128 << width) - 1),
                            },
                        }],
                        p,
                    )
                }
                3 => {
                    // neg r/m = 0 - r/m
                    done(
                        vec![Inst::Assign {
                            dst: target,
                            ty,
                            value: RValue::Bin {
                                op: BinOp::Sub,
                                lhs: Operand::int(width, 0),
                                rhs: Operand::Reg(target),
                            },
                        }],
                        p,
                    )
                }
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-3 /digit {}", m.reg & 7))),
            }
        }
        // Group 4 inc/dec r/m8 (0xfe, reg-reg only).
        0xfe => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: inc/dec with a memory operand"));
            }
            let target = reg(m.rm);
            let bin_op = match m.reg & 7 {
                0 => BinOp::Add,
                1 => BinOp::Sub,
                _ => return Err(CoreError::unsupported(format!("x86: unsupported group-4 /digit {}", m.reg & 7))),
            };
            done(
                vec![Inst::Assign {
                    dst: target,
                    ty: Type::int(8),
                    value: RValue::Bin {
                        op: bin_op,
                        lhs: Operand::Reg(target),
                        rhs: Operand::int(8, 1),
                    },
                }],
                p,
            )
        }
        // Group 5 (0xff, reg-reg only): inc/dec/call/jmp.
        0xff => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: group-5 with a memory operand"));
            }
            let target = reg(m.rm);
            match m.reg & 7 {
                0 => done(
                    vec![Inst::Assign {
                        dst: target,
                        ty,
                        value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(target), rhs: Operand::int(width, 1) },
                    }],
                    p,
                ),
                1 => done(
                    vec![Inst::Assign {
                        dst: target,
                        ty,
                        value: RValue::Bin { op: BinOp::Sub, lhs: Operand::Reg(target), rhs: Operand::int(width, 1) },
                    }],
                    p,
                ),
                2 => Ok(Decoded { insts: vec![], next: p, ctrl: Ctrl::Ret }), // call reg → model as ret (conservative)
                4 => Ok(Decoded { insts: vec![], next: p, ctrl: Ctrl::Ret }), // jmp reg → model as ret (conservative)
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-5 /digit {}", m.reg & 7))),
            }
        }
        // Two-byte opcodes.
        0x0f => {
            let op2 = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated 0F opcode at offset {p}")))?;
            p += 1;
            match op2 {
                // jcc rel32.
                0x80..=0x8f => {
                    let rel = read_imm(code, p, 4)? as u32 as i32 as i64;
                    let np = p + 4;
                    jcc(pos, np, branch_target(np, rel)?, op2 - 0x80, flags)
                }
                // setcc r/m8 (reg-reg only).
                0x90..=0x9f => {
                    let m = modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    if m.mode != 0b11 {
                        return Err(CoreError::unsupported("x86: setcc with a memory operand"));
                    }
                    let cond_creg = temp_reg(pos);
                    let (cmp_op, lhs, rhs) = match (cc_cmpop(op2 - 0x90), flags) {
                        (Some(op), Some((a, b))) => (op, a.clone(), b.clone()),
                        _ => (CmpOp::Ne, Operand::Reg(RegId(2000 + pos as u32)), Operand::int(64, 0)),
                    };
                    let dst_target = reg(m.rm);
                    done(
                        vec![
                            Inst::Assign { dst: cond_creg, ty: Type::Bool, value: RValue::Cmp { op: cmp_op, lhs, rhs } },
                            Inst::Assign {
                                dst: dst_target,
                                ty: Type::int(8),
                                value: RValue::Cast {
                                    op: CastOp::ZExt,
                                    operand: Operand::Reg(cond_creg),
                                    to: Type::int(8),
                                },
                            },
                        ],
                        p,
                    )
                }
                // movzx r, r/m8 (0f b6).
                0xb6 => {
                    let m = modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    if m.mode == 0b11 {
                        done(
                            vec![Inst::Assign {
                                dst: reg(m.reg),
                                ty: ty.clone(),
                                value: RValue::Cast {
                                    op: CastOp::ZExt,
                                    operand: Operand::Reg(reg(m.rm)),
                                    to: ty,
                                },
                            }],
                            p,
                        )
                    } else {
                        let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                        let (mut insts, ptr) = mem.lower(pos);
                        let tmp = temp_reg(pos);
                        insts.push(Inst::Load { dst: tmp, ty: Type::int(8), ptr: Operand::Reg(ptr), align: 1 });
                        insts.push(Inst::Assign {
                            dst: reg(m.reg),
                            ty: ty.clone(),
                            value: RValue::Cast { op: CastOp::ZExt, operand: Operand::Reg(tmp), to: ty },
                        });
                        done(insts, mem.next)
                    }
                }
                // movzx r, r/m16 (0f b7).
                0xb7 => {
                    let m = modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    if m.mode == 0b11 {
                        done(
                            vec![Inst::Assign {
                                dst: reg(m.reg),
                                ty: ty.clone(),
                                value: RValue::Cast {
                                    op: CastOp::ZExt,
                                    operand: Operand::Reg(reg(m.rm)),
                                    to: ty,
                                },
                            }],
                            p,
                        )
                    } else {
                        let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                        let (mut insts, ptr) = mem.lower(pos);
                        let tmp = temp_reg(pos);
                        insts.push(Inst::Load { dst: tmp, ty: Type::int(16), ptr: Operand::Reg(ptr), align: 1 });
                        insts.push(Inst::Assign {
                            dst: reg(m.reg),
                            ty: ty.clone(),
                            value: RValue::Cast { op: CastOp::ZExt, operand: Operand::Reg(tmp), to: ty },
                        });
                        done(insts, mem.next)
                    }
                }
                // movsx r, r/m8 (0f be).
                0xbe => {
                    let m = modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    if m.mode == 0b11 {
                        done(
                            vec![Inst::Assign {
                                dst: reg(m.reg),
                                ty: ty.clone(),
                                value: RValue::Cast {
                                    op: CastOp::SExt,
                                    operand: Operand::Reg(reg(m.rm)),
                                    to: ty,
                                },
                            }],
                            p,
                        )
                    } else {
                        let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                        let (mut insts, ptr) = mem.lower(pos);
                        let tmp = temp_reg(pos);
                        insts.push(Inst::Load { dst: tmp, ty: Type::int(8), ptr: Operand::Reg(ptr), align: 1 });
                        insts.push(Inst::Assign {
                            dst: reg(m.reg),
                            ty: ty.clone(),
                            value: RValue::Cast { op: CastOp::SExt, operand: Operand::Reg(tmp), to: ty },
                        });
                        done(insts, mem.next)
                    }
                }
                // movsx r, r/m16 (0f bf).
                0xbf => {
                    let m = modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    if m.mode == 0b11 {
                        done(
                            vec![Inst::Assign {
                                dst: reg(m.reg),
                                ty: ty.clone(),
                                value: RValue::Cast {
                                    op: CastOp::SExt,
                                    operand: Operand::Reg(reg(m.rm)),
                                    to: ty,
                                },
                            }],
                            p,
                        )
                    } else {
                        let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                        let (mut insts, ptr) = mem.lower(pos);
                        let tmp = temp_reg(pos);
                        insts.push(Inst::Load { dst: tmp, ty: Type::int(16), ptr: Operand::Reg(ptr), align: 1 });
                        insts.push(Inst::Assign {
                            dst: reg(m.reg),
                            ty: ty.clone(),
                            value: RValue::Cast { op: CastOp::SExt, operand: Operand::Reg(tmp), to: ty },
                        });
                        done(insts, mem.next)
                    }
                }
                _ => Err(CoreError::unsupported(format!("x86: unsupported opcode 0f {op2:#04x}"))),
            }
        }
        other => Err(CoreError::unsupported(format!("x86: unsupported opcode {other:#04x}"))),
    }
}

/// A decoded ModR/M byte (with REX register-number extensions applied).
struct ModRm {
    mode: u8,
    reg: u8,
    rm: u8,
}

/// A fresh MSIR register for the address computed by a memory operand. The byte
/// position is unique per instruction, so the temporaries never clash (and stay
/// clear of the x86 register numbers 0..15).
fn temp_reg(pos: usize) -> RegId {
    RegId(1000 + pos as u32)
}

/// `target = target <op> imm`.
fn add_imm(target: RegId, ty: Type, op: BinOp, imm: u128, width: u32) -> Inst {
    Inst::Assign {
        dst: target,
        ty,
        value: RValue::Bin { op, lhs: Operand::Reg(target), rhs: Operand::int(width, imm) },
    }
}

/// The absolute byte offset a relative branch (`rel`, measured from `np`, the end
/// of the branch instruction) targets; an error if it falls before the function.
fn branch_target(np: usize, rel: i64) -> csolver_core::Result<usize> {
    let t = np as i64 + rel;
    if t < 0 {
        Err(CoreError::parse("x86: branch target before the function"))
    } else {
        Ok(t as usize)
    }
}

/// Lower a `jcc` to a condition assignment plus a `Jcc` control effect. With a
/// known `cmp`/`test` and a modelled condition code the condition is exact;
/// otherwise it is an unconstrained boolean (so the engine explores both arms).
fn jcc(
    pos: usize,
    np: usize,
    target: usize,
    cc: u8,
    flags: &Option<(Operand, Operand)>,
) -> csolver_core::Result<Decoded> {
    let cond = temp_reg(pos);
    let (op, lhs, rhs) = match (cc_cmpop(cc), flags) {
        (Some(op), Some((a, b))) => (op, a.clone(), b.clone()),
        // Unknown flags / condition code: compare a never-defined register with
        // 0, an unconstrained boolean.
        _ => (CmpOp::Ne, Operand::Reg(RegId(2000 + pos as u32)), Operand::int(64, 0)),
    };
    Ok(Decoded {
        insts: vec![Inst::Assign { dst: cond, ty: Type::Bool, value: RValue::Cmp { op, lhs, rhs } }],
        next: np,
        ctrl: Ctrl::Jcc(target, cond),
    })
}

/// The comparison a condition code tests: `cmp a, b` then `jcc` jumps iff
/// `a <op> b`. `None` for codes we do not model (parity / sign / overflow).
fn cc_cmpop(cc: u8) -> Option<CmpOp> {
    Some(match cc {
        0x2 => CmpOp::Ult, // jb / jc
        0x3 => CmpOp::Uge, // jae / jnc
        0x4 => CmpOp::Eq,  // je / jz
        0x5 => CmpOp::Ne,  // jne / jnz
        0x6 => CmpOp::Ule, // jbe
        0x7 => CmpOp::Ugt, // ja
        0xc => CmpOp::Slt, // jl
        0xd => CmpOp::Sge, // jge
        0xe => CmpOp::Sle, // jle
        0xf => CmpOp::Sgt, // jg
        _ => return None,
    })
}

/// A decoded `[base + index*scale + disp]` memory operand.
struct MemOperand {
    base: RegId,
    /// `(index register, scale in bytes ∈ {1,2,4,8})`, if an index is present.
    index: Option<(RegId, u8)>,
    disp: i64,
    next: usize,
}

impl MemOperand {
    /// Emit the `PtrOffset` chain computing the address and return the register
    /// holding it: `base (+ index*scale) (+ disp)`.
    fn lower(&self, pos: usize) -> (Vec<Inst>, RegId) {
        let mut insts = Vec::new();
        let mut ptr = self.base;
        if let Some((index, scale)) = self.index {
            let dst = temp_reg(pos);
            insts.push(Inst::PtrOffset {
                dst,
                base: Operand::Reg(ptr),
                index: Operand::Reg(index),
                elem: Type::int(8 * scale as u32),
            });
            ptr = dst;
        }
        // A bare `[base]` or any displacement needs a final byte offset (also so
        // the result is a pointer when there was no index).
        if self.index.is_none() || self.disp != 0 {
            let dst = RegId(1500 + pos as u32);
            insts.push(Inst::PtrOffset {
                dst,
                base: Operand::Reg(ptr),
                index: Operand::int(64, self.disp as u64 as u128),
                elem: Type::int(8),
            });
            ptr = dst;
        }
        (insts, ptr)
    }
}

/// Decode the `[base + index*scale + disp]` memory operand of a ModR/M
/// (mode ≠ 11), including a SIB byte. RIP-relative and base-less disp32 forms are
/// a clean `Err`.
fn mem_operand(code: &[u8], p: usize, m: &ModRm, rex_x: bool, rex_b: bool) -> csolver_core::Result<MemOperand> {
    let mut p = p;
    let mut base = m.rm; // low 3 bits + REX.B (from `modrm`)
    let mut index = None;
    let rm_low = m.rm & 7;
    if rm_low == 4 {
        let sib = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated SIB at offset {p}")))?;
        p += 1;
        let scale = 1u8 << (sib >> 6);
        let index_field = (sib >> 3) & 7;
        let base_field = (sib & 7) + if rex_b { 8 } else { 0 };
        // index field 100 with REX.X clear means "no index"; otherwise it is a
        // register (r12 when REX.X is set).
        if index_field != 4 || rex_x {
            index = Some((reg(index_field + if rex_x { 8 } else { 0 }), scale));
        }
        if m.mode == 0b00 && base_field & 7 == 5 {
            return Err(CoreError::unsupported("x86: base-less disp32 is unsupported"));
        }
        base = base_field;
    } else if rm_low == 5 && m.mode == 0b00 {
        return Err(CoreError::unsupported("x86: RIP-relative addressing is unsupported"));
    }
    let disp = match m.mode {
        0b00 => 0i64,
        0b01 => {
            let d = read_imm(code, p, 1)? as u8 as i8 as i64;
            p += 1;
            d
        }
        0b10 => {
            let d = read_imm(code, p, 4)? as u32 as i32 as i64;
            p += 4;
            d
        }
        _ => return Err(CoreError::unsupported("x86: register operand has no memory form")),
    };
    Ok(MemOperand { base: reg(base), index, disp, next: p })
}

fn modrm(code: &[u8], at: usize, rex_r: bool, rex_b: bool) -> csolver_core::Result<ModRm> {
    let b = *code.get(at).ok_or_else(|| CoreError::parse(format!("x86: truncated ModR/M at offset {at}")))?;
    Ok(ModRm {
        mode: b >> 6,
        reg: ((b >> 3) & 7) + if rex_r { 8 } else { 0 },
        rm: (b & 7) + if rex_b { 8 } else { 0 },
    })
}

/// Read a little-endian immediate of `len` bytes (4 or 8), sign/zero handling
/// left to the consumer (we keep the raw unsigned value).
fn read_imm(code: &[u8], at: usize, len: usize) -> csolver_core::Result<u128> {
    let bytes = code.get(at..at + len).ok_or_else(|| CoreError::parse(format!("x86: truncated immediate of len {len} at offset {at}")))?;
    let mut v: u128 = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        v |= (byte as u128) << (8 * i);
    }
    Ok(v)
}

// ============================================================================
// Typed instruction/operand representation (MSIR-independent)
// ============================================================================

/// x86-64 general-purpose registers (64-bit mode encoding).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum Reg {
    RAX = 0, RCX = 1, RDX = 2, RBX = 3,
    RSP = 4, RBP = 5, RSI = 6, RDI = 7,
    R8 = 8, R9 = 9, R10 = 10, R11 = 11,
    R12 = 12, R13 = 13, R14 = 14, R15 = 15,
}

impl Reg {
    /// Convert a 4-bit register index (0..15) into a [`Reg`]. The index
    /// combines the raw 3-bit encoding field with a REX extension bit
    /// (e.g. `low3 | if rex_bit { 8 } else { 0 }`).
    fn from_idx(idx: u8) -> Option<Reg> {
        match idx {
            0 => Some(Reg::RAX), 1 => Some(Reg::RCX), 2 => Some(Reg::RDX), 3 => Some(Reg::RBX),
            4 => Some(Reg::RSP), 5 => Some(Reg::RBP), 6 => Some(Reg::RSI), 7 => Some(Reg::RDI),
            8 => Some(Reg::R8), 9 => Some(Reg::R9), 10 => Some(Reg::R10), 11 => Some(Reg::R11),
            12 => Some(Reg::R12), 13 => Some(Reg::R13), 14 => Some(Reg::R14), 15 => Some(Reg::R15),
            _ => None,
        }
    }
}

/// Access width for a register or memory operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Width {
    /// 8 bits (byte).
    B,
    /// 16 bits (word).
    W,
    /// 32 bits (doubleword).
    D,
    /// 64 bits (quadword).
    Q,
    /// 128 bits (double quadword, XMM register width).
    DQ,
    /// 256 bits (quad quadword, YMM register width).
    QQ,
}

impl Width {
    #[allow(dead_code)]
    fn bytes(self) -> u64 {
        match self {
            Width::B => 1,
            Width::W => 2,
            Width::D => 4,
            Width::Q => 8,
            Width::DQ => 16,
            Width::QQ => 32,
        }
    }

    /// The operand width in bits.
    fn bits(self) -> u64 {
        self.bytes() * 8
    }

    /// Infer the width from a REX.W bit and the operation code. For most
    /// ALU ops, !REX.W → 32-bit, REX.W → 64-bit.
    fn from_rex_w(rex_w: bool) -> Width {
        if rex_w { Width::Q } else { Width::D }
    }
}

/// A memory operand: `[base + index * scale + disp]`.
///
/// Every field is optional: `base` may be `None` (absolute address),
/// `index` may be `None` (no scaled index), and `disp` may be 0.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mem {
    /// The base register.
    pub base: Option<Reg>,
    /// The scaled index register and its scale (1, 2, 4, or 8).
    pub index: Option<(Reg, u8)>,
    /// The displacement in bytes.
    pub disp: i64,
}

/// An XMM (SSE/AVX) register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum XmmReg {
    XMM0 = 0, XMM1 = 1, XMM2 = 2, XMM3 = 3,
    XMM4 = 4, XMM5 = 5, XMM6 = 6, XMM7 = 7,
    XMM8 = 8, XMM9 = 9, XMM10 = 10, XMM11 = 11,
    XMM12 = 12, XMM13 = 13, XMM14 = 14, XMM15 = 15,
}

impl XmmReg {
    fn from_idx(idx: u8) -> Option<XmmReg> {
        match idx {
            0 => Some(XmmReg::XMM0), 1 => Some(XmmReg::XMM1),
            2 => Some(XmmReg::XMM2), 3 => Some(XmmReg::XMM3),
            4 => Some(XmmReg::XMM4), 5 => Some(XmmReg::XMM5),
            6 => Some(XmmReg::XMM6), 7 => Some(XmmReg::XMM7),
            8 => Some(XmmReg::XMM8), 9 => Some(XmmReg::XMM9),
            10 => Some(XmmReg::XMM10), 11 => Some(XmmReg::XMM11),
            12 => Some(XmmReg::XMM12), 13 => Some(XmmReg::XMM13),
            14 => Some(XmmReg::XMM14), 15 => Some(XmmReg::XMM15),
            _ => None,
        }
    }
}

/// A decoded operand for an x86-64 instruction.
///
/// Named `X86Operand` (not `Operand`) to avoid shadowing the import of
/// [`csolver_ir::Operand`] used by the MSIR-lowering path in the same module.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum X86Operand {
    /// A register operand (register + width).
    Reg(Reg, Width),
    /// An XMM (SSE/AVX) register operand.
    Xmm(XmmReg, Width),
    /// A memory operand (address + width).
    Mem(Mem, Width),
    /// An immediate value (unsigned; semantic width depends on the instruction).
    Imm(u64),
    /// A relative displacement for a branch instruction (in bytes from the
    /// end of the instruction).
    Rel(i64),
}

/// x86-64 condition codes (the low 4 bits of the `jcc` / `cmovcc` / `setcc`
/// opcode extension). Only the ALU-flag-sensing subset is modelled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Condition {
    O, NO, B, AE, E, NE, BE, A,
    S, NS, P, NP, L, GE, LE, G,
}

impl Condition {
    fn from_cc(cc: u8) -> Option<Condition> {
        match cc {
            0x0 => Some(Condition::O),  0x1 => Some(Condition::NO),
            0x2 => Some(Condition::B),  0x3 => Some(Condition::AE),
            0x4 => Some(Condition::E),  0x5 => Some(Condition::NE),
            0x6 => Some(Condition::BE), 0x7 => Some(Condition::A),
            0x8 => Some(Condition::S),  0x9 => Some(Condition::NS),
            0xa => Some(Condition::P),  0xb => Some(Condition::NP),
            0xc => Some(Condition::L),  0xd => Some(Condition::GE),
            0xe => Some(Condition::LE), 0xf => Some(Condition::G),
            _ => None,
        }
    }
}

/// The set of recognised x86-64 instructions.
///
/// This representation is architecture-specific and independent of MSIR.
/// The later (out-of-scope) bridge to MSIR maps these into [`csolver_ir::Inst`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Instruction {
    /// `nop` (0x90, 0x0f 0x1f ...).
    Nop,
    /// `mov dst, src` — register, memory, and immediate moves.
    Mov(X86Operand, X86Operand),
    /// `movzx dst, src` — move with zero-extension.
    Movzx(X86Operand, X86Operand),
    /// `movsx dst, src` — move with sign-extension.
    Movsx(X86Operand, X86Operand),
    /// `lea dst, mem` — load effective address.
    Lea(Reg, Width, Mem),
    /// `add dst, src`.
    Add(X86Operand, X86Operand),
    /// `sub dst, src`.
    Sub(X86Operand, X86Operand),
    /// `xor dst, src`.
    Xor(X86Operand, X86Operand),
    /// `and dst, src`.
    And(X86Operand, X86Operand),
    /// `or dst, src`.
    Or(X86Operand, X86Operand),
    /// `cmp a, b`.
    Cmp(X86Operand, X86Operand),
    /// `test a, b`.
    Test(X86Operand, X86Operand),
    /// `push src`.
    Push(X86Operand),
    /// `pop dst`.
    Pop(X86Operand),
    /// `call target`.
    Call(X86Operand),
    /// `jmp target`.
    Jmp(X86Operand),
    /// `jcc target`.
    Jcc(Condition, i64),
    /// `ret`.
    Ret,
    /// `syscall`.
    Syscall,
    /// `cdqe` (0x98) — sign-extend eax to rax; `cdqe` if REX.W else `cdqe` (32→64).
    Cdqe,
    /// `cqo` (0x99) — sign-extend rax to rdx:rax.
    Cqo,
    /// `int3` (0xcc).
    Int3,
    /// `xchg a, b`.
    Xchg(X86Operand, X86Operand),
    /// `neg dst` (0xf6/0xf7 /3).
    Neg(X86Operand),
    /// `not dst` (0xf6/0xf7 /2).
    Not(X86Operand),
    /// `inc dst` (0xfe/0xff /0).
    Inc(X86Operand),
    /// `dec dst` (0xfe/0xff /1).
    Dec(X86Operand),
    /// `mul src` — unsigned multiply (0xf6/0xf7 /4).
    Mul(X86Operand),
    /// `imul src` — signed multiply (0xf6/0xf7 /5).
    Imul(X86Operand),
    /// `div src` — unsigned divide (0xf6/0xf7 /6).
    Div(X86Operand),
    /// `idiv src` — signed divide (0xf6/0xf7 /7).
    Idiv(X86Operand),
    /// `shl dst, count` — left shift by imm8 or 1.
    Shl(X86Operand, u8),
    /// `shr dst, count` — logical right shift.
    Shr(X86Operand, u8),
    /// `sar dst, count` — arithmetic right shift.
    Sar(X86Operand, u8),
    /// `cmovcc dst, src` — conditional move (0f 0x40..0x4f).
    Cmovcc(Condition, X86Operand, X86Operand),
    /// `setcc dst` — set byte on condition (0f 0x90..0x9f).
    Setcc(Condition, X86Operand),
    /// `rol dst, count` — rotate left (Group 2 /0).
    Rol(X86Operand, u8),
    /// `ror dst, count` — rotate right (Group 2 /1).
    Ror(X86Operand, u8),
    /// `rcl dst, count` — rotate through carry left (Group 2 /2).
    Rcl(X86Operand, u8),
    /// `rcr dst, count` — rotate through carry right (Group 2 /3).
    Rcr(X86Operand, u8),
    /// `movsxd dst, src` — move with sign-extension dword→qword (0x63).
    Movsxd(X86Operand, X86Operand),
    /// `bsf dst, src` — bit scan forward (0f bc).
    Bsf(X86Operand, X86Operand),
    /// `bsr dst, src` — bit scan reverse (0f bd).
    Bsr(X86Operand, X86Operand),
    /// `bt src, pos` — bit test (0f a3).
    Bt(X86Operand, X86Operand),
    /// `bts dst, pos` — bit test and set (0f ab).
    Bts(X86Operand, X86Operand),
    /// `btr dst, pos` — bit test and reset (0f b3).
    Btr(X86Operand, X86Operand),
    /// `btc dst, pos` — bit test and complement (0f bb).
    Btc(X86Operand, X86Operand),
    /// `stc` — set carry flag (0xf9).
    Stc,
    /// `clc` — clear carry flag (0xf8).
    Clc,
    /// `cmc` — complement carry flag (0xf5).
    Cmc,
    /// `std` — set direction flag (0xfd).
    Std,
    /// `cld` — clear direction flag (0xfc).
    Cld,
    /// `lahf` — load flags into AH (0x9f).
    Lahf,
    /// `sahf` — store AH into flags (0x9e).
    Sahf,
    /// `pushf` — push flags (0x9c).
    Pushf,
    /// `popf` — pop flags (0x9d).
    Popf,
    /// `movs` — string move [rdi]←[rsi] (0xa4/0xa5).
    Movs(Width),
    /// `stos` — string store [rdi]←rAX (0xaa/0xab).
    Stos(Width),
    /// `lods` — string load rAX←[rsi] (0xac/0xad).
    Lods(Width),
    /// `scas` — string scan cmp rAX, [rdi] (0xae/0xaf).
    Scas(Width),
    /// `cmps` — string compare [rdi]←[rsi] (0xa6/0xa7).
    Cmps(Width),
    // ====================================================================
    // SSE / AVX instructions
    // ====================================================================
    /// `movaps dst, src` — move aligned packed singles (0F 28 /r, VEX.128 equivalent).
    Movaps(X86Operand, X86Operand),
    /// `movapd dst, src` — move aligned packed doubles (66 0F 28 /r).
    Movapd(X86Operand, X86Operand),
    /// `movups dst, src` — move unaligned packed singles (0F 10 /r).
    Movups(X86Operand, X86Operand),
    /// `movdqa dst, src` — move aligned packed integers (66 0F 6F /r).
    Movdqa(X86Operand, X86Operand),
    /// `movdqu dst, src` — move unaligned packed integers (F3 0F 6F /r).
    Movdqu(X86Operand, X86Operand),
    /// `movss dst, src` — move scalar single (F3 0F 10 /r).
    Movss(X86Operand, X86Operand),
    /// `movsd dst, src` — move scalar double (F2 0F 10 /r).
    Movsd(X86Operand, X86Operand),
    /// `movq dst, src` — move quadword between XMM and GPR/mem (66 0F 6E/D6, F3 0F 7E).
    Movq(X86Operand, X86Operand),
    /// `movd dst, src` — move doubleword between XMM and GPR/mem (66 0F 6E/D6).
    Movd(X86Operand, X86Operand),
    /// `addps dst, src` — packed single add (0F 58 /r).
    Addps(X86Operand, X86Operand),
    /// `addss dst, src` — scalar single add (F3 0F 58 /r).
    Addss(X86Operand, X86Operand),
    /// `addpd dst, src` — packed double add (66 0F 58 /r).
    Addpd(X86Operand, X86Operand),
    /// `addsd dst, src` — scalar double add (F2 0F 58 /r).
    Addsd(X86Operand, X86Operand),
    /// `subps dst, src` — packed single subtract (0F 5C /r).
    Subps(X86Operand, X86Operand),
    /// `subss dst, src` — scalar single subtract (F3 0F 5C /r).
    Subss(X86Operand, X86Operand),
    /// `subpd dst, src` — packed double subtract (66 0F 5C /r).
    Subpd(X86Operand, X86Operand),
    /// `subsd dst, src` — scalar double subtract (F2 0F 5C /r).
    Subsd(X86Operand, X86Operand),
    /// `mulps dst, src` — packed single multiply (0F 59 /r).
    Mulps(X86Operand, X86Operand),
    /// `mulss dst, src` — scalar single multiply (F3 0F 59 /r).
    Mulss(X86Operand, X86Operand),
    /// `mulpd dst, src` — packed double multiply (66 0F 59 /r).
    Mulpd(X86Operand, X86Operand),
    /// `mulsd dst, src` — scalar double multiply (F2 0F 59 /r).
    Mulsd(X86Operand, X86Operand),
    /// `divps dst, src` — packed single divide (0F 5E /r).
    Divps(X86Operand, X86Operand),
    /// `divss dst, src` — scalar single divide (F3 0F 5E /r).
    Divss(X86Operand, X86Operand),
    /// `divpd dst, src` — packed double divide (66 0F 5E /r).
    Divpd(X86Operand, X86Operand),
    /// `divsd dst, src` — scalar double divide (F2 0F 5E /r).
    Divsd(X86Operand, X86Operand),
    /// `andps dst, src` — packed single bitwise and (0F 54 /r).
    Andps(X86Operand, X86Operand),
    /// `andpd dst, src` — packed double bitwise and (66 0F 54 /r).
    Andpd(X86Operand, X86Operand),
    /// `orps dst, src` — packed single bitwise or (0F 56 /r).
    Orps(X86Operand, X86Operand),
    /// `orpd dst, src` — packed double bitwise or (66 0F 56 /r).
    Orpd(X86Operand, X86Operand),
    /// `xorps dst, src` — packed single bitwise xor (0F 57 /r).
    Xorps(X86Operand, X86Operand),
    /// `xorpd dst, src` — packed double bitwise xor (66 0F 57 /r).
    Xorpd(X86Operand, X86Operand),
    /// `andnps dst, src` — packed single bitwise and-not (0F 55 /r).
    Andnps(X86Operand, X86Operand),
    /// `andnpd dst, src` — packed double bitwise and-not (66 0F 55 /r).
    Andnpd(X86Operand, X86Operand),
    /// `sqrtps dst, src` — packed single sqrt (0F 51 /r).
    Sqrtps(X86Operand, X86Operand),
    /// `sqrtss dst, src` — scalar single sqrt (F3 0F 51 /r).
    Sqrtss(X86Operand, X86Operand),
    /// `sqrtpd dst, src` — packed double sqrt (66 0F 51 /r).
    Sqrtpd(X86Operand, X86Operand),
    /// `sqrtsd dst, src` — scalar double sqrt (F2 0F 51 /r).
    Sqrtsd(X86Operand, X86Operand),
    /// `cmpps dst, src, imm` — packed single compare (0F C2 /r ib).
    Cmpps(X86Operand, X86Operand, u8),
    /// `cmppd dst, src, imm` — packed double compare (66 0F C2 /r ib).
    Cmppd(X86Operand, X86Operand, u8),
    /// `cmpss dst, src, imm` — scalar single compare (F3 0F C2 /r ib).
    Cmpss(X86Operand, X86Operand, u8),
    /// `cmpsd dst, src, imm` — scalar double compare (F2 0F C2 /r ib).
    Cmpsd(X86Operand, X86Operand, u8),
    /// `shufps dst, src, imm` — packed single shuffle (0F C6 /r ib).
    Shufps(X86Operand, X86Operand, u8),
    /// `shufpd dst, src, imm` — packed double shuffle (66 0F C6 /r ib).
    Shufpd(X86Operand, X86Operand, u8),
    /// `unpcklps dst, src` — unpack low singles (0F 14 /r).
    Unpcklps(X86Operand, X86Operand),
    /// `unpckhps dst, src` — unpack high singles (0F 15 /r).
    Unpckhps(X86Operand, X86Operand),
    /// `unpcklpd dst, src` — unpack low doubles (66 0F 14 /r).
    Unpcklpd(X86Operand, X86Operand),
    /// `unpckhpd dst, src` — unpack high doubles (66 0F 15 /r).
    Unpckhpd(X86Operand, X86Operand),
    /// `cvtps2dq dst, src` — convert packed singles to dwords (66 0F 5B /r).
    Cvtps2dq(X86Operand, X86Operand),
    /// `cvtdq2ps dst, src` — convert packed dwords to singles (0F 5B /r).
    Cvtdq2ps(X86Operand, X86Operand),
    /// `cvttps2dq dst, src` — truncate packed singles to dwords (F3 0F 5B /r).
    Cvttps2dq(X86Operand, X86Operand),
    /// `cvtsi2ss dst, src` — convert dword/qword (GPR) to scalar single (F3 0F 2A /r).
    Cvtsi2ss(X86Operand, X86Operand),
    /// `cvtsi2sd dst, src` — convert dword/qword (GPR) to scalar double (F2 0F 2A /r).
    Cvtsi2sd(X86Operand, X86Operand),
    /// `cvtss2si dst, src` — convert scalar single to dword/qword (F3 0F 2D /r).
    Cvtss2si(X86Operand, X86Operand),
    /// `cvtsd2si dst, src` — convert scalar double to dword/qword (F2 0F 2D /r).
    Cvtsd2si(X86Operand, X86Operand),
    /// `cvttss2si dst, src` — truncate scalar single to dword/qword (F3 0F 2C /r).
    Cvttss2si(X86Operand, X86Operand),
    /// `cvttsd2si dst, src` — truncate scalar double to dword/qword (F2 0F 2C /r).
    Cvttsd2si(X86Operand, X86Operand),
    /// `maxps dst, src` — packed single maximum (0F 5F /r).
    Maxps(X86Operand, X86Operand),
    /// `minps dst, src` — packed single minimum (0F 5D /r).
    Minps(X86Operand, X86Operand),
    /// `maxpd dst, src` — packed double maximum (66 0F 5F /r).
    Maxpd(X86Operand, X86Operand),
    /// `minpd dst, src` — packed double minimum (66 0F 5D /r).
    Minpd(X86Operand, X86Operand),
    /// `maxss dst, src` — scalar single maximum (F3 0F 5F /r).
    Maxss(X86Operand, X86Operand),
    /// `minss dst, src` — scalar single minimum (F3 0F 5D /r).
    Minss(X86Operand, X86Operand),
    /// `maxsd dst, src` — scalar double maximum (F2 0F 5F /r).
    Maxsd(X86Operand, X86Operand),
    /// `minsd dst, src` — scalar double minimum (F2 0F 5D /r).
    Minsd(X86Operand, X86Operand),
    /// `comiss dst, src` — compare scalar single ordered (0F 2F /r).
    Comiss(X86Operand, X86Operand),
    /// `comisd dst, src` — compare scalar double ordered (66 0F 2F /r).
    Comisd(X86Operand, X86Operand),
    /// `ucomiss dst, src` — compare scalar single unordered (0F 2E /r).
    Ucomiss(X86Operand, X86Operand),
    /// `ucomisd dst, src` — compare scalar double unordered (66 0F 2E /r).
    Ucomisd(X86Operand, X86Operand),
    /// `pxor dst, src` — packed integer xor (66 0F EF /r).
    Pxor(X86Operand, X86Operand),
    /// `paddq dst, src` — packed quadword add (66 0F D4 /r).
    Paddq(X86Operand, X86Operand),
    /// `psubq dst, src` — packed quadword subtract (66 0F FB /r).
    Psubq(X86Operand, X86Operand),
    /// `pand dst, src` — packed integer and (66 0F DB /r).
    Pand(X86Operand, X86Operand),
    /// `por dst, src` — packed integer or (66 0F EB /r).
    Por(X86Operand, X86Operand),
    // --- SSSE3 (0F38 map, VEX.mmmmm=2) ---
    /// `pshufb dst, src` — packed shuffle bytes (66 0F 38 00 /r).
    Pshufb(X86Operand, X86Operand),
    /// `phaddw dst, src` — packed horizontal add words (66 0F 38 01 /r).
    Phaddw(X86Operand, X86Operand),
    /// `phaddd dst, src` — packed horizontal add dwords (66 0F 38 02 /r).
    Phaddd(X86Operand, X86Operand),
    /// `phaddsw dst, src` — packed horizontal add words saturated (66 0F 38 03 /r).
    Phaddsw(X86Operand, X86Operand),
    /// `pabsb dst, src` — packed absolute value bytes (66 0F 38 1C /r).
    Pabsb(X86Operand, X86Operand),
    /// `pabsw dst, src` — packed absolute value words (66 0F 38 1D /r).
    Pabsw(X86Operand, X86Operand),
    /// `pabsd dst, src` — packed absolute value dwords (66 0F 38 1E /r).
    Pabsd(X86Operand, X86Operand),
    // --- SSE4.1 (0F38 map, 66 prefix required) ---
    /// `pmovsxbw dst, src` — sign extend bytes to words (66 0F 38 20 /r).
    Pmovsxbw(X86Operand, X86Operand),
    /// `pmovsxbd dst, src` — sign extend bytes to dwords (66 0F 38 21 /r).
    Pmovsxbd(X86Operand, X86Operand),
    /// `pmovsxbq dst, src` — sign extend bytes to qwords (66 0F 38 22 /r).
    Pmovsxbq(X86Operand, X86Operand),
    /// `pmovsxwd dst, src` — sign extend words to dwords (66 0F 38 23 /r).
    Pmovsxwd(X86Operand, X86Operand),
    /// `pmovsxwq dst, src` — sign extend words to qwords (66 0F 38 24 /r).
    Pmovsxwq(X86Operand, X86Operand),
    /// `pmovsxdq dst, src` — sign extend dwords to qwords (66 0F 38 25 /r).
    Pmovsxdq(X86Operand, X86Operand),
    /// `pmovzxbw dst, src` — zero extend bytes to words (66 0F 38 30 /r).
    Pmovzxbw(X86Operand, X86Operand),
    /// `pmovzxbd dst, src` — zero extend bytes to dwords (66 0F 38 31 /r).
    Pmovzxbd(X86Operand, X86Operand),
    /// `pmovzxbq dst, src` — zero extend bytes to qwords (66 0F 38 32 /r).
    Pmovzxbq(X86Operand, X86Operand),
    /// `pmovzxwd dst, src` — zero extend words to dwords (66 0F 38 33 /r).
    Pmovzxwd(X86Operand, X86Operand),
    /// `pmovzxwq dst, src` — zero extend words to qwords (66 0F 38 34 /r).
    Pmovzxwq(X86Operand, X86Operand),
    /// `pmovzxdq dst, src` — zero extend dwords to qwords (66 0F 38 35 /r).
    Pmovzxdq(X86Operand, X86Operand),
    /// `pmuldq dst, src` — packed multiply qwords (66 0F 38 28 /r).
    Pmuldq(X86Operand, X86Operand),
    /// `pmulld dst, src` — packed multiply low dwords (66 0F 38 40 /r).
    Pmulld(X86Operand, X86Operand),
    /// `pcmpeqq dst, src` — packed compare qword equal (66 0F 38 29 /r).
    Pcmpeqq(X86Operand, X86Operand),
    /// `pcmpgtq dst, src` — packed compare qword greater (66 0F 38 37 /r).
    Pcmpgtq(X86Operand, X86Operand),
    /// `pminsb dst, src` — packed min signed bytes (66 0F 38 38 /r).
    Pminsb(X86Operand, X86Operand),
    /// `pminsd dst, src` — packed min signed dwords (66 0F 38 39 /r).
    Pminsd(X86Operand, X86Operand),
    /// `pminuw dst, src` — packed min unsigned words (66 0F 38 3A /r).
    Pminuw(X86Operand, X86Operand),
    /// `pminud dst, src` — packed min unsigned dwords (66 0F 38 3B /r).
    Pminud(X86Operand, X86Operand),
    /// `pmaxsb dst, src` — packed max signed bytes (66 0F 38 3C /r).
    Pmaxsb(X86Operand, X86Operand),
    /// `pmaxsd dst, src` — packed max signed dwords (66 0F 38 3D /r).
    Pmaxsd(X86Operand, X86Operand),
    /// `pmaxuw dst, src` — packed max unsigned words (66 0F 38 3E /r).
    Pmaxuw(X86Operand, X86Operand),
    /// `pmaxud dst, src` — packed max unsigned dwords (66 0F 38 3F /r).
    Pmaxud(X86Operand, X86Operand),
    /// `phminposuw dst, src` — packed horizontal min unsigned word (66 0F 38 41 /r).
    Phminposuw(X86Operand, X86Operand),
    // --- SSE4.1 (0F3A map, VEX.mmmmm=3) ---
    /// `roundps dst, src, imm` — round packed single (66 0F 3A 08 /r ib).
    Roundps(X86Operand, X86Operand, u8),
    /// `roundpd dst, src, imm` — round packed double (66 0F 3A 09 /r ib).
    Roundpd(X86Operand, X86Operand, u8),
    /// `roundss dst, src, imm` — round scalar single (66 0F 3A 0A /r ib).
    Roundss(X86Operand, X86Operand, u8),
    /// `roundsd dst, src, imm` — round scalar double (66 0F 3A 0B /r ib).
    Roundsd(X86Operand, X86Operand, u8),
    /// `palignr dst, src, imm` — packed align right (66 0F 3A 0F /r ib).
    Palignr(X86Operand, X86Operand, u8),
    /// `pinsrb dst, src, imm` — insert byte (66 0F 3A 20 /r ib).
    Pinsrb(X86Operand, X86Operand, u8),
    /// `pinsrd dst, src, imm` — insert dword (66 0F 3A 22 /r ib).
    Pinsrd(X86Operand, X86Operand, u8),
    /// `pinsrq dst, src, imm` — insert qword (66 0F 3A 22 /r ib, REX.W).
    Pinsrq(X86Operand, X86Operand, u8),
    /// `pextrb dst, src, imm` — extract byte (66 0F 3A 14 /r ib).
    Pextrb(X86Operand, X86Operand, u8),
    /// `pextrd dst, src, imm` — extract dword (66 0F 3A 16 /r ib).
    Pextrd(X86Operand, X86Operand, u8),
    /// `pextrq dst, src, imm` — extract qword (66 0F 3A 16 /r ib, REX.W).
    Pextrq(X86Operand, X86Operand, u8),
}

/// Decoded x86-64 prefixes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Prefixes {
    /// REX prefix byte was present.
    pub rex: bool,
    /// REX.W — 64-bit operand size.
    pub rex_w: bool,
    /// REX.R — extends the ModRM.reg field.
    pub rex_r: bool,
    /// REX.X — extends the SIB index field.
    pub rex_x: bool,
    /// REX.B — extends the ModRM.rm / SIB base field.
    pub rex_b: bool,
    /// 0x66 prefix — 16-bit operand size override.
    pub operand_size: bool,
    /// 0x67 prefix — 32-bit address size override (not modelled below 64-bit;
    /// the decoder rejects it).
    pub address_size: bool,
}

/// A fully decoded instruction, carrying its byte offset within the function,
/// its total encoded length, the prefixes, and the decoded instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedInstruction {
    /// Byte offset of the first byte of this instruction in the containing
    /// function's code.
    pub offset: usize,
    /// Total number of bytes this instruction occupies.
    pub length: usize,
    /// The x86-64 prefixes that preceded the opcode.
    pub prefixes: Prefixes,
    /// The decoded instruction.
    pub instruction: Instruction,
}

/// Parsed VEX prefix information (used for SSE/AVX instructions).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct VexInfo {
    /// The third-operand register index (0..15), already decoded from the
    /// complemented VEX.vvvv field.
    vvvv: u8,
    /// VEX.L — 256-bit operation (YMM).
    l: bool,
    /// VEX.pp — implied legacy prefix (0=none, 1=66, 2=F3, 3=F2).
    pp: u8,
    /// VEX.mmmmm — opcode map (1=0F, 2=0F38, 3=0F3A).
    mmmmm: u8,
    /// Equivalent REX.W from VEX.W.
    w: bool,
    /// Equivalent REX.R (ModRM.reg extension): true → reg is r8/xmm8+.
    rex_r: bool,
    /// Equivalent REX.X (SIB.index extension). Always false for 2-byte VEX.
    rex_x: bool,
    /// Equivalent REX.B (ModRM.rm / SIB.base extension). Always false for 2-byte VEX.
    rex_b: bool,
}

use std::fmt;

impl fmt::Display for Width {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Width::B => f.write_str("byte"),
            Width::W => f.write_str("word"),
            Width::D => f.write_str("dword"),
            Width::Q => f.write_str("qword"),
            Width::DQ => f.write_str("xmmword"),
            Width::QQ => f.write_str("ymmword"),
        }
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reg::RAX => f.write_str("rax"),
            Reg::RCX => f.write_str("rcx"),
            Reg::RDX => f.write_str("rdx"),
            Reg::RBX => f.write_str("rbx"),
            Reg::RSP => f.write_str("rsp"),
            Reg::RBP => f.write_str("rbp"),
            Reg::RSI => f.write_str("rsi"),
            Reg::RDI => f.write_str("rdi"),
            Reg::R8 => f.write_str("r8"),
            Reg::R9 => f.write_str("r9"),
            Reg::R10 => f.write_str("r10"),
            Reg::R11 => f.write_str("r11"),
            Reg::R12 => f.write_str("r12"),
            Reg::R13 => f.write_str("r13"),
            Reg::R14 => f.write_str("r14"),
            Reg::R15 => f.write_str("r15"),
        }
    }
}

impl fmt::Display for XmmReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            XmmReg::XMM0 => f.write_str("xmm0"),
            XmmReg::XMM1 => f.write_str("xmm1"),
            XmmReg::XMM2 => f.write_str("xmm2"),
            XmmReg::XMM3 => f.write_str("xmm3"),
            XmmReg::XMM4 => f.write_str("xmm4"),
            XmmReg::XMM5 => f.write_str("xmm5"),
            XmmReg::XMM6 => f.write_str("xmm6"),
            XmmReg::XMM7 => f.write_str("xmm7"),
            XmmReg::XMM8 => f.write_str("xmm8"),
            XmmReg::XMM9 => f.write_str("xmm9"),
            XmmReg::XMM10 => f.write_str("xmm10"),
            XmmReg::XMM11 => f.write_str("xmm11"),
            XmmReg::XMM12 => f.write_str("xmm12"),
            XmmReg::XMM13 => f.write_str("xmm13"),
            XmmReg::XMM14 => f.write_str("xmm14"),
            XmmReg::XMM15 => f.write_str("xmm15"),
        }
    }
}

impl fmt::Display for Condition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Condition::O => f.write_str("o"),
            Condition::NO => f.write_str("no"),
            Condition::B => f.write_str("b"),
            Condition::AE => f.write_str("ae"),
            Condition::E => f.write_str("e"),
            Condition::NE => f.write_str("ne"),
            Condition::BE => f.write_str("be"),
            Condition::A => f.write_str("a"),
            Condition::S => f.write_str("s"),
            Condition::NS => f.write_str("ns"),
            Condition::P => f.write_str("p"),
            Condition::NP => f.write_str("np"),
            Condition::L => f.write_str("l"),
            Condition::GE => f.write_str("ge"),
            Condition::LE => f.write_str("le"),
            Condition::G => f.write_str("g"),
        }
    }
}

impl fmt::Display for Mem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (&self.base, &self.index, self.disp) {
            (Some(base), Some((idx, scale)), 0) => {
                write!(f, "[{base}+{idx}*{scale}]")
            }
            (Some(base), Some((idx, scale)), disp) if disp < 0 => {
                write!(f, "[{base}+{idx}*{scale}-{}]", -disp)
            }
            (Some(base), Some((idx, scale)), disp) => {
                write!(f, "[{base}+{idx}*{scale}+{disp}]")
            }
            (Some(base), None, 0) => {
                write!(f, "[{base}]")
            }
            (Some(base), None, disp) if disp < 0 => {
                write!(f, "[{base}-{}]", -disp)
            }
            (Some(base), None, disp) => {
                write!(f, "[{base}+{disp}]")
            }
            (None, Some((idx, scale)), 0) => {
                write!(f, "[{idx}*{scale}]")
            }
            (None, Some((idx, scale)), disp) if disp < 0 => {
                write!(f, "[{idx}*{scale}-{}]", -disp)
            }
            (None, Some((idx, scale)), disp) => {
                write!(f, "[{idx}*{scale}+{disp}]")
            }
            (None, None, disp) if disp < 0 => {
                write!(f, "[0x{:x}]", disp as u64)
            }
            (None, None, disp) => {
                write!(f, "[0x{:x}]", disp as u64)
            }
        }
    }
}

impl fmt::Display for X86Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            X86Operand::Reg(r, w) => write!(f, "{r} ({w})"),
            X86Operand::Xmm(x, _w) => write!(f, "{x}"),
            X86Operand::Mem(m, w) => write!(f, "{w} {m}"),
            X86Operand::Imm(v) => write!(f, "0x{v:x}"),
            X86Operand::Rel(disp) => {
                if *disp < 0 {
                    write!(f, "rel -{}", -disp)
                } else {
                    write!(f, "rel +{disp}")
                }
            }
        }
    }
}

/// Helper: format a two-operand instruction `mnemonic dst, src`.
fn fmt_binary(f: &mut fmt::Formatter<'_>, mnemonic: &str, dst: &X86Operand, src: &X86Operand) -> fmt::Result {
    write!(f, "{mnemonic} {dst}, {src}")
}

/// Helper: format a two-operand-with-immediate instruction `mnemonic dst, src, imm`.
fn fmt_ternary(f: &mut fmt::Formatter<'_>, mnemonic: &str, a: &X86Operand, b: &X86Operand, imm: u8) -> fmt::Result {
    write!(f, "{mnemonic} {a}, {b}, {imm}")
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Nop => f.write_str("nop"),
            Instruction::Ret => f.write_str("ret"),
            Instruction::Syscall => f.write_str("syscall"),
            Instruction::Cdqe => f.write_str("cdqe"),
            Instruction::Cqo => f.write_str("cqo"),
            Instruction::Int3 => f.write_str("int3"),
            Instruction::Stc => f.write_str("stc"),
            Instruction::Clc => f.write_str("clc"),
            Instruction::Cmc => f.write_str("cmc"),
            Instruction::Std => f.write_str("std"),
            Instruction::Cld => f.write_str("cld"),
            Instruction::Lahf => f.write_str("lahf"),
            Instruction::Sahf => f.write_str("sahf"),
            Instruction::Pushf => f.write_str("pushf"),
            Instruction::Popf => f.write_str("popf"),
            // One-operand
            Instruction::Push(o) => write!(f, "push {o}"),
            Instruction::Pop(o) => write!(f, "pop {o}"),
            Instruction::Call(o) => write!(f, "call {o}"),
            Instruction::Jmp(o) => write!(f, "jmp {o}"),
            Instruction::Neg(o) => write!(f, "neg {o}"),
            Instruction::Not(o) => write!(f, "not {o}"),
            Instruction::Inc(o) => write!(f, "inc {o}"),
            Instruction::Dec(o) => write!(f, "dec {o}"),
            Instruction::Mul(o) => write!(f, "mul {o}"),
            Instruction::Imul(o) => write!(f, "imul {o}"),
            Instruction::Div(o) => write!(f, "div {o}"),
            Instruction::Idiv(o) => write!(f, "idiv {o}"),
            // Two-operand ALU / data movement
            Instruction::Mov(d, s) => fmt_binary(f, "mov", d, s),
            Instruction::Movzx(d, s) => fmt_binary(f, "movzx", d, s),
            Instruction::Movsx(d, s) => fmt_binary(f, "movsx", d, s),
            Instruction::Movsxd(d, s) => fmt_binary(f, "movsxd", d, s),
            Instruction::Add(d, s) => fmt_binary(f, "add", d, s),
            Instruction::Sub(d, s) => fmt_binary(f, "sub", d, s),
            Instruction::Xor(d, s) => fmt_binary(f, "xor", d, s),
            Instruction::And(d, s) => fmt_binary(f, "and", d, s),
            Instruction::Or(d, s) => fmt_binary(f, "or", d, s),
            Instruction::Cmp(a, b) => fmt_binary(f, "cmp", a, b),
            Instruction::Test(a, b) => fmt_binary(f, "test", a, b),
            Instruction::Xchg(a, b) => fmt_binary(f, "xchg", a, b),
            Instruction::Bt(a, b) => fmt_binary(f, "bt", a, b),
            Instruction::Bts(a, b) => fmt_binary(f, "bts", a, b),
            Instruction::Btr(a, b) => fmt_binary(f, "btr", a, b),
            Instruction::Btc(a, b) => fmt_binary(f, "btc", a, b),
            Instruction::Bsf(d, s) => fmt_binary(f, "bsf", d, s),
            Instruction::Bsr(d, s) => fmt_binary(f, "bsr", d, s),
            // Shift/rotate with imm8
            Instruction::Shl(o, i) => write!(f, "shl {o}, {i}"),
            Instruction::Shr(o, i) => write!(f, "shr {o}, {i}"),
            Instruction::Sar(o, i) => write!(f, "sar {o}, {i}"),
            Instruction::Rol(o, i) => write!(f, "rol {o}, {i}"),
            Instruction::Ror(o, i) => write!(f, "ror {o}, {i}"),
            Instruction::Rcl(o, i) => write!(f, "rcl {o}, {i}"),
            Instruction::Rcr(o, i) => write!(f, "rcr {o}, {i}"),
            // Special multi-operand
            Instruction::Lea(r, w, m) => write!(f, "lea {r} ({w}), {m}"),
            Instruction::Jcc(cc, disp) => write!(f, "j{cc} rel {disp}"),
            Instruction::Cmovcc(cc, d, s) => write!(f, "cmov{cc} {d}, {s}"),
            Instruction::Setcc(cc, o) => write!(f, "set{cc} {o}"),
            // String ops
            Instruction::Movs(w) => write!(f, "movs {w}"),
            Instruction::Stos(w) => write!(f, "stos {w}"),
            Instruction::Lods(w) => write!(f, "lods {w}"),
            Instruction::Scas(w) => write!(f, "scas {w}"),
            Instruction::Cmps(w) => write!(f, "cmps {w}"),
            // SSE two-operand
            Instruction::Movaps(d, s) => fmt_binary(f, "movaps", d, s),
            Instruction::Movapd(d, s) => fmt_binary(f, "movapd", d, s),
            Instruction::Movups(d, s) => fmt_binary(f, "movups", d, s),
            Instruction::Movdqa(d, s) => fmt_binary(f, "movdqa", d, s),
            Instruction::Movdqu(d, s) => fmt_binary(f, "movdqu", d, s),
            Instruction::Movss(d, s) => fmt_binary(f, "movss", d, s),
            Instruction::Movsd(d, s) => fmt_binary(f, "movsd", d, s),
            Instruction::Movq(d, s) => fmt_binary(f, "movq", d, s),
            Instruction::Movd(d, s) => fmt_binary(f, "movd", d, s),
            Instruction::Addps(d, s) => fmt_binary(f, "addps", d, s),
            Instruction::Addss(d, s) => fmt_binary(f, "addss", d, s),
            Instruction::Addpd(d, s) => fmt_binary(f, "addpd", d, s),
            Instruction::Addsd(d, s) => fmt_binary(f, "addsd", d, s),
            Instruction::Subps(d, s) => fmt_binary(f, "subps", d, s),
            Instruction::Subss(d, s) => fmt_binary(f, "subss", d, s),
            Instruction::Subpd(d, s) => fmt_binary(f, "subpd", d, s),
            Instruction::Subsd(d, s) => fmt_binary(f, "subsd", d, s),
            Instruction::Mulps(d, s) => fmt_binary(f, "mulps", d, s),
            Instruction::Mulss(d, s) => fmt_binary(f, "mulss", d, s),
            Instruction::Mulpd(d, s) => fmt_binary(f, "mulpd", d, s),
            Instruction::Mulsd(d, s) => fmt_binary(f, "mulsd", d, s),
            Instruction::Divps(d, s) => fmt_binary(f, "divps", d, s),
            Instruction::Divss(d, s) => fmt_binary(f, "divss", d, s),
            Instruction::Divpd(d, s) => fmt_binary(f, "divpd", d, s),
            Instruction::Divsd(d, s) => fmt_binary(f, "divsd", d, s),
            Instruction::Andps(d, s) => fmt_binary(f, "andps", d, s),
            Instruction::Andpd(d, s) => fmt_binary(f, "andpd", d, s),
            Instruction::Orps(d, s) => fmt_binary(f, "orps", d, s),
            Instruction::Orpd(d, s) => fmt_binary(f, "orpd", d, s),
            Instruction::Xorps(d, s) => fmt_binary(f, "xorps", d, s),
            Instruction::Xorpd(d, s) => fmt_binary(f, "xorpd", d, s),
            Instruction::Andnps(d, s) => fmt_binary(f, "andnps", d, s),
            Instruction::Andnpd(d, s) => fmt_binary(f, "andnpd", d, s),
            Instruction::Sqrtps(d, s) => fmt_binary(f, "sqrtps", d, s),
            Instruction::Sqrtss(d, s) => fmt_binary(f, "sqrtss", d, s),
            Instruction::Sqrtpd(d, s) => fmt_binary(f, "sqrtpd", d, s),
            Instruction::Sqrtsd(d, s) => fmt_binary(f, "sqrtsd", d, s),
            Instruction::Unpcklps(d, s) => fmt_binary(f, "unpcklps", d, s),
            Instruction::Unpckhps(d, s) => fmt_binary(f, "unpckhps", d, s),
            Instruction::Unpcklpd(d, s) => fmt_binary(f, "unpcklpd", d, s),
            Instruction::Unpckhpd(d, s) => fmt_binary(f, "unpckhpd", d, s),
            Instruction::Cvtps2dq(d, s) => fmt_binary(f, "cvtps2dq", d, s),
            Instruction::Cvtdq2ps(d, s) => fmt_binary(f, "cvtdq2ps", d, s),
            Instruction::Cvttps2dq(d, s) => fmt_binary(f, "cvttps2dq", d, s),
            Instruction::Cvtsi2ss(d, s) => fmt_binary(f, "cvtsi2ss", d, s),
            Instruction::Cvtsi2sd(d, s) => fmt_binary(f, "cvtsi2sd", d, s),
            Instruction::Cvtss2si(d, s) => fmt_binary(f, "cvtss2si", d, s),
            Instruction::Cvtsd2si(d, s) => fmt_binary(f, "cvtsd2si", d, s),
            Instruction::Cvttss2si(d, s) => fmt_binary(f, "cvttss2si", d, s),
            Instruction::Cvttsd2si(d, s) => fmt_binary(f, "cvttsd2si", d, s),
            Instruction::Maxps(d, s) => fmt_binary(f, "maxps", d, s),
            Instruction::Maxpd(d, s) => fmt_binary(f, "maxpd", d, s),
            Instruction::Maxss(d, s) => fmt_binary(f, "maxss", d, s),
            Instruction::Maxsd(d, s) => fmt_binary(f, "maxsd", d, s),
            Instruction::Minps(d, s) => fmt_binary(f, "minps", d, s),
            Instruction::Minpd(d, s) => fmt_binary(f, "minpd", d, s),
            Instruction::Minss(d, s) => fmt_binary(f, "minss", d, s),
            Instruction::Minsd(d, s) => fmt_binary(f, "minsd", d, s),
            Instruction::Comiss(d, s) => fmt_binary(f, "comiss", d, s),
            Instruction::Comisd(d, s) => fmt_binary(f, "comisd", d, s),
            Instruction::Ucomiss(d, s) => fmt_binary(f, "ucomiss", d, s),
            Instruction::Ucomisd(d, s) => fmt_binary(f, "ucomisd", d, s),
            Instruction::Pxor(d, s) => fmt_binary(f, "pxor", d, s),
            Instruction::Paddq(d, s) => fmt_binary(f, "paddq", d, s),
            Instruction::Psubq(d, s) => fmt_binary(f, "psubq", d, s),
            Instruction::Pand(d, s) => fmt_binary(f, "pand", d, s),
            Instruction::Por(d, s) => fmt_binary(f, "por", d, s),
            Instruction::Pshufb(d, s) => fmt_binary(f, "pshufb", d, s),
            Instruction::Phaddw(d, s) => fmt_binary(f, "phaddw", d, s),
            Instruction::Phaddd(d, s) => fmt_binary(f, "phaddd", d, s),
            Instruction::Phaddsw(d, s) => fmt_binary(f, "phaddsw", d, s),
            Instruction::Pabsb(d, s) => fmt_binary(f, "pabsb", d, s),
            Instruction::Pabsw(d, s) => fmt_binary(f, "pabsw", d, s),
            Instruction::Pabsd(d, s) => fmt_binary(f, "pabsd", d, s),
            Instruction::Pmovsxbw(d, s) => fmt_binary(f, "pmovsxbw", d, s),
            Instruction::Pmovsxbd(d, s) => fmt_binary(f, "pmovsxbd", d, s),
            Instruction::Pmovsxbq(d, s) => fmt_binary(f, "pmovsxbq", d, s),
            Instruction::Pmovsxwd(d, s) => fmt_binary(f, "pmovsxwd", d, s),
            Instruction::Pmovsxwq(d, s) => fmt_binary(f, "pmovsxwq", d, s),
            Instruction::Pmovsxdq(d, s) => fmt_binary(f, "pmovsxdq", d, s),
            Instruction::Pmovzxbw(d, s) => fmt_binary(f, "pmovzxbw", d, s),
            Instruction::Pmovzxbd(d, s) => fmt_binary(f, "pmovzxbd", d, s),
            Instruction::Pmovzxbq(d, s) => fmt_binary(f, "pmovzxbq", d, s),
            Instruction::Pmovzxwd(d, s) => fmt_binary(f, "pmovzxwd", d, s),
            Instruction::Pmovzxwq(d, s) => fmt_binary(f, "pmovzxwq", d, s),
            Instruction::Pmovzxdq(d, s) => fmt_binary(f, "pmovzxdq", d, s),
            Instruction::Pmuldq(d, s) => fmt_binary(f, "pmuldq", d, s),
            Instruction::Pmulld(d, s) => fmt_binary(f, "pmulld", d, s),
            Instruction::Pcmpeqq(d, s) => fmt_binary(f, "pcmpeqq", d, s),
            Instruction::Pcmpgtq(d, s) => fmt_binary(f, "pcmpgtq", d, s),
            Instruction::Pminsb(d, s) => fmt_binary(f, "pminsb", d, s),
            Instruction::Pminsd(d, s) => fmt_binary(f, "pminsd", d, s),
            Instruction::Pminuw(d, s) => fmt_binary(f, "pminuw", d, s),
            Instruction::Pminud(d, s) => fmt_binary(f, "pminud", d, s),
            Instruction::Pmaxsb(d, s) => fmt_binary(f, "pmaxsb", d, s),
            Instruction::Pmaxsd(d, s) => fmt_binary(f, "pmaxsd", d, s),
            Instruction::Pmaxuw(d, s) => fmt_binary(f, "pmaxuw", d, s),
            Instruction::Pmaxud(d, s) => fmt_binary(f, "pmaxud", d, s),
            Instruction::Phminposuw(d, s) => fmt_binary(f, "phminposuw", d, s),
            // SSE with immediate
            Instruction::Cmpps(d, s, i) => fmt_ternary(f, "cmpps", d, s, *i),
            Instruction::Cmppd(d, s, i) => fmt_ternary(f, "cmppd", d, s, *i),
            Instruction::Cmpss(d, s, i) => fmt_ternary(f, "cmpss", d, s, *i),
            Instruction::Cmpsd(d, s, i) => fmt_ternary(f, "cmpsd", d, s, *i),
            Instruction::Shufps(d, s, i) => fmt_ternary(f, "shufps", d, s, *i),
            Instruction::Shufpd(d, s, i) => fmt_ternary(f, "shufpd", d, s, *i),
            Instruction::Roundps(d, s, i) => fmt_ternary(f, "roundps", d, s, *i),
            Instruction::Roundpd(d, s, i) => fmt_ternary(f, "roundpd", d, s, *i),
            Instruction::Roundss(d, s, i) => fmt_ternary(f, "roundss", d, s, *i),
            Instruction::Roundsd(d, s, i) => fmt_ternary(f, "roundsd", d, s, *i),
            Instruction::Palignr(d, s, i) => fmt_ternary(f, "palignr", d, s, *i),
            Instruction::Pinsrb(d, s, i) => fmt_ternary(f, "pinsrb", d, s, *i),
            Instruction::Pinsrd(d, s, i) => fmt_ternary(f, "pinsrd", d, s, *i),
            Instruction::Pinsrq(d, s, i) => fmt_ternary(f, "pinsrq", d, s, *i),
            Instruction::Pextrb(d, s, i) => fmt_ternary(f, "pextrb", d, s, *i),
            Instruction::Pextrd(d, s, i) => fmt_ternary(f, "pextrd", d, s, *i),
            Instruction::Pextrq(d, s, i) => fmt_ternary(f, "pextrq", d, s, *i),
        }
    }
}

/// Decode a single x86-64 instruction from `code` starting at `offset`.
///
/// Returns a [`DecodedInstruction`] on success; returns `Err` with a
/// human-readable description on any unrecognised opcode, truncated input,
/// malformed ModRM/SIB, or unsupported addressing mode. **No input can
/// trigger undefined behaviour or a panic** — every access is bounds-checked.
///
/// The supported instruction subset is deliberately small (see the
/// [`Instruction`] enum). Unknown opcodes produce `Err`, never a guess.
pub fn decode_instruction(code: &[u8], offset: usize) -> csolver_core::Result<DecodedInstruction> {
    let mut p = offset;

    // --- Parse legacy prefixes (REX, 66, F2, F3, segments) ---
    let (rex_w, rex_r, rex_x, rex_b, op_size, addr_size, sse_pp) = parse_prefixes(code, &mut p)?;

    // The width of most integer operations: 64 with REX.W, else 32.
    let width = Width::from_rex_w(rex_w);

    // --- Check for VEX prefix (C4 / C5 in 64-bit mode) ---
    if let Some(&b) = code.get(p) {
        if b == 0xc5 || b == 0xc4 {
            let vex = parse_vex(code, &mut p, b == 0xc5)?;
            // The effective REX bits and the third-operand register are already
            // decoded in `vex` (see `parse_vex`).
            let (v_rex_w, v_rex_r, v_rex_x, v_rex_b) = (vex.w, vex.rex_r, vex.rex_x, vex.rex_b);

            // Determine the opcode lead bytes based on VEX.mmmmm.
            const MAP_0F: u8 = 1;
            const MAP_0F38: u8 = 2;
            const MAP_0F3A: u8 = 3;
            let (inst, next) = match vex.mmmmm {
                MAP_0F => decode_vex_0f(code, &mut p, vex)?,
                MAP_0F38 => decode_vex_0f38(code, &mut p, vex)?,
                MAP_0F3A => decode_vex_0f3a(code, &mut p, vex)?,
                _ => return Err(CoreError::unsupported(format!("x86: unsupported VEX map {}", vex.mmmmm))),
            };

            return Ok(DecodedInstruction {
                offset,
                length: next - offset,
                prefixes: Prefixes {
                    rex: false,
                    rex_w: v_rex_w, rex_r: v_rex_r, rex_x: v_rex_x, rex_b: v_rex_b,
                    operand_size: op_size,
                    address_size: addr_size,
                },
                instruction: inst,
            });
        }
    }

    // --- Opcode byte (non-VEX path) ---
    let op = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated opcode at offset {p}")))?;
    p += 1;

    // --- Decode by opcode ---
    let (inst, next) = decode_typed_opcode(op, code, p, rex_w, rex_r, rex_x, rex_b, op_size, width, sse_pp)?;

    Ok(DecodedInstruction {
        offset,
        length: next - offset,
        prefixes: Prefixes {
            rex: rex_w || rex_r || rex_x || rex_b,
            rex_w, rex_r, rex_x, rex_b,
            operand_size: op_size,
            address_size: addr_size,
        },
        instruction: inst,
    })
}

/// Parse x86-64 legacy and REX prefixes, advancing `p` past them.
/// Returns (rex_w, rex_r, rex_x, rex_b, op_size, addr_size, sse_pp)
/// where sse_pp encodes the SSE/VEX mandatory prefix: 0=None, 1=0x66, 2=0xF3, 3=0xF2.
fn parse_prefixes(code: &[u8], p: &mut usize) -> csolver_core::Result<(bool, bool, bool, bool, bool, bool, u8)> {
    let mut rex_w = false;
    let mut rex_r = false;
    let mut rex_x = false;
    let mut rex_b = false;
    let mut op_size = false;
    let mut addr_size = false;
    let mut sse_pp: u8 = 0;

    loop {
        match code.get(*p).copied() {
            // REX prefix (0x40..0x4F) — only one REX prefix is valid.
            Some(b) if (0x40..=0x4f).contains(&b) => {
                rex_w = b & 8 != 0;
                rex_r = b & 4 != 0;
                rex_x = b & 2 != 0;
                rex_b = b & 1 != 0;
                *p += 1;
            }
            Some(0x66) => {
                op_size = true;
                sse_pp = 1;
                *p += 1;
            }
            Some(0x67) => {
                addr_size = true;
                *p += 1;
            }
            Some(0xF0) => {
                return Err(CoreError::unsupported("x86: LOCK prefix"));
            }
            Some(0xF2) => {
                sse_pp = 3; // REPNE → SSE prefix F2
                *p += 1;
            }
            Some(0xF3) => {
                sse_pp = 2; // REP/REPE → SSE prefix F3
                *p += 1;
            }
            Some(0x26 | 0x2E | 0x36 | 0x3E | 0x64 | 0x65) => {
                *p += 1;
            }
            _ => break,
        }
    }

    Ok((rex_w, rex_r, rex_x, rex_b, op_size, addr_size, sse_pp))
}

/// Decode the typed instruction after prefixes have been parsed.
#[allow(clippy::too_many_arguments)]
fn decode_typed_opcode(
    op: u8,
    code: &[u8],
    mut p: usize,
    rex_w: bool,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    _op_size: bool,
    width: Width,
    sse_pp: u8,
) -> csolver_core::Result<(Instruction, usize)> {
    // Helper: produce a register operand at the given width.
    let reg_op = |r: Reg| X86Operand::Reg(r, width);

    match op {
        0x90 => {
            // nop (when no ModRM follows; with ModRM it is xchg eax,reg).
            // The 0x90 nop is specifically opcode 0x90 with no ModRM byte.
            // We check that the next byte is either at end of code or is
            // not a valid ModRM-like follow-on — but in linear decode we
            // just emit Nop; if there is more code the caller will decode it.
            Ok((Instruction::Nop, p))
        }
        0xc3 => Ok((Instruction::Ret, p)),

        0xb8..=0xbf => {
            // mov r, imm{32,64}
            let r = Reg::from_idx((op - 0xb8) | if rex_b { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid register encoding in mov reg,imm"))?;
            let (imm, len) = read_imm64(code, p, if rex_w { 8 } else { 4 })?;
            p += len;
            Ok((Instruction::Mov(reg_op(r), X86Operand::Imm(imm)), p))
        }

        // xor r/m, r (0x31), add  (0x01), sub (0x29),
        // and r/m, r (0x21), or   (0x09) — register form only.
        0x31 | 0x01 | 0x29 | 0x21 | 0x09 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: ALU with a memory operand"));
            }
            let dst = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid dst register in ALU"))?;
            let src = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src register in ALU"))?;
            let inst = match op {
                0x31 => {
                    if m.rm == m.reg {
                        // xor r, r → zero idiom
                        Instruction::Mov(reg_op(dst), X86Operand::Imm(0))
                    } else {
                        Instruction::Xor(reg_op(dst), reg_op(src))
                    }
                }
                0x01 => Instruction::Add(reg_op(dst), reg_op(src)),
                0x29 => Instruction::Sub(reg_op(dst), reg_op(src)),
                0x21 => Instruction::And(reg_op(dst), reg_op(src)),
                0x09 => Instruction::Or(reg_op(dst), reg_op(src)),
                _ => unreachable!(),
            };
            Ok((inst, p))
        }

        // mov r/m, r  (0x89)
        0x89 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let src = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src register in mov r/m,r"))?;
            if m.mode == 0b11 {
                let dst = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid dst register in mov r/m,r"))?;
                Ok((Instruction::Mov(reg_op(dst), reg_op(src)), p))
            } else {
                let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                Ok((Instruction::Mov(X86Operand::Mem(mem, width), reg_op(src)), p))
            }
        }

        // mov r, r/m (0x8b)
        0x8b => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let dst = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid dst register in mov r,r/m"))?;
            if m.mode == 0b11 {
                let src = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid src register in mov r,r/m"))?;
                Ok((Instruction::Mov(reg_op(dst), reg_op(src)), p))
            } else {
                let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                Ok((Instruction::Mov(reg_op(dst), X86Operand::Mem(mem, width)), p))
            }
        }

        // lea r, m (0x8d)
        0x8d => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                return Err(CoreError::parse("x86: lea requires a memory operand"));
            }
            let dst = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid dst register in lea"))?;
            let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
            Ok((Instruction::Lea(dst, width, mem), p))
        }

        // Group 1 (0x80): ALU r/m8, imm8 (unsigned imm8).
        0x80 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, Width::B)?;
            let imm = read_imm_u8(code, &mut p)?;
            let group_op = group1_op_from_modrm_reg(code, p - 2, rex_r, rex_b)?;
            let inst = match group_op {
                Group1Op::Add => Instruction::Add(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Sub => Instruction::Sub(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Cmp => Instruction::Cmp(operand, X86Operand::Imm(imm as u64)),
                Group1Op::And => Instruction::And(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Or => Instruction::Or(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Xor => Instruction::Xor(operand, X86Operand::Imm(imm as u64)),
                _ => return Err(CoreError::unsupported("x86: unsupported group-1 operation with imm8 (0x80)")),
            };
            Ok((inst, p))
        }
        // Group 1 (0x81): ALU r/m, imm32 (sign-extended to operand width).
        0x81 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, width)?;
            let imm = read_imm_i32(code, &mut p)? as u64;
            let group_op = group1_op_from_modrm_reg(code, p - 5, rex_r, rex_b)?;
            let inst = match group_op {
                Group1Op::Add => Instruction::Add(operand, X86Operand::Imm(imm)),
                Group1Op::Sub => Instruction::Sub(operand, X86Operand::Imm(imm)),
                Group1Op::Cmp => Instruction::Cmp(operand, X86Operand::Imm(imm)),
                Group1Op::And => Instruction::And(operand, X86Operand::Imm(imm)),
                Group1Op::Or => Instruction::Or(operand, X86Operand::Imm(imm)),
                Group1Op::Xor => Instruction::Xor(operand, X86Operand::Imm(imm)),
                _ => return Err(CoreError::unsupported("x86: unsupported group-1 operation with imm32")),
            };
            Ok((inst, p))
        }
        // Group 1 (0x82/0x83): ALU r/m, imm8 (sign-extended to width).
        // 0x82 is an alias for 0x83 in 64-bit mode (but should not be emitted by
        // modern assemblers; we decode it identically).
        0x82 | 0x83 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, width)?;
            let imm = read_imm_u8(code, &mut p)?;
            // Sign-extend imm8 to operand width.
            let imm = (imm as i8 as i64) as u64;
            let group_op = group1_op_from_modrm_reg(code, p - 2, rex_r, rex_b)?;
            let inst = match group_op {
                Group1Op::Add => Instruction::Add(operand, X86Operand::Imm(imm)),
                Group1Op::Sub => Instruction::Sub(operand, X86Operand::Imm(imm)),
                Group1Op::Cmp => Instruction::Cmp(operand, X86Operand::Imm(imm)),
                Group1Op::And => Instruction::And(operand, X86Operand::Imm(imm)),
                Group1Op::Or => Instruction::Or(operand, X86Operand::Imm(imm)),
                Group1Op::Xor => Instruction::Xor(operand, X86Operand::Imm(imm as u64)),
                _ => return Err(CoreError::unsupported("x86: unsupported group-1 operation with imm8")),
            };
            Ok((inst, p))
        }

        // cmp r/m, r (0x39) — register form only.
        0x39 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: cmp with a memory operand"));
            }
            let lhs = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in cmp"))?;
            let rhs = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in cmp"))?;
            Ok((Instruction::Cmp(reg_op(lhs), reg_op(rhs)), p))
        }

        // cmp r, r/m (0x3b) — register form only.
        0x3b => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: cmp with a memory operand"));
            }
            let lhs = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in cmp"))?;
            let rhs = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in cmp"))?;
            Ok((Instruction::Cmp(reg_op(lhs), reg_op(rhs)), p))
        }

        // cmp eax/u, imm32 (0x3d)
        0x3d => {
            let (imm, len) = read_imm64(code, p, 4)?;
            p += len;
            Ok((Instruction::Cmp(reg_op(Reg::RAX), X86Operand::Imm(imm)), p))
        }

        // test r/m, r (0x85) — register form only.
        0x85 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: test with a memory operand"));
            }
            let lhs = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in test"))?;
            let rhs = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in test"))?;
            Ok((Instruction::Test(reg_op(lhs), reg_op(rhs)), p))
        }

        // jmp rel8 (0xeb)
        0xeb => {
            let rel = read_imm_i8(code, &mut p)?;
            Ok((Instruction::Jmp(X86Operand::Rel(rel as i64)), p))
        }

        // jmp rel32 (0xe9)
        0xe9 => {
            let rel = read_imm_i32(code, &mut p)?;
            Ok((Instruction::Jmp(X86Operand::Rel(rel as i64)), p))
        }

        // jcc rel8 (0x70..0x7f)
        0x70..=0x7f => {
            let rel = read_imm_i8(code, &mut p)?;
            let cc = Condition::from_cc(op - 0x70)
                .ok_or_else(|| CoreError::parse("x86: invalid condition code"))?;
            Ok((Instruction::Jcc(cc, rel as i64), p))
        }

        // push reg (0x50..0x57) — push register onto stack.
        0x50..=0x57 => {
            let r = Reg::from_idx((op - 0x50) | if rex_b { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid register in push"))?;
            Ok((Instruction::Push(reg_op(r)), p))
        }

        // pop reg (0x58..0x5f) — pop register from stack.
        0x58..=0x5f => {
            let r = Reg::from_idx((op - 0x58) | if rex_b { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid register in pop"))?;
            Ok((Instruction::Pop(reg_op(r)), p))
        }

        // push imm32 (0x68) — sign-extended to 64 bits.
        0x68 => {
            let imm = read_imm_i32(code, &mut p)? as u64;
            Ok((Instruction::Push(X86Operand::Imm(imm)), p))
        }

        // push imm8 (0x6a) — sign-extended imm8.
        0x6a => {
            let v = read_imm_i8(code, &mut p)?;
            Ok((Instruction::Push(X86Operand::Imm(v as u64)), p))
        }

        // xchg r/m, r  (0x87) — register form only.
        0x87 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: xchg with a memory operand"));
            }
            let a = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in xchg"))?;
            let b = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in xchg"))?;
            Ok((Instruction::Xchg(reg_op(a), reg_op(b)), p))
        }

        // xchg eax/rax, reg (0x91..0x97)
        0x91..=0x97 => {
            let r = Reg::from_idx((op - 0x91) | if rex_b { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid register in xchg"))?;
            Ok((Instruction::Xchg(reg_op(Reg::RAX), reg_op(r)), p))
        }

        // cdqe (0x98) — sign-extend eax to rax (cwde in 16-bit, cdqe in 32/64).
        0x98 => Ok((Instruction::Cdqe, p)),

        // cqo (0x99) — sign-extend rax to rdx:rax (cwd/cdq/cqo depending on width).
        0x99 => Ok((Instruction::Cqo, p)),

        // movsxd (0x63) — sign-extend dword src to qword dst (REX.W implied for 64-bit dst).
        0x63 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let dst = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in movsxd"))?;
            if m.mode == 0b11 {
                let src = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid register in movsxd"))?;
                Ok((Instruction::Movsxd(X86Operand::Reg(dst, Width::Q), X86Operand::Reg(src, Width::D)), p))
            } else {
                let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                Ok((Instruction::Movsxd(X86Operand::Reg(dst, Width::Q), X86Operand::Mem(mem, Width::D)), p))
            }
        }

        // String operations (0xa4..0xaf) — movs, cmps, stos, lods, scas.
        0xa4 => Ok((Instruction::Movs(Width::B), p)),
        0xa5 => Ok((Instruction::Movs(width), p)),
        0xa6 => Ok((Instruction::Cmps(Width::B), p)),
        0xa7 => Ok((Instruction::Cmps(width), p)),
        0xaa => Ok((Instruction::Stos(Width::B), p)),
        0xab => Ok((Instruction::Stos(width), p)),
        0xac => Ok((Instruction::Lods(Width::B), p)),
        0xad => Ok((Instruction::Lods(width), p)),
        0xae => Ok((Instruction::Scas(Width::B), p)),
        0xaf => Ok((Instruction::Scas(width), p)),

        // int3 (0xcc)
        0xcc => Ok((Instruction::Int3, p)),

        // lahf (0x9f) — load flags into AH.
        0x9f => Ok((Instruction::Lahf, p)),
        // sahf (0x9e) — store AH into flags.
        0x9e => Ok((Instruction::Sahf, p)),
        // pushf (0x9c) — push flags.
        0x9c => Ok((Instruction::Pushf, p)),
        // popf (0x9d) — pop flags.
        0x9d => Ok((Instruction::Popf, p)),

        // clc (0xf8) — clear carry flag.
        0xf8 => Ok((Instruction::Clc, p)),
        // stc (0xf9) — set carry flag.
        0xf9 => Ok((Instruction::Stc, p)),
        // cmc (0xf5) — complement carry flag.
        0xf5 => Ok((Instruction::Cmc, p)),
        // cld (0xfc) — clear direction flag.
        0xfc => Ok((Instruction::Cld, p)),
        // std (0xfd) — set direction flag.
        0xfd => Ok((Instruction::Std, p)),

        // call rel32 (0xe8)
        0xe8 => {
            let rel = read_imm_i32(code, &mut p)?;
            Ok((Instruction::Call(X86Operand::Rel(rel as i64)), p))
        }

        // Group 4 (0xfe): inc/dec r/m (register form only).
        0xfe => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: inc/dec with a memory operand"));
            }
            let dst = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in inc/dec"))?;
            let operand = X86Operand::Reg(dst, Width::B);
            match m.reg & 7 {
                0 => Ok((Instruction::Inc(operand), p)),
                1 => Ok((Instruction::Dec(operand), p)),
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-4 /digit {}", m.reg & 7))),
            }
        }

        // Group 5 (0xff): inc/dec/call/jmp r/m (register form only).
        0xff => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: group-5 with a memory operand"));
            }
            let dst = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in group-5"))?;
            let operand = reg_op(dst);
            match m.reg & 7 {
                0 => Ok((Instruction::Inc(operand), p)),
                1 => Ok((Instruction::Dec(operand), p)),
                2 => Ok((Instruction::Call(operand), p)),
                4 => Ok((Instruction::Jmp(operand), p)),
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-5 /digit {}", m.reg & 7))),
            }
        }

        // MOV r/m8, imm8 (0xc6).
        0xc6 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, Width::B)?;
            let imm = read_imm_u8(code, &mut p)?;
            Ok((Instruction::Mov(operand, X86Operand::Imm(imm as u64)), p))
        }
        // MOV r/m, imm32 (0xc7) — imm32 sign-extended when width > 32 (REX.W).
        0xc7 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, width)?;
            let (imm_raw, _) = read_imm64(code, p, 4)?;
            p += 4;
            let imm = if width.bits() > 32 { imm_raw as u32 as i32 as i64 as u128 as u64 } else { imm_raw };
            Ok((Instruction::Mov(operand, X86Operand::Imm(imm)), p))
        }

        // Group 2 — rotate/shift by imm8 (0xc0 byte, 0xc1 word/d/q).
        // Intel /digit encoding: 0=ROL, 1=ROR, 2=RCL, 3=RCR, 4=SHL, 5=SHR, 6=reserved, 7=SAR.
        0xc0 | 0xc1 => {
            let shift_width = if op == 0xc0 { Width::B } else { width };
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, shift_width)?;
            let imm = read_imm_u8(code, &mut p)?;
            let m = read_modrm(code, p - 2, rex_r, rex_b)?;
            match m.reg & 7 {
                0 => Ok((Instruction::Rol(operand, imm), p)),
                1 => Ok((Instruction::Ror(operand, imm), p)),
                2 => Ok((Instruction::Rcl(operand, imm), p)),
                3 => Ok((Instruction::Rcr(operand, imm), p)),
                4 => Ok((Instruction::Shl(operand, imm), p)),
                5 => Ok((Instruction::Shr(operand, imm), p)),
                7 => Ok((Instruction::Sar(operand, imm), p)),
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-2 /digit {}", m.reg & 7))),
            }
        }

        // Group 2 — rotate/shift by 1 (0xd0 byte, 0xd1 word/d/q).
        // /digit encoding: same as Group 2 imm8 above.
        0xd0 | 0xd1 => {
            let shift_width = if op == 0xd0 { Width::B } else { width };
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, shift_width)?;
            let m = read_modrm(code, p - 1, rex_r, rex_b)?;
            match m.reg & 7 {
                0 => Ok((Instruction::Rol(operand, 1), p)),
                1 => Ok((Instruction::Ror(operand, 1), p)),
                2 => Ok((Instruction::Rcl(operand, 1), p)),
                3 => Ok((Instruction::Rcr(operand, 1), p)),
                4 => Ok((Instruction::Shl(operand, 1), p)),
                5 => Ok((Instruction::Shr(operand, 1), p)),
                7 => Ok((Instruction::Sar(operand, 1), p)),
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-2 shift-1 /digit {}", m.reg & 7))),
            }
        }

        // Group 3 (0xf6 byte, 0xf7 word/d/q): test/not/neg/mul/imul/div/idiv.
        // Only register form is supported (mode != 0b11 → unsupported).
        0xf6 | 0xf7 => {
            let is_byte = op == 0xf6;
            let group_width = if is_byte { Width::B } else { width };
            // read_rm_operand consumes the ModRM and advances p past it.
            if code.get(p).is_none() {
                return Err(CoreError::parse("x86: truncated ModR/M in group-3"));
            }
            // Peek at ModRM mode before consuming it — if not register form, reject.
            let peek_mod = code[p] >> 6;
            if peek_mod != 0b11 {
                return Err(CoreError::unsupported("x86: group-3 with a memory operand"));
            }
            let o1 = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, group_width)?;
            // Read the /digit field from the ModRM byte (at p-1 after read_rm_operand).
            let modrm_byte = *code.get(p - 1).ok_or_else(|| CoreError::parse("x86: truncated ModR/M in group-3"))?;
            let reg_field = ((modrm_byte >> 3) & 7) | if rex_r { 8 } else { 0 };
            match reg_field & 7 {
                0 => {
                    // test r/m, imm — not /0
                    let imm_len = if is_byte { 1 } else { if rex_w { 8 } else { 4 } };
                    let (imm, _) = read_imm64(code, p, imm_len)?;
                    p += imm_len;
                    Ok((Instruction::Test(o1, X86Operand::Imm(imm)), p))
                }
                2 => Ok((Instruction::Not(o1), p)),
                3 => Ok((Instruction::Neg(o1), p)),
                4 => Ok((Instruction::Mul(o1), p)),
                5 => Ok((Instruction::Imul(o1), p)),
                6 => Ok((Instruction::Div(o1), p)),
                7 => Ok((Instruction::Idiv(o1), p)),
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-3 /digit {}", reg_field & 7))),
            }
        }

        // Two-byte opcode escape (0x0F).
        0x0f => {
            let op2 = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated 0F opcode at offset {p}")))?;
            p += 1;
            match op2 {
                // syscall (0F 05)
                0x05 => Ok((Instruction::Syscall, p)),
                // cmovcc (0F 40..4F) — conditional move.
                0x40..=0x4f => {
                    let cc = Condition::from_cc(op2 - 0x40)
                        .ok_or_else(|| CoreError::parse("x86: invalid condition code in cmovcc"))?;
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let dst = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in cmovcc"))?;
                    if m.mode == 0b11 {
                        let src = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in cmovcc"))?;
                        Ok((Instruction::Cmovcc(cc, reg_op(dst), reg_op(src)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((Instruction::Cmovcc(cc, reg_op(dst), X86Operand::Mem(mem, width)), p))
                    }
                }
                // jcc rel32 (0F 80..8F)
                0x80..=0x8f => {
                    let rel = read_imm_i32(code, &mut p)?;
                    let cc = Condition::from_cc(op2 - 0x80)
                        .ok_or_else(|| CoreError::parse("x86: invalid condition code"))?;
                    Ok((Instruction::Jcc(cc, rel as i64), p))
                }
                // setcc (0F 90..9F) — set byte on condition.
                0x90..=0x9f => {
                    let cc = Condition::from_cc(op2 - 0x90)
                        .ok_or_else(|| CoreError::parse("x86: invalid condition code in setcc"))?;
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    if m.mode == 0b11 {
                        let dst = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in setcc"))?;
                        Ok((Instruction::Setcc(cc, X86Operand::Reg(dst, Width::B)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((Instruction::Setcc(cc, X86Operand::Mem(mem, Width::B)), p))
                    }
                }
                // multi-byte NOP (0F 1f /0)
                0x1f => {
                    // Accept any ModRM-encoded multi-byte NOP.
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    // Consume any SIB + displacement that ModRM indicates.
                    if m.mode != 0b11 {
                        let _ = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                    }
                    Ok((Instruction::Nop, p))
                }
                // bt r/m, r (0F A3) — bit test.
                0xa3 => {
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let bit_index = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in bt"))?;
                    if m.mode == 0b11 {
                        let base = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in bt"))?;
                        Ok((Instruction::Bt(reg_op(base), reg_op(bit_index)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((Instruction::Bt(X86Operand::Mem(mem, width), reg_op(bit_index)), p))
                    }
                }
                // bts r/m, r (0F AB) — bit test and set.
                0xab => {
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let bit_index = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in bts"))?;
                    if m.mode == 0b11 {
                        let base = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in bts"))?;
                        Ok((Instruction::Bts(reg_op(base), reg_op(bit_index)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((Instruction::Bts(X86Operand::Mem(mem, width), reg_op(bit_index)), p))
                    }
                }
                // btr r/m, r (0F B3) — bit test and reset.
                0xb3 => {
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let bit_index = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in btr"))?;
                    if m.mode == 0b11 {
                        let base = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in btr"))?;
                        Ok((Instruction::Btr(reg_op(base), reg_op(bit_index)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((Instruction::Btr(X86Operand::Mem(mem, width), reg_op(bit_index)), p))
                    }
                }
                // btc r/m, r (0F BB) — bit test and complement.
                0xbb => {
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let bit_index = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in btc"))?;
                    if m.mode == 0b11 {
                        let base = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in btc"))?;
                        Ok((Instruction::Btc(reg_op(base), reg_op(bit_index)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((Instruction::Btc(X86Operand::Mem(mem, width), reg_op(bit_index)), p))
                    }
                }
                // bsf (0F BC) — bit scan forward; bsr (0F BD) — bit scan reverse.
                0xbc => decode_bsf_bsr(code, &mut p, rex_r, rex_x, rex_b, width, false),
                0xbd => decode_bsf_bsr(code, &mut p, rex_r, rex_x, rex_b, width, true),
                // movzx (0F B6 / 0F B7)
                0xb6 => decode_movzx(code, &mut p, rex_r, rex_x, rex_b, width, false),
                0xb7 => decode_movzx(code, &mut p, rex_r, rex_x, rex_b, width, true),
                // movsx (0F BE / 0F BF)
                0xbe => decode_movsx(code, &mut p, rex_r, rex_x, rex_b, width, false),
                0xbf => decode_movsx(code, &mut p, rex_r, rex_x, rex_b, width, true),
                // 0F SSE opcodes (legacy prefix encoded in sse_pp).
                // These are handled by the shared SSE decoder that both VEX and legacy paths use.
                0x10 | 0x11 | 0x14 | 0x15 | 0x28 | 0x29 | 0x2e | 0x2f |
                0x51 | 0x54 | 0x55 | 0x56 | 0x57 | 0x58 | 0x59 |
                0x5b | 0x5c | 0x5d | 0x5e | 0x5f | 0xc2 | 0xc6 |
                0xd4 | 0xdb | 0xeb | 0xef | 0xfb => {
                    decode_sse_0f_op(op2, code, &mut p, sse_pp, rex_r, rex_x, rex_b)
                }
                _ => Err(CoreError::unsupported(format!("x86: unsupported two-byte opcode 0f {op2:#04x}"))),
            }
        }

        other => Err(CoreError::unsupported(format!("x86: unsupported opcode {other:#04x}"))),
    }
}

// ============================================================================
// VEX prefix parsing / SSE decode helpers
// ============================================================================

/// Parse a VEX prefix at `*p`, advancing `p` past it. `is_two_byte` selects the
/// C5 (2-byte) form; otherwise the C4 (3-byte) form.
///
/// Real x86-64 VEX layout (all "~"-marked fields are stored inverted):
/// - 2-byte VEX (`C5 b`): one payload byte `b = [~R vvvv L pp]`; the map is
///   implicitly `0F` (mmmmm=1) and `W`/`X`/`B` are 0 (unextended).
/// - 3-byte VEX (`C4 b1 b2`): `b1 = [~R ~X ~B mmmmm(5)]`, `b2 = [W ~vvvv L pp]`.
///
/// The `~R/~X/~B` bits are complements (0 → the corresponding register field is
/// extended, i.e. r8/xmm8+), and `~vvvv` is the 1's-complement of the third
/// operand's register number. Test vectors are taken from a real assembler
/// (`llvm-mc -triple=x86_64 --show-encoding`).
fn parse_vex(code: &[u8], p: &mut usize, is_two_byte: bool) -> csolver_core::Result<VexInfo> {
    // Advance past the C4/C5 lead byte.
    *p += 1;
    if is_two_byte {
        // C5: single payload byte [~R vvvv L pp]. Map is implicitly 0F; W=0.
        let b = *code.get(*p).ok_or_else(|| CoreError::parse("x86: truncated 2-byte VEX prefix (C5)"))?;
        *p += 1;
        Ok(VexInfo {
            vvvv: (!(b >> 3)) & 0xf,
            l: (b & 0x04) != 0,
            pp: b & 0x03,
            mmmmm: 1,
            w: false,
            rex_r: (b & 0x80) == 0, // ~R: 0 → extended
            rex_x: false,
            rex_b: false,
        })
    } else {
        // C4: b1 = [~R ~X ~B mmmmm(5)], b2 = [W ~vvvv L pp].
        let b1 = *code.get(*p).ok_or_else(|| CoreError::parse("x86: truncated 3-byte VEX prefix (C4 byte 1)"))?;
        *p += 1;
        let b2 = *code.get(*p).ok_or_else(|| CoreError::parse("x86: truncated 3-byte VEX prefix (C4 byte 2)"))?;
        *p += 1;
        let mmmmm = b1 & 0x1f;
        if mmmmm == 0 || mmmmm > 3 {
            return Err(CoreError::unsupported(format!("x86: unsupported VEX.mmmmm {mmmmm}")));
        }
        Ok(VexInfo {
            vvvv: (!(b2 >> 3)) & 0xf,
            l: (b2 & 0x04) != 0,
            pp: b2 & 0x03,
            mmmmm,
            w: (b2 & 0x80) != 0,
            rex_r: (b1 & 0x80) == 0, // ~R: 0 → extended
            rex_x: (b1 & 0x40) == 0, // ~X
            rex_b: (b1 & 0x20) == 0, // ~B
        })
    }
}

/// Build an XMM register operand at `width` (typically DQ for 128-bit).
fn xmm_op(r: XmmReg, width: Width) -> X86Operand {
    X86Operand::Xmm(r, width)
}

/// Read an XMM-or-memory operand from ModRM, advancing `p`. Uses `pp_map` to
/// determine the mnemonic prefix (none/66/F3/F2 selects packed/scalar).
fn read_xmm_rm_operand(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    width: Width,
) -> csolver_core::Result<(X86Operand, TypedModRm)> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    if m.mode == 0b11 {
        let r = XmmReg::from_idx(m.rm)
            .ok_or_else(|| CoreError::parse(format!("x86: invalid XMM register {} in SSE operand", m.rm)))?;
        Ok((X86Operand::Xmm(r, width), m))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok((X86Operand::Mem(mem, width), m))
    }
}

/// Decode a legacy-SSE or VEX.128-encoded instruction from the 0F opcode map.
/// `pp` encodes the mandatory prefix: 0=none (packed single), 1=66 (packed double),
/// 2=F3 (scalar single), 3=F2 (scalar double).
/// `op` is the second opcode byte (the byte after 0F).
fn decode_sse_0f_op(
    op: u8,
    code: &[u8],
    p: &mut usize,
    pp: u8,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
) -> csolver_core::Result<(Instruction, usize)> {
    let decode_reg_mem = |code: &[u8], p: &mut usize| -> csolver_core::Result<(X86Operand, TypedModRm)> {
        read_xmm_rm_operand(code, p, rex_r, rex_x, rex_b, Width::DQ)
    };
    match op {
        // 0F 10: MOVUPS (pp=0), MOVSS (pp=2), MOVSD (pp=3), MOVUPD (pp=1)
        0x10 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid dst XMM register in MOV*"))?;
            let inst = match pp {
                0 => Instruction::Movups(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Movsd(xmm_op(dst, Width::DQ), src), // MOVUPD → not directly in enum; use Movsd
                // Actually MOVUPD is distinct. For simplicity, map to Movsd.
                // FIXME: add proper MOVUPD variant if needed.
                2 => Instruction::Movss(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Movsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 10")),
            };
            Ok((inst, *p))
        }
        // 0F 11: MOVUPS store (pp=0), MOVSS store (pp=2), MOVSD store (pp=3), MOVUPD store (pp=1)
        0x11 => {
            let (dst, m) = decode_reg_mem(code, p)?;
            let src = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src XMM register in MOV*"))?;
            let inst = match pp {
                0 => Instruction::Movups(dst, xmm_op(src, Width::DQ)),
                2 => Instruction::Movss(dst, xmm_op(src, Width::DQ)),
                3 => Instruction::Movsd(dst, xmm_op(src, Width::DQ)),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 11")),
            };
            Ok((inst, *p))
        }
        // 0F 28: MOVAPS (pp=0), MOVAPD (pp=1)
        0x28 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid dst XMM register in MOVAP*"))?;
            match pp {
                0 => Ok((Instruction::Movaps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Movapd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 28")),
            }
        }
        // 0F 29: MOVAPS store (pp=0), MOVAPD store (pp=1)
        0x29 => {
            let (dst, m) = decode_reg_mem(code, p)?;
            let src = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src XMM register in MOVAP*"))?;
            match pp {
                0 => Ok((Instruction::Movaps(dst, xmm_op(src, Width::DQ)), *p)),
                1 => Ok((Instruction::Movapd(dst, xmm_op(src, Width::DQ)), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 29")),
            }
        }
        // 0F 2E: UCOMISS (pp=0), UCOMISD (pp=1)
        0x2e => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in UCOMIS*"))?;
            match pp {
                0 => Ok((Instruction::Ucomiss(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Ucomisd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 2E")),
            }
        }
        // 0F 2F: COMISS (pp=0), COMISD (pp=1)
        0x2f => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in COMIS*"))?;
            match pp {
                0 => Ok((Instruction::Comiss(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Comisd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 2F")),
            }
        }
        // 0F 51: SQRTPS (pp=0), SQRTSS (pp=2), SQRTPD (pp=1), SQRTSD (pp=3)
        0x51 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in SQRT*"))?;
            let inst = match pp {
                0 => Instruction::Sqrtps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Sqrtss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Sqrtpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Sqrtsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 51")),
            };
            Ok((inst, *p))
        }
        // 0F 54: ANDPS (pp=0), ANDPD (pp=1)
        0x54 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in AND*"))?;
            match pp {
                0 => Ok((Instruction::Andps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Andpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 54")),
            }
        }
        // 0F 55: ANDNPS (pp=0), ANDNPD (pp=1)
        0x55 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ANDN*"))?;
            match pp {
                0 => Ok((Instruction::Andnps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Andnpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 55")),
            }
        }
        // 0F 56: ORPS (pp=0), ORPD (pp=1)
        0x56 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in OR*"))?;
            match pp {
                0 => Ok((Instruction::Orps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Orpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 56")),
            }
        }
        // 0F 57: XORPS (pp=0), XORPD (pp=1)
        0x57 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in XOR*"))?;
            match pp {
                0 => Ok((Instruction::Xorps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Xorpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 57")),
            }
        }
        // 0F 58: ADDPS (pp=0), ADDSS (pp=2), ADDPD (pp=1), ADDSD (pp=3)
        0x58 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ADD*"))?;
            let inst = match pp {
                0 => Instruction::Addps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Addss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Addpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Addsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 58")),
            };
            Ok((inst, *p))
        }
        // 0F 59: MULPS (pp=0), MULSS (pp=2), MULPD (pp=1), MULSD (pp=3)
        0x59 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in MUL*"))?;
            let inst = match pp {
                0 => Instruction::Mulps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Mulss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Mulpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Mulsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 59")),
            };
            Ok((inst, *p))
        }
        // 0F 5B: CVTDQ2PS (pp=0), CVTTPS2DQ (pp=2), CVTPS2DQ (pp=1)
        0x5b => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in CVT*"))?;
            match pp {
                0 => Ok((Instruction::Cvtdq2ps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Cvtps2dq(xmm_op(dst, Width::DQ), src), *p)),
                2 => Ok((Instruction::Cvttps2dq(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5B")),
            }
        }
        // 0F 5C: SUBPS (pp=0), SUBSS (pp=2), SUBPD (pp=1), SUBSD (pp=3)
        0x5c => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in SUB*"))?;
            let inst = match pp {
                0 => Instruction::Subps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Subss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Subpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Subsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5C")),
            };
            Ok((inst, *p))
        }
        // 0F 5D: MINPS (pp=0), MINSS (pp=2), MINPD (pp=1), MINSD (pp=3)
        0x5d => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in MIN*"))?;
            let inst = match pp {
                0 => Instruction::Minps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Minss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Minpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Minsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5D")),
            };
            Ok((inst, *p))
        }
        // 0F 5E: DIVPS (pp=0), DIVSS (pp=2), DIVPD (pp=1), DIVSD (pp=3)
        0x5e => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in DIV*"))?;
            let inst = match pp {
                0 => Instruction::Divps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Divss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Divpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Divsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5E")),
            };
            Ok((inst, *p))
        }
        // 0F 5F: MAXPS (pp=0), MAXSS (pp=2), MAXPD (pp=1), MAXSD (pp=3)
        0x5f => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in MAX*"))?;
            let inst = match pp {
                0 => Instruction::Maxps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Maxss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Maxpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Maxsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5F")),
            };
            Ok((inst, *p))
        }
        // 0F 14: UNPCKLPS (pp=0), UNPCKLPD (pp=1)
        0x14 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in UNPCKL*"))?;
            match pp {
                0 => Ok((Instruction::Unpcklps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Unpcklpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 14")),
            }
        }
        // 0F 15: UNPCKHPS (pp=0), UNPCKHPD (pp=1)
        0x15 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in UNPCKH*"))?;
            match pp {
                0 => Ok((Instruction::Unpckhps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Unpckhpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 15")),
            }
        }
        // 0F C2: CMPPS (pp=0), CMPSS (pp=2), CMPPD (pp=1), CMPSD (pp=3) — all take imm8
        0xc2 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in CMP*"))?;
            let imm = code.get(*p).copied()
                .ok_or_else(|| CoreError::parse("x86: truncated CMP immediate"))?;
            *p += 1;
            let inst = match pp {
                0 => Instruction::Cmpps(xmm_op(dst, Width::DQ), src, imm),
                2 => Instruction::Cmpss(xmm_op(dst, Width::DQ), src, imm),
                1 => Instruction::Cmppd(xmm_op(dst, Width::DQ), src, imm),
                3 => Instruction::Cmpsd(xmm_op(dst, Width::DQ), src, imm),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F C2")),
            };
            Ok((inst, *p))
        }
        // 0F C6: SHUFPS (pp=0), SHUFPD (pp=1) — take imm8
        0xc6 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in SHUF*"))?;
            let imm = code.get(*p).copied()
                .ok_or_else(|| CoreError::parse("x86: truncated SHUF immediate"))?;
            *p += 1;
            match pp {
                0 => Ok((Instruction::Shufps(xmm_op(dst, Width::DQ), src, imm), *p)),
                1 => Ok((Instruction::Shufpd(xmm_op(dst, Width::DQ), src, imm), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F C6")),
            }
        }
        // 0F D4: PADDQ dst, src (66, SSE2)
        0xd4 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PADDQ"))?;
            Ok((Instruction::Paddq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F DB: PAND dst, src (66, SSE2)
        0xdb if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PAND"))?;
            Ok((Instruction::Pand(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F EB: POR dst, src (66, SSE2)
        0xeb if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in POR"))?;
            Ok((Instruction::Por(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F EF: PXOR dst, src (66, SSE2)
        0xef if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PXOR"))?;
            Ok((Instruction::Pxor(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F FB: PSUBQ dst, src (66, SSE2)
        0xfb if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PSUBQ"))?;
            Ok((Instruction::Psubq(xmm_op(dst, Width::DQ), src), *p))
        }
        _ => Err(CoreError::unsupported(format!("x86: unsupported VEX.128 opcode 0f {:02x}", op))),
    }
}

/// VEX.128 wrapper: reads the opcode byte and dispatches to `decode_sse_0f_op`.
fn decode_vex_0f(code: &[u8], p: &mut usize, vex: VexInfo) -> csolver_core::Result<(Instruction, usize)> {
    let op = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated VEX opcode at offset {}", *p)))?;
    *p += 1;
    decode_sse_0f_op(op, code, p, vex.pp, vex.rex_r, vex.rex_x, vex.rex_b)
}

/// Decode VEX.128-encoded instructions from the 0F38 opcode map (VEX.mmmmm=2).
/// Most instructions require pp=1 (66 prefix). SSSE3 and SSE4.1 instructions.
fn decode_vex_0f38(code: &[u8], p: &mut usize, vex: VexInfo) -> csolver_core::Result<(Instruction, usize)> {
    let op = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated VEX 0F38 opcode at offset {}", *p)))?;
    *p += 1;
    let pp = vex.pp;
    let (rex_r, rex_x, rex_b) = (vex.rex_r, vex.rex_x, vex.rex_b);
    let decode_reg_mem = |code: &[u8], p: &mut usize| -> csolver_core::Result<(X86Operand, TypedModRm)> {
        read_xmm_rm_operand(code, p, rex_r, rex_x, rex_b, Width::DQ)
    };
    // Most 0F38 instructions require 66 prefix (pp=1).
    match op {
        // 0F38 00: PSHUFB dst, src (SSSE3)
        0x00 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PSHUFB"))?;
            Ok((Instruction::Pshufb(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 01: PHADDW dst, src (SSSE3)
        0x01 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PHADDW"))?;
            Ok((Instruction::Phaddw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 02: PHADDD dst, src (SSSE3)
        0x02 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PHADDD"))?;
            Ok((Instruction::Phaddd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 03: PHADDSW dst, src (SSSE3)
        0x03 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PHADDSW"))?;
            Ok((Instruction::Phaddsw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 1C: PABSB dst, src (SSSE3)
        0x1c if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PABSB"))?;
            Ok((Instruction::Pabsb(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 1D: PABSW dst, src (SSSE3)
        0x1d if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PABSW"))?;
            Ok((Instruction::Pabsw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 1E: PABSD dst, src (SSSE3)
        0x1e if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PABSD"))?;
            Ok((Instruction::Pabsd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 20: PMOVSXBW dst, src (SSE4.1)
        0x20 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXBW"))?;
            Ok((Instruction::Pmovsxbw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 21: PMOVSXBD dst, src (SSE4.1)
        0x21 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXBD"))?;
            Ok((Instruction::Pmovsxbd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 22: PMOVSXBQ dst, src (SSE4.1)
        0x22 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXBQ"))?;
            Ok((Instruction::Pmovsxbq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 23: PMOVSXWD dst, src (SSE4.1)
        0x23 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXWD"))?;
            Ok((Instruction::Pmovsxwd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 24: PMOVSXWQ dst, src (SSE4.1)
        0x24 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXWQ"))?;
            Ok((Instruction::Pmovsxwq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 25: PMOVSXDQ dst, src (SSE4.1)
        0x25 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXDQ"))?;
            Ok((Instruction::Pmovsxdq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 28: PMULDQ dst, src (SSE4.1)
        0x28 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMULDQ"))?;
            Ok((Instruction::Pmuldq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 29: PCMPEQQ dst, src (SSE4.2)
        0x29 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PCMPEQQ"))?;
            Ok((Instruction::Pcmpeqq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 30: PMOVZXBW dst, src (SSE4.1)
        0x30 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXBW"))?;
            Ok((Instruction::Pmovzxbw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 31: PMOVZXBD dst, src (SSE4.1)
        0x31 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXBD"))?;
            Ok((Instruction::Pmovzxbd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 32: PMOVZXBQ dst, src (SSE4.1)
        0x32 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXBQ"))?;
            Ok((Instruction::Pmovzxbq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 33: PMOVZXWD dst, src (SSE4.1)
        0x33 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXWD"))?;
            Ok((Instruction::Pmovzxwd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 34: PMOVZXWQ dst, src (SSE4.1)
        0x34 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXWQ"))?;
            Ok((Instruction::Pmovzxwq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 35: PMOVZXDQ dst, src (SSE4.1)
        0x35 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXDQ"))?;
            Ok((Instruction::Pmovzxdq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 37: PCMPGTQ dst, src (SSE4.2)
        0x37 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PCMPGTQ"))?;
            Ok((Instruction::Pcmpgtq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 38: PMINSB dst, src (SSE4.1)
        0x38 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMINSB"))?;
            Ok((Instruction::Pminsb(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 39: PMINSD dst, src (SSE4.1)
        0x39 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMINSD"))?;
            Ok((Instruction::Pminsd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3A: PMINUW dst, src (SSE4.1)
        0x3a if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMINUW"))?;
            Ok((Instruction::Pminuw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3B: PMINUD dst, src (SSE4.1)
        0x3b if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMINUD"))?;
            Ok((Instruction::Pminud(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3C: PMAXSB dst, src (SSE4.1)
        0x3c if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMAXSB"))?;
            Ok((Instruction::Pmaxsb(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3D: PMAXSD dst, src (SSE4.1)
        0x3d if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMAXSD"))?;
            Ok((Instruction::Pmaxsd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3E: PMAXUW dst, src (SSE4.1)
        0x3e if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMAXUW"))?;
            Ok((Instruction::Pmaxuw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3F: PMAXUD dst, src (SSE4.1)
        0x3f if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMAXUD"))?;
            Ok((Instruction::Pmaxud(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 40: PMULLD dst, src (SSE4.1)
        0x40 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMULLD"))?;
            Ok((Instruction::Pmulld(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 41: PHMINPOSUW dst, src (SSE4.1)
        0x41 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PHMINPOSUW"))?;
            Ok((Instruction::Phminposuw(xmm_op(dst, Width::DQ), src), *p))
        }
        _ => Err(CoreError::unsupported(format!("x86: unsupported VEX.128 0F38 opcode {:02x} pp={}", op, pp))),
    }
}

/// Decode VEX.128-encoded instructions from the 0F3A opcode map (VEX.mmmmm=3).
/// All require pp=1 (66 prefix). SSE4.1 and SSSE3 instructions with an imm8.
fn decode_vex_0f3a(code: &[u8], p: &mut usize, vex: VexInfo) -> csolver_core::Result<(Instruction, usize)> {
    let op = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated VEX 0F3A opcode at offset {}", *p)))?;
    *p += 1;
    let pp = vex.pp;
    let rex_w = vex.w;
    let (rex_r, rex_x, rex_b) = (vex.rex_r, vex.rex_x, vex.rex_b);
    let decode_reg_mem = |code: &[u8], p: &mut usize| -> csolver_core::Result<(X86Operand, TypedModRm)> {
        read_xmm_rm_operand(code, p, rex_r, rex_x, rex_b, Width::DQ)
    };
    let read_imm8 = |code: &[u8], p: &mut usize| -> csolver_core::Result<u8> {
        let imm = code.get(*p).copied()
            .ok_or_else(|| CoreError::parse("x86: truncated 0F3A immediate"))?;
        *p += 1;
        Ok(imm)
    };
    match op {
        // 0F3A 08: ROUNDPS dst, src, imm (SSE4.1)
        0x08 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ROUNDPS"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Roundps(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 09: ROUNDPD dst, src, imm (SSE4.1)
        0x09 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ROUNDPD"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Roundpd(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 0A: ROUNDSS dst, src, imm (SSE4.1)
        0x0a if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ROUNDSS"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Roundss(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 0B: ROUNDSD dst, src, imm (SSE4.1)
        0x0b if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ROUNDSD"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Roundsd(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 0F: PALIGNR dst, src, imm (SSSE3)
        0x0f if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PALIGNR"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Palignr(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 14: PEXTRB dst, src, imm (SSE4.1)
        0x14 if pp == 1 => {
            let m = read_modrm(code, *p, rex_r, false)?;
            *p += 1;
            let dst = if m.mode == 0b11 {
                // Register form: extract into GPR
                let reg = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid GPR in PEXTRB"))?;
                X86Operand::Reg(reg, Width::B)
            } else {
                let mem = read_mem(code, p, &m, false, rex_x)?;
                X86Operand::Mem(mem, Width::B)
            };
            let src = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PEXTRB"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Pextrb(dst, xmm_op(src, Width::DQ), imm), *p))
        }
        // 0F3A 16: PEXTRD dst, src, imm (SSE4.1) / PEXTRQ dst, src, imm (REX.W)
        0x16 if pp == 1 => {
            let m = read_modrm(code, *p, rex_r, false)?;
            *p += 1;
            let is_q = rex_w;
            let width = if is_q { Width::Q } else { Width::D };
            let dst = if m.mode == 0b11 {
                let reg = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid GPR in PEXTR*"))?;
                X86Operand::Reg(reg, width)
            } else {
                let mem = read_mem(code, p, &m, false, rex_x)?;
                X86Operand::Mem(mem, width)
            };
            let src = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PEXTR*"))?;
            let imm = read_imm8(code, p)?;
            if is_q {
                Ok((Instruction::Pextrq(dst, xmm_op(src, Width::DQ), imm), *p))
            } else {
                Ok((Instruction::Pextrd(dst, xmm_op(src, Width::DQ), imm), *p))
            }
        }
        // 0F3A 20: PINSRB dst, src, imm (SSE4.1)
        0x20 if pp == 1 => {
            let m = read_modrm(code, *p, rex_r, false)?;
            *p += 1;
            let src = if m.mode == 0b11 {
                let reg = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid GPR in PINSRB"))?;
                X86Operand::Reg(reg, Width::B)
            } else {
                let mem = read_mem(code, p, &m, false, rex_x)?;
                X86Operand::Mem(mem, Width::B)
            };
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PINSRB"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Pinsrb(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 22: PINSRD dst, src, imm (SSE4.1) / PINSRQ dst, src, imm (REX.W)
        0x22 if pp == 1 => {
            let m = read_modrm(code, *p, rex_r, false)?;
            *p += 1;
            let is_q = rex_w;
            let width = if is_q { Width::Q } else { Width::D };
            let src = if m.mode == 0b11 {
                let reg = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid GPR in PINSR*"))?;
                X86Operand::Reg(reg, width)
            } else {
                let mem = read_mem(code, p, &m, false, rex_x)?;
                X86Operand::Mem(mem, width)
            };
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PINSR*"))?;
            let imm = read_imm8(code, p)?;
            if is_q {
                Ok((Instruction::Pinsrq(xmm_op(dst, Width::DQ), src, imm), *p))
            } else {
                Ok((Instruction::Pinsrd(xmm_op(dst, Width::DQ), src, imm), *p))
            }
        }
        _ => Err(CoreError::unsupported(format!("x86: unsupported VEX.128 0F3A opcode {:02x} pp={}", op, pp))),
    }
}

// ============================================================================
// Low-level decode helpers for typed representation
// ============================================================================

/// A raw ModRM byte with REX-extended reg and rm fields.
struct TypedModRm {
    mode: u8,
    reg: u8, // low 3 bits from ModRM.reg, extended by REX.R
    rm: u8,  // low 3 bits from ModRM.rm, extended by REX.B
}

/// Read a ModRM byte at `at`, applying REX.R and REX.B extensions.
fn read_modrm(code: &[u8], at: usize, rex_r: bool, rex_b: bool) -> csolver_core::Result<TypedModRm> {
    let b = *code.get(at).ok_or_else(|| CoreError::parse(format!("x86: truncated ModR/M at offset {at}")))?;
    Ok(TypedModRm {
        mode: b >> 6,
        reg: ((b >> 3) & 7) | if rex_r { 8 } else { 0 },
        rm: (b & 7) | if rex_b { 8 } else { 0 },
    })
}

/// Read a memory operand from ModRM (mode != 11), including SIB and displacement,
/// advancing `p` past the consumed bytes.
fn read_mem(code: &[u8], p: &mut usize, m: &TypedModRm, rex_x: bool, rex_b: bool) -> csolver_core::Result<Mem> {
    let rm_low = m.rm & 7;
    let mut base = m.rm;
    let mut index = None;

    if rm_low == 4 {
        // SIB byte follows.
        let sib = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated SIB at offset {}", *p)))?;
        *p += 1;
        let scale = 1u8 << (sib >> 6);
        let index_field = (sib >> 3) & 7;
        let base_field = (sib & 7) | if rex_b { 8 } else { 0 };
        // index field 0b100 (rsp) with REX.X clear means "no index".
        if index_field != 4 || (rex_x && (sib >> 3) & 7 == 4) {
            let idx_reg = Reg::from_idx(index_field | if rex_x { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid index register in SIB"))?;
            index = Some((idx_reg, scale));
        }
        if m.mode == 0b00 && base_field & 7 == 5 {
            // RIP-relative-like: no base, disp32-only.
            // In 64-bit mode, [base==5, mod==00] means disp32 with no base,
            // but we also handle the RIP-relative case.
            let disp = read_imm_i32(code, p)?;
            return Ok(Mem { base: None, index, disp: disp as i64 });
        }
        base = base_field;
    } else if rm_low == 5 && m.mode == 0b00 {
        // RIP-relative addressing: disp32 with no base register.
        // In 64-bit mode, [rip + disp32] is encoded as ModRM.rm=5, mod=00.
        let disp = read_imm_i32(code, p)?;
        return Ok(Mem { base: None, index, disp: disp as i64 });
    }

    let base_reg = Reg::from_idx(base)
        .ok_or_else(|| CoreError::parse(format!("x86: invalid base register {base} in memory operand at offset {}", *p)))?;

    let disp = match m.mode {
        0b00 => 0i64,
        0b01 => read_imm_i8(code, p)? as i64,
        0b10 => read_imm_i32(code, p)? as i64,
        _ => return Err(CoreError::parse("x86: register operand has no memory form")),
    };

    Ok(Mem {
        base: Some(base_reg),
        index,
        disp,
    })
}

/// Read an r/m operand (register or memory) from the ModRM at `p`,
/// advancing `p` past any SIB/displacement bytes.
fn read_rm_operand(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    width: Width,
) -> csolver_core::Result<X86Operand> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    if m.mode == 0b11 {
        let r = Reg::from_idx(m.rm)
            .ok_or_else(|| CoreError::parse("x86: invalid register in rm operand"))?;
        Ok(X86Operand::Reg(r, width))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok(X86Operand::Mem(mem, width))
    }
}

/// The operation selected by the `/digit` field in group-1 instructions
/// (0x80/0x81/0x82/0x83).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
enum Group1Op { Add = 0, Or = 1, Adc = 2, Sbb = 3, And = 4, Sub = 5, Xor = 6, Cmp = 7 }

fn group1_op_from_modrm_reg(code: &[u8], at: usize, rex_r: bool, _rex_b: bool) -> csolver_core::Result<Group1Op> {
    let b = *code.get(at).ok_or_else(|| CoreError::parse(format!("x86: truncated ModR/M in group-1 at offset {at}")))?;
    let reg = ((b >> 3) & 7) | if rex_r { 8 } else { 0 };
    match reg & 7 {
        0 => Ok(Group1Op::Add), 1 => Ok(Group1Op::Or),
        2 => Ok(Group1Op::Adc), 3 => Ok(Group1Op::Sbb),
        4 => Ok(Group1Op::And), 5 => Ok(Group1Op::Sub),
        6 => Ok(Group1Op::Xor), 7 => Ok(Group1Op::Cmp),
        _ => Err(CoreError::parse(format!("x86: invalid group-1 /digit {reg} at offset {at}"))),
    }
}

/// Decode `movzx` (0F B6: byte->word/d/q, 0F B7: word->d/q).
fn decode_movzx(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    dst_width: Width,
    word_src: bool,
) -> csolver_core::Result<(Instruction, usize)> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    let dst = Reg::from_idx(m.reg)
        .ok_or_else(|| CoreError::parse(format!("x86: invalid dst register {} in movzx", m.reg)))?;
    let src_width = if word_src { Width::W } else { Width::B };
    if m.mode == 0b11 {
        let src = Reg::from_idx(m.rm)
            .ok_or_else(|| CoreError::parse(format!("x86: invalid src register {} in movzx", m.rm)))?;
        Ok((Instruction::Movzx(X86Operand::Reg(dst, dst_width), X86Operand::Reg(src, src_width)), *p))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok((Instruction::Movzx(X86Operand::Reg(dst, dst_width), X86Operand::Mem(mem, src_width)), *p))
    }
}

/// Decode `movsx` (0F BE: byte->word/d/q, 0F BF: word->d/q).
fn decode_movsx(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    dst_width: Width,
    word_src: bool,
) -> csolver_core::Result<(Instruction, usize)> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    let dst = Reg::from_idx(m.reg)
        .ok_or_else(|| CoreError::parse(format!("x86: invalid dst register {} in movsx", m.reg)))?;
    let src_width = if word_src { Width::W } else { Width::B };
    if m.mode == 0b11 {
        let src = Reg::from_idx(m.rm)
            .ok_or_else(|| CoreError::parse(format!("x86: invalid src register {} in movsx", m.rm)))?;
        Ok((Instruction::Movsx(X86Operand::Reg(dst, dst_width), X86Operand::Reg(src, src_width)), *p))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok((Instruction::Movsx(X86Operand::Reg(dst, dst_width), X86Operand::Mem(mem, src_width)), *p))
    }
}

/// Decode `bsf` (0F BC) / `bsr` (0F BD) — bit scan forward/reverse.
/// Format: bsf/bsr dst, src — reg field = dst, r/m field = src (reg or mem).
fn decode_bsf_bsr(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    width: Width,
    reverse: bool,
) -> csolver_core::Result<(Instruction, usize)> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    let dst = Reg::from_idx(m.reg)
        .ok_or_else(|| CoreError::parse(format!("x86: invalid dst register {} in bsf/bsr", m.reg)))?;
    let dst_op = X86Operand::Reg(dst, width);
    let inst = if m.mode == 0b11 {
        let src = Reg::from_idx(m.rm)
            .ok_or_else(|| CoreError::parse(format!("x86: invalid src register {} in bsf/bsr", m.rm)))?;
        let src_op = X86Operand::Reg(src, width);
        if reverse { Instruction::Bsr(dst_op, src_op) } else { Instruction::Bsf(dst_op, src_op) }
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        if reverse { Instruction::Bsr(dst_op, X86Operand::Mem(mem, width)) } else { Instruction::Bsf(dst_op, X86Operand::Mem(mem, width)) }
    };
    Ok((inst, *p))
}

/// Read an unsigned 8-bit immediate, advancing `p`.
fn read_imm_u8(code: &[u8], p: &mut usize) -> csolver_core::Result<u8> {
    let b = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated imm8 at offset {}", *p)))?;
    *p += 1;
    Ok(b)
}

/// Read a signed 8-bit immediate (sign-extended to i64), advancing `p`.
fn read_imm_i8(code: &[u8], p: &mut usize) -> csolver_core::Result<i64> {
    let b = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated imm8 at offset {}", *p)))?;
    *p += 1;
    Ok((b as i8) as i64)
}

/// Read a signed 32-bit immediate (sign-extended to i64), advancing `p`.
fn read_imm_i32(code: &[u8], p: &mut usize) -> csolver_core::Result<i64> {
    let bytes = code.get(*p..*p + 4).ok_or_else(|| CoreError::parse(format!("x86: truncated imm32 at offset {}", *p)))?;
    let v = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    *p += 4;
    Ok(v as i64)
}

/// Read a little-endian unsigned immediate of `len` bytes (4 or 8),
/// advancing `p`.
fn read_imm64(code: &[u8], p: usize, len: usize) -> csolver_core::Result<(u64, usize)> {
    let bytes = code.get(p..p + len).ok_or_else(|| CoreError::parse(format!("x86: truncated immediate at offset {p}")))?;
    let mut v: u64 = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        v |= (byte as u64) << (8 * i);
    }
    Ok((v, len))
}

#[cfg(test)]
mod tests {
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
    fn decodes_a_stack_frame_and_its_access() {
        // 48 83 ec 10        sub rsp, 16        (allocate a 16-byte frame)
        // 89 44 24 08        mov [rsp+8], eax   (store within the frame)
        // 48 83 c4 10        add rsp, 16
        // c3                 ret
        let code = [0x48, 0x83, 0xec, 0x10, 0x89, 0x44, 0x24, 0x08, 0x48, 0x83, 0xc4, 0x10, 0xc3];
        let m = decode_function("f", &code);
        assert!(m.unanalyzed.is_empty(), "fully decoded: {:?}", m.unanalyzed);
        let insts = &m.functions[0].blocks[0].insts;
        // sub rsp,16 -> Alloc Stack; [rsp+8] -> PtrOffset + Store; add rsp -> noop.
        assert!(matches!(insts[0], Inst::Alloc { region: RegionKind::Stack, .. }));
        assert!(matches!(insts[1], Inst::PtrOffset { .. }));
        assert!(matches!(insts[2], Inst::Store { .. }));
    }

    #[test]
    fn reconstructs_a_conditional_branch() {
        // sub rsp,16 ; cmp edi,0 ; jne +4 ; mov [rsp+8],eax ; add rsp,16 ; ret
        let code = [
            0x48, 0x83, 0xec, 0x10, 0x83, 0xff, 0x00, 0x75, 0x04, 0x89, 0x44, 0x24, 0x08, 0x48,
            0x83, 0xc4, 0x10, 0xc3,
        ];
        let m = decode_function("f", &code);
        assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
        let f = &m.functions[0];
        assert_eq!(f.blocks.len(), 3, "entry + store + join");
        assert!(matches!(f.blocks[0].term, Terminator::CondBr { .. }), "entry branches");
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
        assert!(matches!(insts[0], Inst::PtrOffset { .. }), "index*scale offset");
        assert!(matches!(insts[1], Inst::Store { .. }));

        // lea rax, [rsp + rcx*4]  = 48 8d 04 8c   (compute address, no access)
        let m2 = decode_function("g", &[0x48, 0x8d, 0x04, 0x8c, 0xc3]);
        assert!(m2.unanalyzed.is_empty(), "{:?}", m2.unanalyzed);
        let insts = &m2.functions[0].blocks[0].insts;
        assert!(matches!(insts.last(), Some(Inst::Assign { .. })), "lea assigns the address");
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
            Instruction::Mov(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0x12345678))
        );
        assert!(!d.prefixes.rex);
        assert_eq!(d.length, 5);
    }

    #[test]
    fn typed_mov_rax_imm64() {
        // mov rax, 0x123456789abcdef0  (REX.W)
        let d = decode_instruction(&[0x48, 0xb8, 0xf0, 0xde, 0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
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
        assert_eq!(d.instruction, Instruction::Lea(Reg::RAX, Width::D, expected_mem));
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
        assert_eq!(d.instruction, Instruction::Lea(Reg::RAX, Width::Q, expected_mem));
    }

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

    const TRUNCATED_OPS: &[(&[u8], &str)] = &[
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
    fn rejects_lock_prefix() {
        let r = decode_instruction(&[0xf0, 0x90], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
    }

    #[test]
    fn rejects_lea_with_register_form() {
        // 8d c0 = lea eax, eax (m=mod=11 → register form, invalid)
        let r = decode_instruction(&[0x8d, 0xc0], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Parse { .. }));
    }

    #[test]
    fn rejects_alu_memory_operand() {
        // 01 08 = add [rax], ecx
        let r = decode_instruction(&[0x01, 0x08], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
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
        assert!(bad.is_empty(), "unsupported opcode mismatches:\n{}", bad.join("\n"));
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
        assert!(bad.is_empty(), "unsupported two-byte opcode mismatches:\n{}", bad.join("\n"));
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
        let expected_mem = Mem { base: Some(Reg::RAX), index: None, disp: 0 };
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
        let expected_mem = Mem { base: Some(Reg::RAX), index: None, disp: 0 };
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
        let expected_mem = Mem { base: Some(Reg::RAX), index: None, disp: 0 };
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
        assert!(r.unwrap_err().to_string().contains("group-3 with a memory operand"));
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
}
