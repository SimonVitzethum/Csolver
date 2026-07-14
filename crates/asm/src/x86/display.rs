use super::*;
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
pub(crate) fn fmt_binary(
    f: &mut fmt::Formatter<'_>,
    mnemonic: &str,
    dst: &X86Operand,
    src: &X86Operand,
) -> fmt::Result {
    write!(f, "{mnemonic} {dst}, {src}")
}

/// Helper: format a two-operand-with-immediate instruction `mnemonic dst, src, imm`.
pub(crate) fn fmt_ternary(
    f: &mut fmt::Formatter<'_>,
    mnemonic: &str,
    a: &X86Operand,
    b: &X86Operand,
    imm: u8,
) -> fmt::Result {
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
            Instruction::Movupd(d, s) => fmt_binary(f, "movupd", d, s),
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
