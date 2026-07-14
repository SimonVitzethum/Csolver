use super::*;

impl Reg {
    /// Convert a 4-bit register index (0..15) into a [`Reg`]. The index
    /// combines the raw 3-bit encoding field with a REX extension bit
    /// (e.g. `low3 | if rex_bit { 8 } else { 0 }`).
    pub(crate) fn from_idx(idx: u8) -> Option<Reg> {
        match idx {
            0 => Some(Reg::RAX),
            1 => Some(Reg::RCX),
            2 => Some(Reg::RDX),
            3 => Some(Reg::RBX),
            4 => Some(Reg::RSP),
            5 => Some(Reg::RBP),
            6 => Some(Reg::RSI),
            7 => Some(Reg::RDI),
            8 => Some(Reg::R8),
            9 => Some(Reg::R9),
            10 => Some(Reg::R10),
            11 => Some(Reg::R11),
            12 => Some(Reg::R12),
            13 => Some(Reg::R13),
            14 => Some(Reg::R14),
            15 => Some(Reg::R15),
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
    pub(crate) fn bytes(self) -> u64 {
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
    pub(crate) fn bits(self) -> u64 {
        self.bytes() * 8
    }

    /// Infer the width from a REX.W bit and the operation code. For most
    /// ALU ops, !REX.W → 32-bit, REX.W → 64-bit.
    pub(crate) fn from_rex_w(rex_w: bool) -> Width {
        if rex_w {
            Width::Q
        } else {
            Width::D
        }
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
    XMM0 = 0,
    XMM1 = 1,
    XMM2 = 2,
    XMM3 = 3,
    XMM4 = 4,
    XMM5 = 5,
    XMM6 = 6,
    XMM7 = 7,
    XMM8 = 8,
    XMM9 = 9,
    XMM10 = 10,
    XMM11 = 11,
    XMM12 = 12,
    XMM13 = 13,
    XMM14 = 14,
    XMM15 = 15,
}

impl XmmReg {
    pub(crate) fn from_idx(idx: u8) -> Option<XmmReg> {
        match idx {
            0 => Some(XmmReg::XMM0),
            1 => Some(XmmReg::XMM1),
            2 => Some(XmmReg::XMM2),
            3 => Some(XmmReg::XMM3),
            4 => Some(XmmReg::XMM4),
            5 => Some(XmmReg::XMM5),
            6 => Some(XmmReg::XMM6),
            7 => Some(XmmReg::XMM7),
            8 => Some(XmmReg::XMM8),
            9 => Some(XmmReg::XMM9),
            10 => Some(XmmReg::XMM10),
            11 => Some(XmmReg::XMM11),
            12 => Some(XmmReg::XMM12),
            13 => Some(XmmReg::XMM13),
            14 => Some(XmmReg::XMM14),
            15 => Some(XmmReg::XMM15),
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
    O,
    NO,
    B,
    AE,
    E,
    NE,
    BE,
    A,
    S,
    NS,
    P,
    NP,
    L,
    GE,
    LE,
    G,
}
