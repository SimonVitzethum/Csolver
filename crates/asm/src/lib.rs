//! # csolver-asm — machine-assembly frontend
//!
//! Lowers x86-64 (Intel and AT&T syntax) and AArch64 assembly into MSIR. At the
//! machine level the memory model becomes the flat byte space; registers,
//! flags, and the stack pointer are modelled explicitly, and DWARF (from
//! `csolver-elf`) supplies stack-frame layout and types.
//!
//! ## Status
//!
//! The **machine-code (byte) decoders** are functional: [`x86::decode_function`]
//! and [`arm64::decode_function`] lower a `.text` function (bytes) into MSIR,
//! reconstructing its CFG (~197 x86 mnemonics incl. VEX/EVEX/ModRM/SIB).
//!
//! The **textual-assembly** entry point [`AsmFrontend::lower`] handles all four
//! combinations: **x86-64 in AT&T *and* Intel syntax** ([`x86text`]) and
//! **textual AArch64** ([`arm64_text`]), each a focused common-instruction subset
//! that reuses the CFG assembly and register helpers. An unrecognised mnemonic or
//! operand drops its function to `unanalyzed` (sound — never a guess). The
//! architecture and (for x86) syntax are auto-detected from the source when not
//! given explicitly (see [`detect`]).

pub mod arm64;
pub mod arm64_text;
mod blocks;
pub mod x86;
pub mod x86text;

pub use arm64_text::decode as decode_arm64_text;
pub use x86::decode_function;
pub use x86text::{decode_att, decode_intel};

use csolver_core::Result;
use csolver_ir::{Frontend, Module};

/// Target instruction-set architecture.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Architecture {
    /// x86-64 (AMD64).
    X86_64,
    /// AArch64 (ARM64).
    AArch64,
}

/// Assembly textual syntax (x86 only).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Syntax {
    /// Intel syntax (`mov rax, rbx`).
    Intel,
    /// AT&T syntax (`movq %rbx, %rax`).
    Att,
}

/// Assembly source input.
#[derive(Debug, Clone)]
pub struct AsmInput {
    /// The assembly text.
    pub source: String,
    /// Target architecture.
    pub arch: Architecture,
    /// Syntax (ignored for AArch64).
    pub syntax: Syntax,
}

/// The assembly frontend.
#[derive(Debug, Default, Clone, Copy)]
pub struct AsmFrontend;

impl Frontend for AsmFrontend {
    type Input = AsmInput;

    fn name(&self) -> &'static str {
        "asm"
    }

    fn lower(&self, input: AsmInput) -> Result<Module> {
        Ok(match (input.arch, input.syntax) {
            (Architecture::X86_64, Syntax::Att) => x86text::decode_att(&input.source),
            (Architecture::X86_64, Syntax::Intel) => x86text::decode_intel(&input.source),
            (Architecture::AArch64, _) => arm64_text::decode(&input.source),
        })
    }
}

/// Auto-detect the `(architecture, syntax)` of a textual `.s` translation unit
/// from its content, so a caller need not know it up front:
///
/// * **AArch64** if AArch64-only cues appear — an `.arch armv8` directive, a
///   `:lo12:` relocation, an AArch64-only mnemonic (`adrp`/`ldp`/`stp`/`b.`/…),
///   an `x`/`w`/`sp` register operand, or a `#`-prefixed immediate — and no
///   x86-style `%reg`;
/// * **Intel** x86 if an `.intel_syntax` directive is present or memory operands
///   use `[...]` with no `%`-prefixed registers; otherwise **AT&T** x86 (the
///   `%reg`/`$imm` default of `clang/gcc -S` on Linux).
pub fn detect(source: &str) -> (Architecture, Syntax) {
    let has_percent = source.contains('%');
    let intel_directive = source.contains(".intel_syntax");
    if !has_percent
        && (source.contains(".arch armv8") || source.contains(":lo12:") || looks_like_arm(source))
    {
        return (Architecture::AArch64, Syntax::Att);
    }
    let syntax = if intel_directive || (!has_percent && source.contains('[')) {
        Syntax::Intel
    } else {
        Syntax::Att
    };
    (Architecture::X86_64, syntax)
}

/// Whether the instruction lines look like AArch64: an AArch64-only mnemonic, a
/// `#`-prefixed immediate operand, or an `x`/`w`/`sp` register operand (none of
/// which appear in x86 AT&T or Intel output).
fn looks_like_arm(source: &str) -> bool {
    source.lines().any(|l| {
        let t = l.trim();
        if t.is_empty() || t.starts_with('.') || t.ends_with(':') {
            return false;
        }
        let (mnem, rest) = t.split_once(char::is_whitespace).unwrap_or((t, ""));
        matches!(
            mnem,
            "adrp" | "adr" | "ldp" | "stp" | "cbz" | "cbnz" | "ldrsw"
        ) || mnem.starts_with("b.")
            || rest.contains(", #")
            || rest.contains(", [")
            || rest.split([',', ' ', '[', ']', '\t']).any(is_arm_reg)
    })
}

/// Whether `tok` is an AArch64 GP register name (`x0..x30`, `w0..w30`, `sp`,
/// `xzr`/`wzr`, `lr`, `fp`).
fn is_arm_reg(tok: &str) -> bool {
    let t = tok.trim();
    if matches!(t, "sp" | "xzr" | "wzr" | "lr" | "fp") {
        return true;
    }
    match t.strip_prefix(['x', 'w']) {
        Some(d) if !d.is_empty() => d.parse::<u8>().is_ok_and(|n| n <= 30),
        _ => false,
    }
}
