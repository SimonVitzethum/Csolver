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
//! The **textual-assembly** entry point [`AsmFrontend::lower`] handles
//! **AT&T-syntax x86-64** (`clang/gcc -S`) via [`att::decode_att`] — a focused
//! common-instruction subset that reuses the CFG assembly and register helpers;
//! an unrecognised mnemonic drops its function to `unanalyzed` (sound). Intel
//! syntax and textual AArch64 are not supported yet (use an ELF object).

mod att;
mod blocks;
pub mod arm64;
pub mod x86;

pub use att::decode_att;
pub use x86::decode_function;

use csolver_core::{Error, Result};
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
        match (input.arch, input.syntax) {
            // Textual AT&T-syntax x86-64 (`clang/gcc -S` default on Linux).
            (Architecture::X86_64, Syntax::Att) => Ok(att::decode_att(&input.source)),
            (Architecture::X86_64, Syntax::Intel) => Err(Error::unsupported(
                "asm: Intel-syntax textual assembly is not supported yet (use AT&T, or an ELF object)",
            )),
            (Architecture::AArch64, _) => Err(Error::unsupported(
                "asm: textual AArch64 assembly is not supported yet (use an ELF object)",
            )),
        }
    }
}
