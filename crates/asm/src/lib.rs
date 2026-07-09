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
//! The **textual-assembly** entry point [`AsmFrontend::lower`] (a `.s` source or
//! a C inline-asm template → MSIR) is still a stub — it reports
//! [`csolver_core::Error::Unsupported`] (planned milestone M4). Until it exists,
//! a C inline-asm block is an opaque havoc in the executor.

mod blocks;
pub mod arm64;
pub mod x86;

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

    fn lower(&self, _input: AsmInput) -> Result<Module> {
        Err(Error::unsupported(
            "assembly lowering is not implemented yet (planned milestone M4)",
        ))
    }
}
