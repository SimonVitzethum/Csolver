//! # csolver-elf — object-file loader (pure Rust, no external crates)
//!
//! A from-scratch ELF64 reader: it parses the header, the section table,
//! program headers, the symbol table, and relocations, exposing exactly the
//! context the assembly frontend and the memory model need — sections (with
//! permissions and where their bytes live), symbols (functions and their code),
//! and program segments. This is the entry point for verifying a *compiled
//! binary* with no source: load the image, locate a function, hand its bytes to
//! the decoder.
//!
//! ## Scope
//!
//! ELF64, little-endian (x86-64 / AArch64). Parsing is **bounds-checked
//! throughout** — a truncated or malformed image yields [`csolver_core::Error`],
//! never a panic, because the loader is the trust boundary between an untrusted
//! file and the analysis. PE / Mach-O, DWARF debug info, and the PLT/GOT are
//! later increments; this layer already lets the pipeline enumerate functions,
//! recover their machine code, and parse relocation metadata.

use csolver_core::{Error, RegionKind, Result};
use std::convert::TryFrom;


// --- module split (mechanical refactor) ---
mod aux;
mod consts;
mod load;
mod reloc;
mod types;
#[cfg(test)]
#[path = "elf_tests.rs"]
mod tests;
#[cfg(test)]
#[path = "elf_tests2.rs"]
mod tests2;
pub use aux::gnu_hash;
pub use consts::{r_aarch64, r_x86_64};
pub use load::{load, EM_AARCH64, EM_X86_64};
pub use reloc::*;
pub use types::*;
use aux::*;
use consts::*;

/// A focused DWARF `.debug_info` reader for recovering pointer-parameter pointee sizes.
pub mod dwarf;
pub use dwarf::parameter_pointee_sizes;

// --- Load an ELF64 (little-endian) object image from raw bytes --------------

