//! # csolver-elf — multi-format object-file loader (pure Rust, no external crates)
//!
//! A from-scratch reader for the three mainstream object formats — **ELF** (Linux),
//! **PE/COFF** (Windows), and **Mach-O** (macOS/iOS) — behind one format-agnostic
//! entry point, [`load_object`], which sniffs the leading magic and dispatches. Each
//! parser produces the same [`Image`]: sections (with permissions and where their bytes
//! live), symbols (functions and their code), and — for ELF — segments, relocations,
//! dynamic info and DWARF. So verifying a *compiled binary with no source* — a Linux
//! `.o`, a Windows `.dll`, a macOS Mach-O — runs the SAME decode + verify pipeline; only
//! the front matter (headers, symbol/export discovery) differs per OS.
//!
//! ## Scope
//!
//! 64-bit little-endian x86-64 / AArch64 (the architectures the decoders handle) across
//! all three formats. Parsing is **bounds-checked throughout** — a truncated or malformed
//! image yields [`csolver_core::Error`], never a panic, because the loader is the trust
//! boundary between an untrusted file and the analysis.
//!
//! * **ELF** (`load`, [`mod@dwarf`]): header, sections, program headers, symbols,
//!   relocations (x86-64/AArch64), dynamic section, GNU/SysV hash, versioning, notes,
//!   and a focused DWARF `.debug_info` reader (pointer-parameter pointee sizes).
//! * **PE/COFF** ([`mod@pe`]): DOS/PE/COFF/optional headers, sections, the COFF symbol
//!   table (objects) and the export directory (linked `.exe`/`.dll`/`.sys`).
//! * **Mach-O** ([`mod@macho`]): the 64-bit header (or the x86-64/arm64 slice of a fat
//!   binary), `LC_SEGMENT_64` sections and the `LC_SYMTAB` symbol table.
//!
//! ELF32 and big-endian ELF are parsed by a class/endian-generic reader (core fields only;
//! DWARF/hash/version auxiliaries stay on the ELF64-LE fast path). Not covered (lower value
//! for the kernel/systems focus): PE base-relocation and Mach-O relocation application (so
//! RIP-relative globals resolve only for ELF's per-symbol relocations), PDB / CFI, and
//! compressed debug sections. A `.debug_line` reader is in [`mod@dwarf_line`].

use csolver_core::{Error, RegionKind, Result};
use std::convert::TryFrom;


// --- module split (mechanical refactor) ---
mod aux;
mod consts;
pub mod iso;
mod load;
mod load_generic;
mod lzx;
pub mod udf;
pub mod wim;
pub mod macho;
pub mod pe;
mod reloc;
mod types;
#[cfg(test)]
#[path = "elf_tests.rs"]
mod tests;
#[cfg(test)]
#[path = "elf_tests2.rs"]
mod tests2;
#[cfg(test)]
#[path = "elf_tests3.rs"]
mod tests3;
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

/// A focused DWARF `.debug_line` reader (instruction address → source line).
pub mod dwarf_line;
pub use dwarf_line::{line_at, line_rows};

/// The object-file format of a byte image.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Format {
    /// ELF (Linux / BSD / bare-metal).
    Elf,
    /// PE/COFF (Windows `.exe`/`.dll`/`.sys`/`.obj`).
    Pe,
    /// Mach-O (macOS / iOS), thin or universal.
    MachO,
}

/// Sniff the object-file format from the leading magic bytes.
pub fn detect_format(bytes: &[u8]) -> Option<Format> {
    if bytes.starts_with(&[0x7f, b'E', b'L', b'F']) {
        Some(Format::Elf)
    } else if pe::is_pe(bytes) {
        Some(Format::Pe)
    } else if macho::is_macho(bytes) {
        Some(Format::MachO)
    } else {
        None
    }
}

/// Load ANY supported object file (ELF / PE / Mach-O) into the common [`Image`],
/// dispatching on the leading magic. This is the format-agnostic entry point the
/// binary-verification pipeline uses — the assembly frontend then decodes a function
/// the same way regardless of which OS produced it.
pub fn load_object(bytes: &[u8]) -> Result<Image> {
    match detect_format(bytes) {
        Some(Format::Elf) => load(bytes),
        Some(Format::Pe) => pe::load(bytes),
        Some(Format::MachO) => macho::load(bytes),
        None => Err(Error::unsupported(
            "unrecognized object file (expected ELF, PE/COFF, or Mach-O magic)",
        )),
    }
}

// --- Load an ELF64 (little-endian) object image from raw bytes --------------

