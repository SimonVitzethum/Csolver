//! # csolver-elf — object-file loader (M0 stub)
//!
//! Parses ELF (and later PE / Mach-O) images and exposes the context the
//! assembly frontend and the memory model need: sections and their
//! permissions, the symbol table, relocations, DWARF debug info (stack layout,
//! types, line tables), the PLT/GOT, TLS template, and `.eh_frame`/exception
//! tables.
//!
//! ## Status
//!
//! Interface only. [`load`] reports [`csolver_core::Error::Unsupported`]. The
//! real implementation (milestone M4) will use the pure-Rust `object` and
//! `gimli` crates — introduced here as the first external dependencies, and
//! justified in `Verification/Assumptions.md`.

use csolver_core::{Error, RegionKind, Result};

/// A loaded section (a contiguous image segment with permissions).
#[derive(Debug, Clone)]
pub struct Section {
    /// Section name (e.g. `.text`, `.rodata`, `.bss`).
    pub name: String,
    /// Virtual address.
    pub address: u64,
    /// Size in bytes.
    pub size: u64,
    /// Whether it is writable.
    pub writable: bool,
    /// Whether it is executable.
    pub executable: bool,
    /// The memory region kind this section maps to.
    pub region: RegionKind,
}

/// A symbol-table entry.
#[derive(Debug, Clone)]
pub struct Symbol {
    /// Symbol name.
    pub name: String,
    /// Virtual address / value.
    pub address: u64,
    /// Size in bytes, if known.
    pub size: u64,
    /// Whether it denotes a function.
    pub is_function: bool,
}

/// A parsed object image.
#[derive(Debug, Clone, Default)]
pub struct Image {
    /// The object's sections.
    pub sections: Vec<Section>,
    /// The object's symbols.
    pub symbols: Vec<Symbol>,
    /// Entry-point virtual address, if any.
    pub entry: Option<u64>,
}

/// Load an object image from raw bytes.
pub fn load(_bytes: &[u8]) -> Result<Image> {
    Err(Error::unsupported(
        "ELF/PE/Mach-O loading is not implemented yet (planned milestone M4)",
    ))
}
