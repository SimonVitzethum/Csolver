use super::*;

/// A loaded section (a contiguous image segment with permissions).
#[derive(Debug, Clone)]
pub struct Section {
    /// Section name (e.g. `.text`, `.rodata`, `.bss`).
    pub name: String,
    /// Virtual address.
    pub address: u64,
    /// Size in bytes.
    pub size: u64,
    /// Offset of the section's bytes within the file (0 for `.bss`/`NOBITS`).
    pub file_offset: u64,
    /// Whether the section occupies file bytes (`false` for `.bss`/`NOBITS`).
    pub has_data: bool,
    /// Whether it is writable.
    pub writable: bool,
    /// Whether it is executable.
    pub executable: bool,
    /// Whether the section data is compressed.
    pub compressed: bool,
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
    /// Section index (SHN_UNDEF = 0, or a 1-based section-table index).
    pub section_index: u16,
}

/// A program-header (segment) entry.
#[derive(Debug, Clone)]
pub struct ProgramHeader {
    /// Segment type (PT_LOAD = 1, PT_DYNAMIC = 2, PT_INTERP = 3, etc.).
    pub kind: u32,
    /// Segment flags (PF_R = 4, PF_W = 2, PF_X = 1).
    pub flags: u32,
    /// Offset within the file image.
    pub offset: u64,
    /// Virtual address of the segment.
    pub vaddr: u64,
    /// Physical address (often equal to vaddr).
    pub paddr: u64,
    /// Size of the segment in the file image.
    pub file_size: u64,
    /// Size of the segment in memory (may be larger than `file_size` for `.bss`).
    pub mem_size: u64,
    /// Alignment constraint (0 or power of 2).
    pub align: u64,
}

/// A single relocation entry.
#[derive(Debug, Clone)]
pub struct Relocation {
    /// Offset (virtual address or section-relative, depending on type).
    pub offset: u64,
    /// Relocation type (architecture-specific constants like R_X86_64_64).
    pub kind: u32,
    /// Symbol index (0-based into the symbol table) or special value.
    pub symbol: u32,
    /// Addend (for `RELA`-format entries).
    pub addend: i64,
}

/// A parsed object image.
#[derive(Debug, Clone, Default)]
pub struct Image {
    /// The `e_machine` architecture id (`EM_X86_64` = 62, `EM_AARCH64` = 183) —
    /// selects which machine-code decoder interprets a function's bytes.
    pub machine: u16,
    /// The object's sections.
    pub sections: Vec<Section>,
    /// The object's symbols.
    pub symbols: Vec<Symbol>,
    /// The object's program headers (segments).
    pub program_headers: Vec<ProgramHeader>,
    /// Relocation entries, indexed by the section they apply to (section index).
    /// Only populated for sections that hold relocation entries (SHT_RELA).
    pub relocations: Vec<(usize, Vec<Relocation>)>,
    /// Dynamic-section entries (from `SHT_DYNAMIC` / `PT_DYNAMIC`).
    pub dynamic_entries: Vec<DynamicEntry>,
    /// Entry-point virtual address, if any.
    pub entry: Option<u64>,
    /// Parsed GNU hash table, if present.
    pub gnu_hash: Option<GnuHash>,
    /// Parsed SysV hash table (`.hash` / `SHT_HASH`), if present.
    /// The tuple is `(buckets, chains)`.
    pub sysv_hash: Option<(Vec<u32>, Vec<u32>)>,
    /// Parsed ELF notes (build ID, ABI tag, etc.).
    pub notes: Vec<Note>,
    /// Version-definition entries (from `SHT_GNU_verdef`).
    pub verdefs: Vec<VerDef>,
    /// Version-need entries (from `SHT_GNU_verneed`).
    pub verneeds: Vec<VerNeed>,
}

impl Image {
    /// The first section whose virtual-address range contains `addr`.
    /// Uses saturating arithmetic so an `addr + size` at the numeric boundary
    /// never panics.
    pub fn section_at(&self, addr: u64) -> Option<&Section> {
        self.sections.iter().find(|s| {
            s.size > 0
                && addr >= s.address
                && addr < s.address.saturating_add(s.size)
        })
    }

    /// The machine-code bytes of `sym` (a function), sliced from the original
    /// image `bytes`. `None` if the symbol is sizeless, not backed by file data,
    /// or out of range.
    pub fn function_code<'a>(&self, sym: &Symbol, bytes: &'a [u8]) -> Option<&'a [u8]> {
        if sym.size == 0 {
            return None;
        }
        // Resolve the symbol's section by its `st_shndx` INDEX, not by address:
        // in a relocatable object (`.o`) every section has address 0, so an
        // address lookup is ambiguous and slices the wrong bytes. `image.sections`
        // is parsed 1:1 with the section-header table (index 0 = the NULL section),
        // so `section_index` indexes it directly; special indices (`SHN_ABS`/… ≥
        // 0xff00) fall out of range and yield `None`.
        let sec = self.sections.get(sym.section_index as usize)?;
        if !sec.has_data || sec.compressed {
            return None;
        }
        // Offset of the symbol within its section (address-relative; 0-based in a
        // `.o` where `sec.address == 0`, vaddr-relative in a linked image).
        let in_sec_off = sym.address.checked_sub(sec.address)?;
        // sym.address + sym.size must stay within sec.address + sec.size.
        let sec_end = sec.address.checked_add(sec.size)?;
        let sym_end = sym.address.checked_add(sym.size)?;
        if sym_end > sec_end {
            return None;
        }
        let start = sec.file_offset.checked_add(in_sec_off)?;
        let end = start.checked_add(sym.size)?;
        let start_us = usize::try_from(start).ok()?;
        let end_us = usize::try_from(end).ok()?;
        bytes.get(start_us..end_us)
    }

    /// The defined function symbols, in image order.
    pub fn functions(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols.iter().filter(|s| s.is_function && s.size > 0)
    }

    /// The raw file bytes of the named section (e.g. `.debug_info`), sliced from the
    /// original image `bytes`. `None` if absent, `NOBITS`, or out of range.
    pub fn section_bytes_by_name<'a>(&self, name: &str, bytes: &'a [u8]) -> Option<&'a [u8]> {
        let s = self.sections.iter().find(|s| s.name == name && s.has_data && s.size > 0)?;
        let start = usize::try_from(s.file_offset).ok()?;
        let end = start.checked_add(usize::try_from(s.size).ok()?)?;
        bytes.get(start..end)
    }
}

// --- ELF constants ---------------------------------------------------------
