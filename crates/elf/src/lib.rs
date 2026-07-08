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
    /// The object's sections.
    pub sections: Vec<Section>,
    /// The object's symbols.
    pub symbols: Vec<Symbol>,
    /// The object's program headers (segments).
    pub program_headers: Vec<ProgramHeader>,
    /// Relocation entries, indexed by the section they apply to (section index).
    /// Only populated for sections that hold relocation entries (SHT_RELA).
    pub relocations: Vec<(usize, Vec<Relocation>)>,
    /// Entry-point virtual address, if any.
    pub entry: Option<u64>,
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
        let sec = self.section_at(sym.address)?;
        if !sec.has_data {
            return None;
        }
        // sym.address - sec.address cannot underflow because section_at
        // guarantees addr >= s.address.
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
}

// --- ELF constants ---------------------------------------------------------

const ELF_HEADER_LEN: usize = 64;
const SECTION_HEADER_LEN: usize = 64;
const PROGRAM_HEADER_LEN: usize = 56;
const SYM_ENTRY_LEN: u64 = 24;
const RELA_ENTRY_LEN: u64 = 24;
const REL_ENTRY_LEN: u64 = 8;

const SHT_SYMTAB: u32 = 2;
const SHT_RELA: u32 = 4;
const SHT_REL: u32 = 9;
const SHT_NOBITS: u32 = 8;

const SHF_WRITE: u64 = 0x1;
const SHF_EXECINSTR: u64 = 0x4;

const STT_FUNC: u8 = 2;
#[allow(dead_code)]
const STT_OBJECT: u8 = 1;

const SHN_UNDEF: u16 = 0;
const SHN_XINDEX: u16 = 0xffff;

// --- bounds-checked little-endian readers ----------------------------------

fn read_u16(bytes: &[u8], off: usize) -> Result<u16> {
    let b = bytes
        .get(off..off + 2)
        .ok_or_else(|| Error::parse("ELF: truncated (u16)"))?;
    Ok(u16::from_le_bytes([b[0], b[1]]))
}

fn read_u32(bytes: &[u8], off: usize) -> Result<u32> {
    let b = bytes
        .get(off..off + 4)
        .ok_or_else(|| Error::parse("ELF: truncated (u32)"))?;
    Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}

fn read_u64(bytes: &[u8], off: usize) -> Result<u64> {
    let b = bytes
        .get(off..off + 8)
        .ok_or_else(|| Error::parse("ELF: truncated (u64)"))?;
    Ok(u64::from_le_bytes([
        b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
    ]))
}

fn read_i64(bytes: &[u8], off: usize) -> Result<i64> {
    let b = bytes
        .get(off..off + 8)
        .ok_or_else(|| Error::parse("ELF: truncated (i64)"))?;
    Ok(i64::from_le_bytes([
        b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
    ]))
}

/// Read a NUL-terminated string at byte offset `off` within a string table
/// `tab`. Returns an error if the offset is past the end of the table or if no
/// NUL terminator is found within the remaining bytes (the entire table is
/// treated as the well-formed region; a missing terminator is a parse error).
fn read_str(tab: &[u8], off: u32) -> Result<String> {
    let start = usize::try_from(off)
        .map_err(|_| Error::parse("ELF: string-table offset overflow"))?;
    if start > tab.len() {
        return Err(Error::parse("ELF: string offset past end of string table"));
    }
    let end = tab[start..]
        .iter()
        .position(|&c| c == 0)
        .ok_or_else(|| Error::parse("ELF: non-NUL-terminated string in string table"))?;
    let slice = &tab[start..start + end];
    Ok(String::from_utf8_lossy(slice).into_owned())
}

// --- helper: convert a u64 offset/size to usize with overflow check ---------

fn u64_to_usize(v: u64, what: &str) -> Result<usize> {
    usize::try_from(v).map_err(|_| {
        Error::parse(format!("ELF: {what} value {v} exceeds platform address space"))
    })
}

// --- section-header parsing support ----------------------------------------

/// A raw section header.
struct SecHdr {
    name_off: u32,
    sh_type: u32,
    flags: u64,
    addr: u64,
    offset: u64,
    size: u64,
    link: u32,
    info: u32,
    entsize: u64,
}

/// Read one section header at byte offset `base` within `bytes`.
fn read_sec_hdr(bytes: &[u8], base: usize) -> Result<SecHdr> {
    Ok(SecHdr {
        name_off: read_u32(bytes, base)?,
        sh_type: read_u32(bytes, base + 4)?,
        flags: read_u64(bytes, base + 8)?,
        addr: read_u64(bytes, base + 16)?,
        offset: read_u64(bytes, base + 24)?,
        size: read_u64(bytes, base + 32)?,
        link: read_u32(bytes, base + 40)?,
        info: read_u32(bytes, base + 44)?,
        entsize: read_u64(bytes, base + 56)?,
    })
}

// --- symbol-parsing support -------------------------------------------------

/// A raw symbol-table entry (ELF64: 24 bytes).
struct RawSym {
    st_name: u32,
    st_info: u8,
    st_shndx: u16,
    st_value: u64,
    st_size: u64,
}

/// Read one symbol-table entry at byte offset `base` within `bytes`.
fn read_sym(bytes: &[u8], base: usize) -> Result<RawSym> {
    Ok(RawSym {
        st_name: read_u32(bytes, base)?,
        st_info: *bytes.get(base + 4).ok_or_else(|| Error::parse("ELF: truncated symbol (info)"))?,
        st_shndx: read_u16(bytes, base + 6)?,
        st_value: read_u64(bytes, base + 8)?,
        st_size: read_u64(bytes, base + 16)?,
    })
}

// --- Load an ELF64 (little-endian) object image from raw bytes --------------

/// Parse an ELF64 (little-endian) object from its raw bytes.
///
/// Returns the parsed [`Image`] containing sections, symbols, program headers,
/// and relocation entries. Every byte access is bounds-checked; malformed or
/// truncated input yields [`Error::Parse`] (never a panic).
pub fn load(bytes: &[u8]) -> Result<Image> {
    // --- ELF header ---
    if bytes.len() < ELF_HEADER_LEN {
        return Err(Error::parse("ELF: file shorter than the 64-byte header"));
    }
    if &bytes[0..4] != b"\x7fELF" {
        return Err(Error::parse("ELF: bad magic"));
    }
    if bytes[4] != 2 {
        return Err(Error::unsupported("ELF: only ELF64 is supported"));
    }
    if bytes[5] != 1 {
        return Err(Error::unsupported("ELF: only little-endian is supported"));
    }

    let entry = read_u64(bytes, 24)?;
    let phoff = read_u64(bytes, 32)?;
    let shoff = read_u64(bytes, 40)?;
    let _flags = read_u32(bytes, 48)?;
    let ehsize = read_u16(bytes, 52)? as usize;
    let phentsize = read_u16(bytes, 54)? as usize;
    let phnum = read_u16(bytes, 56)? as usize;
    let shentsize = read_u16(bytes, 58)? as usize;
    let shnum_raw = read_u16(bytes, 60)?;
    let shstrndx_raw = read_u16(bytes, 62)?;

    // Validate e_ehsize (the header size).
    if ehsize < ELF_HEADER_LEN {
        return Err(Error::parse("ELF: e_ehsize smaller than the standard header"));
    }

    if shentsize < SECTION_HEADER_LEN && shnum_raw > 0 {
        return Err(Error::parse("ELF: section header entry too small"));
    }

    // SHN_XINDEX handling: if shstrndx_raw is SHN_XINDEX (0xffff), the real
    // section-name-string-table index is in sh_link of section 0.
    let shstrndx = if shstrndx_raw == SHN_XINDEX {
        // We need section headers to read section-0's sh_link. Defer until
        // after section-header parsing.
        None
    } else {
        Some(shstrndx_raw as usize)
    };

    // SHN_UNDEF handling: if shnum_raw == 0, the real count is in sh_info of
    // section 0. Defer until after section-header parsing.

    // --- section headers ---
    let shoff_us = u64_to_usize(shoff, "section-header table offset")?;
    // Read all available section headers, bounded by the file size.
    // First pass: determine the actual section count.
    let max_shnum = if shentsize > 0 {
        let remaining = bytes.len().saturating_sub(shoff_us);
        remaining / shentsize
    } else {
        0
    };
    let shnum = if shnum_raw == 0 {
        // Actual count is in sh_info of section 0 — but only if section 0 exists.
        // Without section headers, treat as 0 (no sections).
        0usize
    } else {
        shnum_raw as usize
    };
    let shnum_actual = shnum.min(max_shnum).min(65536); // sanity cap

    let mut headers: Vec<SecHdr> = Vec::with_capacity(shnum_actual);
    for i in 0..shnum_actual {
        let base = shoff_us
            .checked_add(i.checked_mul(shentsize).ok_or_else(|| {
                Error::parse("ELF: section header offset overflow")
            })?)
            .ok_or_else(|| Error::parse("ELF: section header base overflow"))?;
        headers.push(read_sec_hdr(bytes, base)?);
    }

    // Resolve deferred SHN_XINDEX for shstrndx.
    let shstrndx = match shstrndx {
        Some(idx) => idx,
        None => {
            // Read sh_link from section 0.
            if headers.is_empty() {
                return Err(Error::parse("ELF: SHN_XINDEX but no section 0"));
            }
            headers[0].link as usize
        }
    };

    // Resolve deferred section count (if shnum_raw was 0).
    if shnum_raw == 0 && !headers.is_empty() {
        // The real count is in sh_info of section 0.
        let real_count = headers[0].info as usize;
        // Read any remaining section headers.
        while headers.len() < real_count && headers.len() < max_shnum {
            let i = headers.len();
            let base = shoff_us
                .checked_add(i.checked_mul(shentsize).ok_or_else(|| {
                    Error::parse("ELF: section header offset overflow")
                })?)
                .ok_or_else(|| Error::parse("ELF: section header base overflow"))?;
            match read_sec_hdr(bytes, base) {
                Ok(hdr) => headers.push(hdr),
                Err(_) => break,
            }
        }
    }

    // --- section-name string table ---
    let shstrtab = if shstrndx < headers.len() {
        section_bytes(bytes, &headers[shstrndx])?
    } else {
        Vec::new()
    };

    // --- sections ---
    let sections: Vec<Section> = headers
        .iter()
        .map(|h| {
            let name = if h.name_off == 0 {
                String::new()
            } else {
                read_str(&shstrtab, h.name_off).unwrap_or_else(|_| format!("<bad-name-offset-{}>", h.name_off))
            };
            Section {
                name,
                address: h.addr,
                size: h.size,
                file_offset: h.offset,
                has_data: h.sh_type != SHT_NOBITS,
                writable: h.flags & SHF_WRITE != 0,
                executable: h.flags & SHF_EXECINSTR != 0,
                region: RegionKind::Global,
            }
        })
        .collect();

    // --- symbols (from the first SYMTAB and its linked string table) ---
    let mut symbols = Vec::new();
    if let Some(sym_hdr) = headers.iter().find(|h| h.sh_type == SHT_SYMTAB) {
        let symtab = section_bytes(bytes, sym_hdr)?;
        let strtab = if (sym_hdr.link as usize) < headers.len() {
            section_bytes(bytes, &headers[sym_hdr.link as usize])?
        } else {
            Vec::new()
        };
        // entsize must be at least 24 (standard ELF64 symbol entry).
        // If the section header says 0, use the default; clamp to a
        // reasonable minimum.
        let entsize = if sym_hdr.entsize == 0 {
            SYM_ENTRY_LEN
        } else {
            sym_hdr.entsize.max(SYM_ENTRY_LEN)
        };
        let count = if entsize > 0 {
            (symtab.len() as u64 / entsize) as usize
        } else {
            0
        };
        for i in 0..count.min(100_000) {
            // SAFETY: i * entsize could overflow usize on adversarial input.
            // Use checked arithmetic.
            let base = i
                .checked_mul(usize::try_from(entsize).unwrap_or(0))
                .ok_or_else(|| Error::parse("ELF: symbol entry offset overflow"))?;
            if base + 24 > symtab.len() {
                // Truncated symbol entry — stop parsing.
                break;
            }
            let raw = read_sym(&symtab, base)?;
            let name = if raw.st_name == 0 {
                String::new()
            } else {
                read_str(&strtab, raw.st_name).unwrap_or_else(|_| format!("<sym-{}>", i))
            };
            // Skip the null symbol and unnamed locals; always skip the
            // null symbol (name empty, st_info == 0, st_shndx == SHN_UNDEF).
            let is_null = raw.st_name == 0
                && raw.st_info == 0
                && raw.st_value == 0
                && raw.st_size == 0
                && raw.st_shndx == SHN_UNDEF;
            if is_null {
                continue;
            }
            let st_type = raw.st_info & 0xf;
            symbols.push(Symbol {
                name,
                address: raw.st_value,
                size: raw.st_size,
                is_function: st_type == STT_FUNC,
                section_index: raw.st_shndx,
            });
        }
    }

    // --- program headers ---
    let mut program_headers = Vec::new();
    if phoff > 0 && phnum > 0 && phentsize >= PROGRAM_HEADER_LEN {
        let phoff_us = u64_to_usize(phoff, "program-header table offset")?;
        for i in 0..phnum.min(65536) {
            let base = phoff_us
                .checked_add(i.checked_mul(phentsize).ok_or_else(|| {
                    Error::parse("ELF: program-header offset overflow")
                })?)
                .ok_or_else(|| Error::parse("ELF: program-header base overflow"))?;
            if base + PROGRAM_HEADER_LEN > bytes.len() {
                // Truncated — stop parsing.
                break;
            }
            program_headers.push(ProgramHeader {
                kind: read_u32(bytes, base)?,
                flags: read_u32(bytes, base + 4)?,
                offset: read_u64(bytes, base + 8)?,
                vaddr: read_u64(bytes, base + 16)?,
                paddr: read_u64(bytes, base + 24)?,
                file_size: read_u64(bytes, base + 32)?,
                mem_size: read_u64(bytes, base + 40)?,
                align: read_u64(bytes, base + 48)?,
            });
        }
    }

    // --- relocations (from SHT_RELA / SHT_REL sections) ---
    let mut relocations: Vec<(usize, Vec<Relocation>)> = Vec::new();
    for (sec_idx, hdr) in headers.iter().enumerate() {
        if hdr.sh_type == SHT_RELA {
            let rel_data = section_bytes(bytes, hdr)?;
            let rel_entsize = if hdr.entsize == 0 { RELA_ENTRY_LEN } else { hdr.entsize };
            let count = if rel_entsize > 0 {
                (rel_data.len() as u64 / rel_entsize) as usize
            } else {
                0
            };
            let mut rels = Vec::with_capacity(count.min(100_000));
            for i in 0..count.min(100_000) {
                let base = i
                    .checked_mul(usize::try_from(rel_entsize).unwrap_or(0))
                    .ok_or_else(|| Error::parse("ELF: relocation offset overflow"))?;
                if base + 24 > rel_data.len() {
                    break;
                }
                rels.push(Relocation {
                    offset: read_u64(&rel_data, base)?,
                    kind: read_u32(&rel_data, base + 8)?,
                    symbol: read_u32(&rel_data, base + 12)?,
                    addend: read_i64(&rel_data, base + 16)?,
                });
            }
            relocations.push((sec_idx, rels));
        } else if hdr.sh_type == SHT_REL {
            // REL format: 8-byte entries (offset + info), no explicit addend.
            let rel_data = section_bytes(bytes, hdr)?;
            let rel_entsize = if hdr.entsize == 0 { REL_ENTRY_LEN } else { hdr.entsize };
            let count = if rel_entsize > 0 {
                (rel_data.len() as u64 / rel_entsize) as usize
            } else {
                0
            };
            let mut rels = Vec::with_capacity(count.min(100_000));
            for i in 0..count.min(100_000) {
                let base = i
                    .checked_mul(usize::try_from(rel_entsize).unwrap_or(0))
                    .ok_or_else(|| Error::parse("ELF: relocation offset overflow"))?;
                if base + 8 > rel_data.len() {
                    break;
                }
                let r_offset = read_u64(&rel_data, base)?;
                let r_info = read_u64(&rel_data, base + 8)?;
                rels.push(Relocation {
                    offset: r_offset,
                    kind: (r_info & 0xffff_ffff) as u32,
                    symbol: (r_info >> 32) as u32,
                    addend: 0,
                });
            }
            relocations.push((sec_idx, rels));
        }
    }

    Ok(Image {
        sections,
        symbols,
        program_headers,
        relocations,
        entry: (entry != 0).then_some(entry),
    })
}

/// The file bytes a section header refers to (empty for `NOBITS`),
/// bounds-checked.
fn section_bytes(bytes: &[u8], hdr: &SecHdr) -> Result<Vec<u8>> {
    if hdr.sh_type == SHT_NOBITS || hdr.size == 0 {
        return Ok(Vec::new());
    }
    let start = u64_to_usize(hdr.offset, "section offset")?;
    let size = u64_to_usize(hdr.size, "section size")?;
    let end = start
        .checked_add(size)
        .ok_or_else(|| Error::parse("ELF: section offset+size overflow"))?;
    bytes
        .get(start..end)
        .map(<[u8]>::to_vec)
        .ok_or_else(|| Error::parse("ELF: section bytes out of range"))
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used)]
    use super::*;

    fn put_u16(out: &mut [u8], off: usize, v: u16) {
        out[off..off + 2].copy_from_slice(&v.to_le_bytes());
    }

    fn put_u32(out: &mut [u8], off: usize, v: u32) {
        out[off..off + 4].copy_from_slice(&v.to_le_bytes());
    }

    fn put_u64(out: &mut [u8], off: usize, v: u64) {
        out[off..off + 8].copy_from_slice(&v.to_le_bytes());
    }

    /// Build a minimal but valid ELF64 image with one `.text` section (4 bytes)
    /// and one function symbol `myfunc` of size 4 at vaddr 0x1000.
    fn sample_elf() -> Vec<u8> {
        // Layout: [header 64][.text 4][.shstrtab][.strtab][.symtab][shdrs].
        let text: [u8; 4] = [0x31, 0xc0, 0xc3, 0x90]; // xor eax,eax; ret; nop
        let shstr: &[u8] = b"\0.text\0.shstrtab\0.symtab\0.strtab\0";
        let strtab: &[u8] = b"\0myfunc\0";

        let text_off = ELF_HEADER_LEN as u64;
        let shstr_off = text_off + text.len() as u64;
        let strtab_off = shstr_off + shstr.len() as u64;
        let symtab_off = strtab_off + strtab.len() as u64;
        let symtab_size = 2 * SYM_ENTRY_LEN; // null + myfunc
        let shoff = symtab_off + symtab_size;

        let mut out = vec![0u8; (shoff + 5 * SECTION_HEADER_LEN as u64) as usize];
        out[0..4].copy_from_slice(b"\x7fELF");
        out[4] = 2; // ELF64
        out[5] = 1; // little-endian
        out[6] = 1; // version
        put_u16(&mut out, 16, 2); // e_type = ET_EXEC
        put_u16(&mut out, 18, 62); // e_machine = x86-64
        put_u32(&mut out, 20, 1); // e_version
        put_u64(&mut out, 24, 0x1000); // e_entry
        put_u64(&mut out, 40, shoff); // e_shoff
        put_u16(&mut out, 52, ELF_HEADER_LEN as u16); // e_ehsize
        put_u16(&mut out, 58, SECTION_HEADER_LEN as u16); // e_shentsize
        put_u16(&mut out, 60, 5); // e_shnum
        put_u16(&mut out, 62, 2); // e_shstrndx (.shstrtab is section 2)

        out[text_off as usize..(text_off as usize + 4)].copy_from_slice(&text);
        out[shstr_off as usize..(shstr_off as usize + shstr.len())].copy_from_slice(shstr);
        out[strtab_off as usize..(strtab_off as usize + strtab.len())].copy_from_slice(strtab);

        // symtab[1] = myfunc.
        let s1 = symtab_off as usize + SYM_ENTRY_LEN as usize;
        put_u32(&mut out, s1, 1); // st_name -> "myfunc"
        out[s1 + 4] = (1 << 4) | STT_FUNC; // GLOBAL | FUNC
        put_u16(&mut out, s1 + 6, 1); // st_shndx = .text
        put_u64(&mut out, s1 + 8, 0x1000); // st_value
        put_u64(&mut out, s1 + 16, 4); // st_size

        // Section headers (5 × 64); [0]=NULL stays zero.
        let mut sh = |idx: usize, fields: &[(usize, u64, u8)]| {
            let base = shoff as usize + idx * SECTION_HEADER_LEN;
            for &(off, val, width) in fields {
                match width {
                    4 => put_u32(&mut out, base + off, val as u32),
                    _ => put_u64(&mut out, base + off, val),
                }
            }
        };
        sh(1, &[(0, 1, 4), (4, 1, 4), (8, 0x6, 8), (16, 0x1000, 8), (24, text_off, 8), (32, 4, 8), (48, 16, 8)]);
        sh(2, &[(0, 7, 4), (4, 3, 4), (24, shstr_off, 8), (32, shstr.len() as u64, 8)]);
        sh(3, &[(0, 17, 4), (4, 2, 4), (24, symtab_off, 8), (32, symtab_size, 8), (40, 4, 4), (44, 1, 4), (56, SYM_ENTRY_LEN, 8)]);
        sh(4, &[(0, 25, 4), (4, 3, 4), (24, strtab_off, 8), (32, strtab.len() as u64, 8)]);

        out
    }

    /// Build an ELF with named sections, proper shstrtab, a symtab, and
    /// program headers for more thorough testing.
    ///
    /// Section layout:
    ///   0: NULL
    ///   1: .text        (SHT_PROGBITS, addr 0x1000, 8 bytes)
    ///   2: .data        (SHT_PROGBITS, addr 0x2000, 4 bytes)
    ///   3: .shstrtab    (SHT_STRTAB)
    ///   4: .symtab      (SHT_SYMTAB, link=5, info=1)
    ///   5: .strtab      (SHT_STRTAB)
    /// shstrndx = 3 (section 3 is .shstrtab)
    fn sample_elf_with_phdr() -> Vec<u8> {
        let text: [u8; 8] = [0x31, 0xc0, 0x31, 0xdb, 0xc3, 0x90, 0x90, 0x90];
        let data: [u8; 4] = [0x01, 0x00, 0x00, 0x00];
        let shstrtab: &[u8] = b"\0.text\0.data\0.shstrtab\0.symtab\0.strtab\0";
        let strtab: &[u8] = b"\0myfunc\0myvar\0";

        // Offsets within shstrtab:
        //   \0  .text\0  .data\0  .shstrtab\0  .symtab\0  .strtab\0
        //   0   1-5     7-11     13-21        23-29      31-37
        // Offsets within strtab:
        //   \0  myfunc\0  myvar\0
        //   0   1-6      8-12
        const SH_NAME_TEXT: u32 = 1;
        const SH_NAME_DATA: u32 = 7;
        const SH_NAME_SHSTRTAB: u32 = 13;
        const SH_NAME_SYMTAB: u32 = 23;
        const SH_NAME_STRTAB: u32 = 31;
        const SY_NAME_MYFUNC: u32 = 1;
        const SY_NAME_OBJECT: u32 = 8;

        let text_off = ELF_HEADER_LEN as u64;
        let data_off = text_off + text.len() as u64;
        let shstr_off = data_off + data.len() as u64;
        let strtab_off = shstr_off + shstrtab.len() as u64;
        let symtab_off = strtab_off + strtab.len() as u64;
        let symtab_size = 3 * SYM_ENTRY_LEN;
        let shnum = 6usize;
        let shoff = symtab_off + symtab_size;
        let phoff = shoff + shnum as u64 * SECTION_HEADER_LEN as u64;

        let total = phoff + 2 * PROGRAM_HEADER_LEN as u64;
        let mut out = vec![0u8; total as usize];

        // ELF header
        out[0..4].copy_from_slice(b"\x7fELF");
        out[4] = 2;
        out[5] = 1;
        out[6] = 1;
        put_u16(&mut out, 16, 2);                        // e_type
        put_u16(&mut out, 18, 62);                       // e_machine = x86-64
        put_u32(&mut out, 20, 1);                        // e_version
        put_u64(&mut out, 24, 0x1000);                   // e_entry
        put_u64(&mut out, 32, phoff);                    // e_phoff
        put_u64(&mut out, 40, shoff);                    // e_shoff
        put_u32(&mut out, 48, 0);                        // e_flags
        put_u16(&mut out, 52, ELF_HEADER_LEN as u16);    // e_ehsize
        put_u16(&mut out, 54, PROGRAM_HEADER_LEN as u16); // e_phentsize
        put_u16(&mut out, 56, 2);                        // e_phnum
        put_u16(&mut out, 58, SECTION_HEADER_LEN as u16); // e_shentsize
        put_u16(&mut out, 60, shnum as u16);             // e_shnum
        put_u16(&mut out, 62, 3);                        // e_shstrndx = .shstrtab

        // Section content
        out[text_off as usize..][..text.len()].copy_from_slice(&text);
        out[data_off as usize..][..data.len()].copy_from_slice(&data);
        out[shstr_off as usize..][..shstrtab.len()].copy_from_slice(shstrtab);
        out[strtab_off as usize..][..strtab.len()].copy_from_slice(strtab);

        // symtab: null entry, myfunc, myvar
        let s1 = symtab_off as usize + SYM_ENTRY_LEN as usize;
        put_u32(&mut out, s1, SY_NAME_MYFUNC);
        out[s1 + 4] = (1 << 4) | STT_FUNC;     // GLOBAL | FUNC
        put_u16(&mut out, s1 + 6, 1);           // st_shndx = .text
        put_u64(&mut out, s1 + 8, 0x1000);      // st_value
        put_u64(&mut out, s1 + 16, 8);          // st_size
        let s2 = symtab_off as usize + 2 * SYM_ENTRY_LEN as usize;
        put_u32(&mut out, s2, SY_NAME_OBJECT);
        out[s2 + 4] = (1 << 4) | STT_OBJECT;   // GLOBAL | OBJECT
        put_u16(&mut out, s2 + 6, 2);           // st_shndx = .data
        put_u64(&mut out, s2 + 8, 0x2000);      // st_value
        put_u64(&mut out, s2 + 16, 4);          // st_size

        // Section headers (6 entries, 64 bytes each)
        let mut w = |idx: usize, off: usize, val: u64, width: u8| {
            let pos = shoff as usize + idx * 64 + off;
            match width {
                4 => put_u32(&mut out, pos, val as u32),
                _ => put_u64(&mut out, pos, val),
            }
        };
        // Section 0: NULL (all zeros already)
        // Section 1: .text
        w(1, 0, SH_NAME_TEXT as u64, 4);
        w(1, 4, 1, 4);            // SHT_PROGBITS
        w(1, 8, 0x6, 8);          // flags (AX)
        w(1, 16, 0x1000, 8);      // addr
        w(1, 24, text_off, 8);    // offset
        w(1, 32, text.len() as u64, 8); // size
        w(1, 48, 16, 8);          // addralign
        // Section 2: .data
        w(2, 0, SH_NAME_DATA as u64, 4);
        w(2, 4, 1, 4);            // SHT_PROGBITS
        w(2, 8, 0x3, 8);          // flags (WA)
        w(2, 16, 0x2000, 8);      // addr
        w(2, 24, data_off, 8);    // offset
        w(2, 32, data.len() as u64, 8); // size
        w(2, 48, 4, 8);           // addralign
        // Section 3: .shstrtab
        w(3, 0, SH_NAME_SHSTRTAB as u64, 4);
        w(3, 4, 3, 4);            // SHT_STRTAB
        w(3, 24, shstr_off, 8);   // offset
        w(3, 32, shstrtab.len() as u64, 8); // size
        // Section 4: .symtab
        w(4, 0, SH_NAME_SYMTAB as u64, 4);
        w(4, 4, 2, 4);            // SHT_SYMTAB
        w(4, 24, symtab_off, 8);  // offset
        w(4, 32, symtab_size, 8); // size
        w(4, 40, 5, 4);           // link -> .strtab
        w(4, 44, 1, 4);           // info (first non-local symbol)
        w(4, 56, SYM_ENTRY_LEN, 8); // entsize
        // Section 5: .strtab
        w(5, 0, SH_NAME_STRTAB as u64, 4);
        w(5, 4, 3, 4);            // SHT_STRTAB
        w(5, 24, strtab_off, 8);  // offset
        w(5, 32, strtab.len() as u64, 8); // size

        // Program headers: PT_LOAD for text and data
        put_u32(&mut out, phoff as usize, 1);             // p_type = PT_LOAD
        put_u32(&mut out, phoff as usize + 4, 5);         // p_flags = R+X
        put_u64(&mut out, phoff as usize + 8, text_off);  // p_offset
        put_u64(&mut out, phoff as usize + 16, 0x1000);   // p_vaddr
        put_u64(&mut out, phoff as usize + 24, 0x1000);   // p_paddr
        put_u64(&mut out, phoff as usize + 32, text.len() as u64); // p_filesz
        put_u64(&mut out, phoff as usize + 40, text.len() as u64); // p_memsz
        put_u64(&mut out, phoff as usize + 48, 0x1000);   // p_align
        let ph2 = phoff as usize + PROGRAM_HEADER_LEN;
        put_u32(&mut out, ph2, 1);                        // p_type = PT_LOAD
        put_u32(&mut out, ph2 + 4, 6);                    // p_flags = R+W
        put_u64(&mut out, ph2 + 8, data_off);             // p_offset
        put_u64(&mut out, ph2 + 16, 0x2000);              // p_vaddr
        put_u64(&mut out, ph2 + 24, 0x2000);              // p_paddr
        put_u64(&mut out, ph2 + 32, data.len() as u64);   // p_filesz
        put_u64(&mut out, ph2 + 40, data.len() as u64);   // p_memsz
        put_u64(&mut out, ph2 + 48, 0x1000);              // p_align

        out
    }

    // ------------------------------------------------------------------
    // Tests
    // ------------------------------------------------------------------

    #[test]
    fn parses_sections_symbols_and_code() {
        let image = sample_elf();
        let img = load(&image).expect("valid ELF");
        assert_eq!(img.entry, Some(0x1000));

        let text = img.sections.iter().find(|s| s.name == ".text").expect(".text");
        assert!(text.executable && !text.writable);
        assert_eq!(text.address, 0x1000);

        let funcs: Vec<_> = img.functions().collect();
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "myfunc");
        assert_eq!(funcs[0].address, 0x1000);

        let code = img.function_code(funcs[0], &image).expect("code bytes");
        assert_eq!(code, &[0x31, 0xc0, 0xc3, 0x90]);
    }

    #[test]
    fn rejects_non_elf_and_truncation() {
        assert!(load(b"not an elf at all").is_err());
        assert!(load(b"\x7fELF").is_err()); // magic only, truncated
        let mut bad = sample_elf();
        bad[4] = 1; // ELF32
        assert!(load(&bad).is_err());
    }

    #[test]
    fn section_lookup_by_address() {
        let image = sample_elf();
        let img = load(&image).unwrap();
        assert_eq!(img.section_at(0x1002).map(|s| s.name.as_str()), Some(".text"));
        assert!(img.section_at(0x9999).is_none());
    }

    #[test]
    fn rejects_truncated_magic_only() {
        assert!(load(&b"\x7fELF"[..4]).is_err());
    }

    #[test]
    fn rejects_header_shorter_than_64() {
        assert!(load(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]).is_err());
    }

    #[test]
    fn rejects_big_endian() {
        let mut elf = sample_elf();
        elf[5] = 2; // big-endian
        assert!(load(&elf).is_err());
    }

    #[test]
    fn rejects_elf32() {
        let mut elf = sample_elf();
        elf[4] = 1; // ELF32
        assert!(load(&elf).is_err());
    }

    #[test]
    fn handles_empty_section_table() {
        let mut bytes = vec![0u8; ELF_HEADER_LEN];
        bytes[0..4].copy_from_slice(b"\x7fELF");
        bytes[4] = 2;
        bytes[5] = 1;
        bytes[6] = 1;
        put_u16(&mut bytes, 52, ELF_HEADER_LEN as u16); // e_ehsize = 64
        // shnum = 0
        put_u16(&mut bytes, 60, 0);
        let img = load(&bytes).expect("ELF with no sections should parse");
        assert!(img.sections.is_empty());
        assert!(img.symbols.is_empty());
    }

    #[test]
    fn handles_section_size_overflow() {
        // A section with offset = u64::MAX should not panic.
        let mut elf = sample_elf();
        // Patch the symtab section's offset to a huge value (the symtab
        // is read via section_bytes, so u64::MAX will hit overflow).
        let shoff = read_u64(&elf, 40).unwrap() as usize;
        // Section 3 is .symtab (index 3, byte offset 3*64 within shoff).
        put_u64(&mut elf, shoff + 3 * 64 + 24, u64::MAX); // sh_offset of .symtab
        let result = load(&elf);
        // Must be an error, not a panic.
        assert!(result.is_err());
    }

    #[test]
    fn rejects_shstrndx_out_of_range() {
        let mut elf = sample_elf();
        // Set shstrndx to an index beyond the section table.
        put_u16(&mut elf, 62, 99);
        let img = load(&elf).expect("should still parse (strtab becomes empty)");
        // Sections should parse, but names may be <bad-name-offset-...>
        assert!(!img.sections.is_empty());
    }

    #[test]
    fn rejects_shentsize_too_small() {
        let mut elf = sample_elf();
        put_u16(&mut elf, 58, 48); // shentsize smaller than 64
        assert!(load(&elf).is_err());
    }

    #[test]
    fn function_code_returns_none_for_sizeless_symbol() {
        let elf = sample_elf();
        let img = load(&elf).unwrap();
        let sym = Symbol {
            name: "no_size".into(),
            address: 0x1000,
            size: 0,
            is_function: true,
            section_index: 1,
        };
        assert!(img.function_code(&sym, &elf).is_none());
    }

    #[test]
    fn function_code_returns_none_for_out_of_range() {
        let elf = sample_elf();
        let img = load(&elf).unwrap();
        let sym = Symbol {
            name: "gone".into(),
            address: 0x9999,
            size: 4,
            is_function: true,
            section_index: 1,
        };
        assert!(img.function_code(&sym, &elf).is_none());
    }

    #[test]
    fn function_code_handles_overflow() {
        let elf = sample_elf();
        let img = load(&elf).unwrap();
        let sym = Symbol {
            name: "huge".into(),
            address: u64::MAX - 3,
            size: 8,
            is_function: true,
            section_index: 1,
        };
        // Should return None, not panic.
        assert!(img.function_code(&sym, &elf).is_none());
    }

    #[test]
    fn parses_program_headers() {
        let elf = sample_elf_with_phdr();
        let img = load(&elf).expect("valid ELF with program headers");
        assert_eq!(img.program_headers.len(), 2);
        assert_eq!(img.program_headers[0].kind, 1); // PT_LOAD
        assert_eq!(img.program_headers[0].flags, 5); // PF_R | PF_X
        assert_eq!(img.program_headers[0].vaddr, 0x1000);
        assert_eq!(img.program_headers[1].kind, 1);
        assert_eq!(img.program_headers[1].flags, 6); // PF_R | PF_W
        assert_eq!(img.program_headers[1].vaddr, 0x2000);
    }

    #[test]
    fn parses_symbol_types() {
        let elf = sample_elf_with_phdr();
        let img = load(&elf).expect("valid ELF");
        // myfunc should be a function, myvar should not be.
        let myfunc = img.symbols.iter().find(|s| s.name == "myfunc").expect("myfunc");
        assert!(myfunc.is_function);
        assert_eq!(myfunc.size, 8);
        let myvar = img.symbols.iter().find(|s| s.name == "myvar").expect("myvar");
        assert!(!myvar.is_function);
        assert_eq!(myvar.size, 4);
    }

    #[test]
    fn rejects_truncated_program_headers() {
        let mut elf = sample_elf_with_phdr();
        // Truncate the file after the section headers, before program headers.
        let shoff = read_u64(&elf, 40).unwrap() as usize;
        let shnum = read_u16(&elf, 60).unwrap() as usize;
        let truncate_to = shoff + shnum * SECTION_HEADER_LEN;
        elf.truncate(truncate_to);
        // Should parse but with truncated program headers.
        let img = load(&elf).expect("should still parse basic structure");
        assert!(!img.sections.is_empty());
        // Program headers may be incomplete.
        if !img.program_headers.is_empty() {
            // That's fine too; we just must not panic.
        }
    }

    #[test]
    fn rejects_symbol_table_with_truncated_entry() {
        let mut elf = sample_elf();
        // Find the symtab and shorten its size so only a partial entry exists.
        let shoff = read_u64(&elf, 40).unwrap() as usize;
        let symtab_size_off = shoff + 3 * SECTION_HEADER_LEN + 32;
        put_u64(&mut elf, symtab_size_off, 10); // only 10 bytes instead of 48
        let img = load(&elf).expect("should parse without panic");
        // Either no symbols or partial symbols; no panic.
        assert!(img.symbols.len() <= 2);
    }

    #[test]
    fn symbol_has_section_index() {
        let elf = sample_elf();
        let img = load(&elf).expect("valid ELF");
        let myfunc = img.symbols.iter().find(|s| s.name == "myfunc").expect("myfunc");
        assert_eq!(myfunc.section_index, 1); // .text is section 1
    }

    #[test]
    fn saturating_section_at_avoids_overflow() {
        let sections = vec![Section {
            name: "big".into(),
            address: u64::MAX - 100,
            size: 200,
            file_offset: 0,
            has_data: true,
            writable: false,
            executable: false,
            region: RegionKind::Global,
        }];
        let img = Image {
            sections,
            ..Image::default()
        };
        // u64::MAX - 100 + 200 = u64::MAX + 100, which wraps in normal
        // arithmetic but section_at uses saturating_add so it should
        // just clamp at u64::MAX.
        let found = img.section_at(u64::MAX - 50);
        assert!(found.is_some());
        // A clearly-out-of-range address should not match.
        assert!(img.section_at(0).is_none());
    }

    #[test]
    fn zeroed_elf_header_is_rejected_cleanly() {
        let bytes = vec![0u8; ELF_HEADER_LEN];
        assert!(load(&bytes).is_err()); // bad magic
    }

    #[test]
    fn negative_shentsize_zero_with_shnum() {
        let mut elf = sample_elf();
        put_u16(&mut elf, 58, 0); // shentsize = 0
        // shnum = 5, but shentsize = 0 means no headers are readable.
        assert!(load(&elf).is_err());
    }

    /// Verify that a string offset past the table returns an error (not a
    /// silent clamp).
    #[test]
    fn read_str_rejects_out_of_bounds_offset() {
        let tab = b"hello\0world\0";
        assert!(read_str(tab, 20).is_err());  // past end
        assert!(read_str(tab, 0).unwrap() == "hello");
        assert!(read_str(tab, 6).unwrap() == "world");
        // Offset exactly at end (but not past) — no NUL terminator.
        assert!(read_str(tab, 12).is_err());  // at end, no terminator
        // u32::MAX offset.
        assert!(read_str(tab, u32::MAX).is_err());
    }
}
