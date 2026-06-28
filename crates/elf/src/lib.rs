//! # csolver-elf — object-file loader (pure Rust, no external crates)
//!
//! A from-scratch ELF64 reader: it parses the header, the section table, and the
//! symbol table, exposing exactly the context the assembly frontend and the
//! memory model need — sections (with permissions and where their bytes live)
//! and symbols (functions and their code). This is the entry point for verifying
//! a *compiled binary* with no source: load the image, locate a function, hand
//! its bytes to the decoder.
//!
//! ## Scope
//!
//! ELF64, little-endian (x86-64 / AArch64). Parsing is **bounds-checked
//! throughout** — a truncated or malformed image yields [`csolver_core::Error`],
//! never a panic, because the loader is the trust boundary between an untrusted
//! file and the analysis. PE / Mach-O, DWARF debug info, relocations, and the
//! PLT/GOT are later increments; this layer already lets the pipeline enumerate
//! functions and recover their machine code.

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

impl Image {
    /// The first section whose virtual-address range contains `addr`.
    pub fn section_at(&self, addr: u64) -> Option<&Section> {
        self.sections
            .iter()
            .find(|s| s.size > 0 && addr >= s.address && addr < s.address + s.size)
    }

    /// The machine-code bytes of `sym` (a function), sliced from the original
    /// image `bytes`. `None` if the symbol is sizeless, not backed by file data,
    /// or out of range.
    pub fn function_code<'a>(&self, sym: &Symbol, bytes: &'a [u8]) -> Option<&'a [u8]> {
        if sym.size == 0 {
            return None;
        }
        let sec = self.section_at(sym.address)?;
        if !sec.has_data || sym.address + sym.size > sec.address + sec.size {
            return None;
        }
        let start = sec.file_offset.checked_add(sym.address - sec.address)?;
        let end = start.checked_add(sym.size)?;
        bytes.get(start as usize..end as usize)
    }

    /// The defined function symbols, in image order.
    pub fn functions(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols.iter().filter(|s| s.is_function && s.size > 0)
    }
}

// --- ELF constants ---------------------------------------------------------

const ELF_HEADER_LEN: usize = 64;
const SECTION_HEADER_LEN: usize = 64;
const SYM_ENTRY_LEN: u64 = 24;

const SHT_SYMTAB: u32 = 2;
const SHT_NOBITS: u32 = 8;

const SHF_WRITE: u64 = 0x1;
const SHF_EXECINSTR: u64 = 0x4;

const STT_FUNC: u8 = 2;

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

/// A NUL-terminated string at `off` within a string table `tab`.
fn read_str(tab: &[u8], off: u32) -> String {
    let start = (off as usize).min(tab.len());
    let end = tab[start..]
        .iter()
        .position(|&c| c == 0)
        .map(|p| start + p)
        .unwrap_or(tab.len());
    String::from_utf8_lossy(&tab[start..end]).into_owned()
}

/// A raw section header.
struct SecHdr {
    name_off: u32,
    sh_type: u32,
    flags: u64,
    addr: u64,
    offset: u64,
    size: u64,
    link: u32,
    entsize: u64,
}

/// Load an ELF64 (little-endian) object image from raw bytes.
pub fn load(bytes: &[u8]) -> Result<Image> {
    // --- header ---
    if bytes.len() < ELF_HEADER_LEN {
        return Err(Error::parse("ELF: file shorter than the header"));
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
    let shoff = read_u64(bytes, 40)? as usize;
    let shentsize = read_u16(bytes, 58)? as usize;
    let shnum = read_u16(bytes, 60)? as usize;
    let shstrndx = read_u16(bytes, 62)? as usize;

    if shnum == 0 {
        // No sections: a valid (if minimal) image.
        return Ok(Image {
            entry: (entry != 0).then_some(entry),
            ..Image::default()
        });
    }
    if shentsize < SECTION_HEADER_LEN {
        return Err(Error::parse("ELF: section header entry too small"));
    }

    // --- section headers ---
    let mut headers = Vec::with_capacity(shnum);
    for i in 0..shnum {
        let base = shoff + i * shentsize;
        headers.push(SecHdr {
            name_off: read_u32(bytes, base)?,
            sh_type: read_u32(bytes, base + 4)?,
            flags: read_u64(bytes, base + 8)?,
            addr: read_u64(bytes, base + 16)?,
            offset: read_u64(bytes, base + 24)?,
            size: read_u64(bytes, base + 32)?,
            link: read_u32(bytes, base + 40)?,
            entsize: read_u64(bytes, base + 56)?,
        });
    }

    // --- section-name string table ---
    let shstrtab = section_bytes(bytes, headers.get(shstrndx))?;

    // --- sections ---
    let sections = headers
        .iter()
        .map(|h| Section {
            name: read_str(&shstrtab, h.name_off),
            address: h.addr,
            size: h.size,
            file_offset: h.offset,
            has_data: h.sh_type != SHT_NOBITS,
            writable: h.flags & SHF_WRITE != 0,
            executable: h.flags & SHF_EXECINSTR != 0,
            region: RegionKind::Global,
        })
        .collect();

    // --- symbols (from the first SYMTAB and its linked string table) ---
    let mut symbols = Vec::new();
    if let Some(sym_hdr) = headers.iter().find(|h| h.sh_type == SHT_SYMTAB) {
        let symtab = section_bytes(bytes, Some(sym_hdr))?;
        let strtab = section_bytes(bytes, headers.get(sym_hdr.link as usize))?;
        let entsize = if sym_hdr.entsize == 0 { SYM_ENTRY_LEN } else { sym_hdr.entsize };
        let count = (symtab.len() as u64 / entsize) as usize;
        for i in 0..count {
            let base = i * entsize as usize;
            let st_name = read_u32(&symtab, base)?;
            let st_info = symtab[base + 4];
            let st_value = read_u64(&symtab, base + 8)?;
            let st_size = read_u64(&symtab, base + 16)?;
            let name = read_str(&strtab, st_name);
            if name.is_empty() {
                continue; // the null symbol / unnamed locals carry nothing useful
            }
            symbols.push(Symbol {
                name,
                address: st_value,
                size: st_size,
                is_function: st_info & 0xf == STT_FUNC,
            });
        }
    }

    Ok(Image {
        sections,
        symbols,
        entry: (entry != 0).then_some(entry),
    })
}

/// The file bytes a section header refers to (empty for `NOBITS`), bounds-checked.
fn section_bytes(bytes: &[u8], hdr: Option<&SecHdr>) -> Result<Vec<u8>> {
    let Some(h) = hdr else {
        return Err(Error::parse("ELF: section index out of range"));
    };
    if h.sh_type == SHT_NOBITS || h.size == 0 {
        return Ok(Vec::new());
    }
    let start = h.offset as usize;
    let end = start
        .checked_add(h.size as usize)
        .ok_or_else(|| Error::parse("ELF: section size overflow"))?;
    bytes
        .get(start..end)
        .map(<[u8]>::to_vec)
        .ok_or_else(|| Error::parse("ELF: section bytes out of range"))
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used)]
    use super::*;

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

    fn put_u16(out: &mut [u8], off: usize, v: u16) {
        out[off..off + 2].copy_from_slice(&v.to_le_bytes());
    }
    fn put_u32(out: &mut [u8], off: usize, v: u32) {
        out[off..off + 4].copy_from_slice(&v.to_le_bytes());
    }
    fn put_u64(out: &mut [u8], off: usize, v: u64) {
        out[off..off + 8].copy_from_slice(&v.to_le_bytes());
    }

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
}
