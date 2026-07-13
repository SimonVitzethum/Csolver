//! A class- and endian-generic ELF reader for the cases the fast path in [`crate::load`]
//! does not cover: **ELF32** (`ei_class = 1`) and **big-endian** (`ei_data = 2`) images.
//!
//! The mainstream 64-bit little-endian path stays in `load.rs` (it also parses the DWARF,
//! hash and version auxiliaries). This module produces the core [`Image`] fields that the
//! decode-and-verify pipeline consumes (sections, symbols, relocations, program headers,
//! entry, machine) for the remaining three class-by-endian combinations, so a 32-bit or
//! big-endian object is parsed instead of rejected. The auxiliary tables (GNU/SysV hash,
//! notes, version info, dynamic) are left empty for these combinations; they only refine
//! dynamic-symbol niceties, never soundness. Bounds-checked throughout, never a panic.

use super::*;

/// An endian-aware bounds-checked reader over an ELF image.
struct Reader {
    /// True for big-endian (`ELFDATA2MSB`).
    be: bool,
}

impl Reader {
    fn u16(&self, b: &[u8], o: usize) -> Result<u16> {
        let s: [u8; 2] = b.get(o..o + 2).and_then(|x| x.try_into().ok()).ok_or_else(|| Error::parse("ELF: truncated (u16)"))?;
        Ok(if self.be { u16::from_be_bytes(s) } else { u16::from_le_bytes(s) })
    }
    fn u32(&self, b: &[u8], o: usize) -> Result<u32> {
        let s: [u8; 4] = b.get(o..o + 4).and_then(|x| x.try_into().ok()).ok_or_else(|| Error::parse("ELF: truncated (u32)"))?;
        Ok(if self.be { u32::from_be_bytes(s) } else { u32::from_le_bytes(s) })
    }
    fn u64(&self, b: &[u8], o: usize) -> Result<u64> {
        let s: [u8; 8] = b.get(o..o + 8).and_then(|x| x.try_into().ok()).ok_or_else(|| Error::parse("ELF: truncated (u64)"))?;
        Ok(if self.be { u64::from_be_bytes(s) } else { u64::from_le_bytes(s) })
    }
}

/// Parse an ELF32 or big-endian ELF object into the core [`Image`] fields.
pub(crate) fn load_generic(bytes: &[u8]) -> Result<Image> {
    if bytes.len() < 52 {
        return Err(Error::parse("ELF: file shorter than the 32-bit header"));
    }
    let is64 = match bytes[4] {
        1 => false,
        2 => true,
        _ => return Err(Error::unsupported("ELF: unknown ei_class")),
    };
    let be = match bytes[5] {
        1 => false,
        2 => true,
        _ => return Err(Error::unsupported("ELF: unknown ei_data")),
    };
    let r = Reader { be };

    // Header field offsets differ by class after e_flags: ELF32 uses 4-byte
    // entry/phoff/shoff, ELF64 uses 8-byte. Lay them out per class.
    let (e_machine, e_entry, e_shoff, e_shentsize, e_shnum, e_shstrndx, e_phoff, e_phentsize, e_phnum);
    e_machine = r.u16(bytes, 18)?;
    if is64 {
        e_entry = r.u64(bytes, 24)?;
        e_phoff = r.u64(bytes, 32)? as usize;
        e_shoff = r.u64(bytes, 40)? as usize;
        e_phentsize = r.u16(bytes, 54)? as usize;
        e_phnum = r.u16(bytes, 56)? as usize;
        e_shentsize = r.u16(bytes, 58)? as usize;
        e_shnum = r.u16(bytes, 60)? as usize;
        e_shstrndx = r.u16(bytes, 62)? as usize;
    } else {
        e_entry = r.u32(bytes, 24)? as u64;
        e_phoff = r.u32(bytes, 28)? as usize;
        e_shoff = r.u32(bytes, 32)? as usize;
        e_phentsize = r.u16(bytes, 42)? as usize;
        e_phnum = r.u16(bytes, 44)? as usize;
        e_shentsize = r.u16(bytes, 46)? as usize;
        e_shnum = r.u16(bytes, 48)? as usize;
        e_shstrndx = r.u16(bytes, 50)? as usize;
    }

    // --- section headers ---
    struct GHdr {
        name_off: u32,
        sh_type: u32,
        flags: u64,
        addr: u64,
        offset: u64,
        size: u64,
        link: u32,
        info: u32,
    }
    let read_shdr = |base: usize| -> Result<GHdr> {
        if is64 {
            Ok(GHdr {
                name_off: r.u32(bytes, base)?,
                sh_type: r.u32(bytes, base + 4)?,
                flags: r.u64(bytes, base + 8)?,
                addr: r.u64(bytes, base + 16)?,
                offset: r.u64(bytes, base + 24)?,
                size: r.u64(bytes, base + 32)?,
                link: r.u32(bytes, base + 40)?,
                info: r.u32(bytes, base + 44)?,
            })
        } else {
            Ok(GHdr {
                name_off: r.u32(bytes, base)?,
                sh_type: r.u32(bytes, base + 4)?,
                flags: r.u32(bytes, base + 8)? as u64,
                addr: r.u32(bytes, base + 12)? as u64,
                offset: r.u32(bytes, base + 16)? as u64,
                size: r.u32(bytes, base + 20)? as u64,
                link: r.u32(bytes, base + 24)?,
                info: r.u32(bytes, base + 28)?,
            })
        }
    };
    let min_shent = if is64 { 64 } else { 40 };
    if e_shentsize < min_shent && e_shnum > 0 {
        return Err(Error::parse("ELF: section header entry too small"));
    }
    let max_shnum = bytes.len().saturating_sub(e_shoff).checked_div(e_shentsize.max(1)).unwrap_or(0);
    let shnum = e_shnum.min(max_shnum).min(65536);
    let mut headers: Vec<GHdr> = Vec::with_capacity(shnum);
    for i in 0..shnum {
        let base = e_shoff.checked_add(i.checked_mul(e_shentsize).ok_or_else(|| Error::parse("ELF: shdr overflow"))?).ok_or_else(|| Error::parse("ELF: shdr overflow"))?;
        headers.push(read_shdr(base)?);
    }

    // Slice a section's file bytes (bounds-checked; NOBITS → empty).
    let sec_bytes = |h: &GHdr| -> Vec<u8> {
        if h.sh_type == SHT_NOBITS {
            return Vec::new();
        }
        let (Ok(off), Ok(sz)) = (usize::try_from(h.offset), usize::try_from(h.size)) else { return Vec::new() };
        bytes.get(off..off.saturating_add(sz)).map(|s| s.to_vec()).unwrap_or_default()
    };

    // --- section-name string table ---
    let shstrtab = headers.get(e_shstrndx).map(sec_bytes).unwrap_or_default();

    let sections: Vec<Section> = headers
        .iter()
        .map(|h| Section {
            name: if h.name_off == 0 { String::new() } else { read_str(&shstrtab, h.name_off).unwrap_or_default() },
            address: h.addr,
            size: h.size,
            file_offset: h.offset,
            has_data: h.sh_type != SHT_NOBITS,
            writable: h.flags & SHF_WRITE != 0,
            executable: h.flags & SHF_EXECINSTR != 0,
            compressed: h.flags & SHF_COMPRESSED != 0,
            region: RegionKind::Global,
        })
        .collect();

    // --- symbols ---
    let sym_entsize = if is64 { 24 } else { 16 };
    let mut symbols = Vec::new();
    if let Some(sym_hdr) = headers.iter().find(|h| h.sh_type == SHT_SYMTAB) {
        let symtab = sec_bytes(sym_hdr);
        let strtab = headers.get(sym_hdr.link as usize).map(sec_bytes).unwrap_or_default();
        let count = symtab.len() / sym_entsize;
        for i in 0..count.min(100_000) {
            let base = i * sym_entsize;
            let (st_name, st_value, st_size, st_info, st_shndx) = if is64 {
                (r.u32(&symtab, base)?, r.u64(&symtab, base + 8)?, r.u64(&symtab, base + 16)?, symtab[base + 4], r.u16(&symtab, base + 6)?)
            } else {
                // ELF32: name(4) value(4) size(4) info(1) other(1) shndx(2)
                (r.u32(&symtab, base)?, r.u32(&symtab, base + 4)? as u64, r.u32(&symtab, base + 8)? as u64, symtab[base + 12], r.u16(&symtab, base + 14)?)
            };
            let name = if st_name == 0 { String::new() } else { read_str(&strtab, st_name).unwrap_or_default() };
            let st_type = st_info & 0xf;
            symbols.push(Symbol {
                name,
                address: st_value,
                size: st_size,
                is_function: st_type == STT_FUNC || st_type == STT_GNU_IFUNC,
                section_index: st_shndx,
            });
        }
    }

    // --- relocations (RELA / REL) ---
    let mut relocations: Vec<(usize, Vec<Relocation>)> = Vec::new();
    for h in &headers {
        if h.sh_type == SHT_RELA {
            let data = sec_bytes(h);
            let esz = if is64 { 24 } else { 12 };
            let count = data.len() / esz;
            let mut rels = Vec::new();
            for i in 0..count.min(100_000) {
                let base = i * esz;
                if is64 {
                    let info = r.u64(&data, base + 8)?;
                    rels.push(Relocation { offset: r.u64(&data, base)?, kind: (info & 0xffff_ffff) as u32, symbol: (info >> 32) as u32, addend: r.u64(&data, base + 16)? as i64 });
                } else {
                    let info = r.u32(&data, base + 4)?;
                    rels.push(Relocation { offset: r.u32(&data, base)? as u64, kind: info & 0xff, symbol: info >> 8, addend: r.u32(&data, base + 8)? as i32 as i64 });
                }
            }
            relocations.push((h.info as usize, rels));
        } else if h.sh_type == SHT_REL {
            let data = sec_bytes(h);
            let esz = if is64 { 16 } else { 8 };
            let count = data.len() / esz;
            let mut rels = Vec::new();
            for i in 0..count.min(100_000) {
                let base = i * esz;
                if is64 {
                    let info = r.u64(&data, base + 8)?;
                    rels.push(Relocation { offset: r.u64(&data, base)?, kind: (info & 0xffff_ffff) as u32, symbol: (info >> 32) as u32, addend: 0 });
                } else {
                    let info = r.u32(&data, base + 4)?;
                    rels.push(Relocation { offset: r.u32(&data, base)? as u64, kind: info & 0xff, symbol: info >> 8, addend: 0 });
                }
            }
            relocations.push((h.info as usize, rels));
        }
    }

    // --- program headers ---
    let mut program_headers = Vec::new();
    let min_phent = if is64 { 56 } else { 32 };
    if e_phoff > 0 && e_phnum > 0 && e_phentsize >= min_phent {
        for i in 0..e_phnum.min(65536) {
            let base = match e_phoff.checked_add(i.saturating_mul(e_phentsize)) {
                Some(b) => b,
                None => break,
            };
            let ph = if is64 {
                ProgramHeader {
                    kind: r.u32(bytes, base).unwrap_or(0),
                    flags: r.u32(bytes, base + 4).unwrap_or(0),
                    offset: r.u64(bytes, base + 8).unwrap_or(0),
                    vaddr: r.u64(bytes, base + 16).unwrap_or(0),
                    paddr: r.u64(bytes, base + 24).unwrap_or(0),
                    file_size: r.u64(bytes, base + 32).unwrap_or(0),
                    mem_size: r.u64(bytes, base + 40).unwrap_or(0),
                    align: r.u64(bytes, base + 48).unwrap_or(0),
                }
            } else {
                // ELF32 program header: type(4) offset(4) vaddr(4) paddr(4) filesz(4) memsz(4) flags(4) align(4)
                match r.u32(bytes, base) {
                    Ok(kind) => ProgramHeader {
                        kind,
                        offset: r.u32(bytes, base + 4).unwrap_or(0) as u64,
                        vaddr: r.u32(bytes, base + 8).unwrap_or(0) as u64,
                        paddr: r.u32(bytes, base + 12).unwrap_or(0) as u64,
                        file_size: r.u32(bytes, base + 16).unwrap_or(0) as u64,
                        mem_size: r.u32(bytes, base + 20).unwrap_or(0) as u64,
                        flags: r.u32(bytes, base + 24).unwrap_or(0),
                        align: r.u32(bytes, base + 28).unwrap_or(0) as u64,
                    },
                    Err(_) => break,
                }
            };
            program_headers.push(ph);
        }
    }
    let _ = e_machine; // used below

    Ok(Image {
        machine: e_machine,
        sections,
        symbols,
        program_headers,
        relocations,
        entry: (e_entry != 0).then_some(e_entry),
        ..Image::default()
    })
}

#[cfg(test)]
#[path = "load_generic_tests.rs"]
mod tests;
