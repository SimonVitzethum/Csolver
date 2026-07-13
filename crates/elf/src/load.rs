use super::*;

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
    // ELF32 (ei_class = 1) and big-endian (ei_data = 2) images are parsed by the
    // class/endian-generic reader; this fast path handles the mainstream ELF64-LE case
    // (and also parses the DWARF / hash / version auxiliaries).
    if bytes[4] != 2 || bytes[5] != 1 {
        return crate::load_generic::load_generic(bytes);
    }

    let machine = read_u16(bytes, 18)?;
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
    let max_shnum = bytes.len().saturating_sub(shoff_us).checked_div(shentsize).unwrap_or(0);
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
                compressed: h.flags & SHF_COMPRESSED != 0,
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
        let count = (symtab.len() as u64).checked_div(entsize).unwrap_or(0) as usize;
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
            // Keep EVERY entry (including the index-0 null symbol as an empty
            // placeholder), so `symbols[i]` stays aligned with the symbol-table index
            // — a relocation's `symbol` field indexes this table directly. The null
            // symbol is harmless (empty name, size 0, not a function).
            let st_type = raw.st_info & 0xf;
            symbols.push(Symbol {
                name,
                address: raw.st_value,
                size: raw.st_size,
                is_function: st_type == STT_FUNC || st_type == STT_GNU_IFUNC,
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

    // --- dynamic section (SHT_DYNAMIC) ---
    let mut dynamic_entries: Vec<DynamicEntry> = Vec::new();
    for hdr in &headers {
        if hdr.sh_type == SHT_DYNAMIC {
            let data = section_bytes(bytes, hdr)?;
            let entsize = if hdr.entsize == 0 { 16 } else { hdr.entsize };
            for chunk in data.chunks(entsize as usize) {
                if chunk.len() < 16 {
                    break;
                }
                let tag = u64::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3], chunk[4], chunk[5], chunk[6], chunk[7]]);
                let val = u64::from_le_bytes([chunk[8], chunk[9], chunk[10], chunk[11], chunk[12], chunk[13], chunk[14], chunk[15]]);
                if tag == dt::NULL {
                    break;
                }
                dynamic_entries.push(DynamicEntry { tag, val });
            }
            break; // Only one PT_DYNAMIC / SHT_DYNAMIC is expected.
        }
    }

    // --- relocations (from SHT_RELA / SHT_REL sections) ---
    let mut relocations: Vec<(usize, Vec<Relocation>)> = Vec::new();
    for hdr in &headers {
        if hdr.sh_type == SHT_RELA {
            let rel_data = section_bytes(bytes, hdr)?;
            let rel_entsize = if hdr.entsize == 0 { RELA_ENTRY_LEN } else { hdr.entsize };
            let count = (rel_data.len() as u64).checked_div(rel_entsize).unwrap_or(0) as usize;
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
            relocations.push((hdr.info as usize, rels));
        } else if hdr.sh_type == SHT_REL {
            // REL format: 8-byte entries (offset + info), no explicit addend.
            let rel_data = section_bytes(bytes, hdr)?;
            let rel_entsize = if hdr.entsize == 0 { REL_ENTRY_LEN } else { hdr.entsize };
            let count = (rel_data.len() as u64).checked_div(rel_entsize).unwrap_or(0) as usize;
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
            relocations.push((hdr.info as usize, rels));
        }
    }

    // --- GNU hash table (SHT_GNU_HASH) ---
    let mut gnu_hash: Option<GnuHash> = None;
    if let Some(hdr) = headers.iter().find(|h| h.sh_type == SHT_GNU_HASH) {
        if hdr.size > 0 {
            let data = section_bytes(bytes, hdr).unwrap_or_default();
            gnu_hash = parse_gnu_hash(&data).ok();
        }
    }

    // --- SysV hash table (SHT_HASH / .hash) ---
    let mut sysv_hash: Option<(Vec<u32>, Vec<u32>)> = None;
    if let Some(hdr) = headers.iter().find(|h| h.sh_type == SHT_HASH) {
        if hdr.size > 0 {
            if let Ok(data) = section_bytes(bytes, hdr) {
                sysv_hash = parse_hash(&data).ok();
            }
        }
    }

    // --- Notes (SHT_NOTE) ---
    let mut notes: Vec<Note> = Vec::new();
    for hdr in &headers {
        if hdr.sh_type == SHT_NOTE && hdr.size > 0 {
            if let Ok(data) = section_bytes(bytes, hdr) {
                notes.extend(parse_notes(&data));
            }
        }
    }

    // --- Version info (SHT_GNU_verdef, SHT_GNU_verneed) ---
    let mut verdefs: Vec<VerDef> = Vec::new();
    let mut verneeds: Vec<VerNeed> = Vec::new();
    if let Some(vd_hdr) = headers.iter().find(|h| h.sh_type == SHT_GNU_VERDEF) {
        if vd_hdr.size > 0 {
            let link_strtab = if (vd_hdr.link as usize) < headers.len() {
                section_bytes(bytes, &headers[vd_hdr.link as usize]).ok()
            } else {
                None
            };
            if let Some(ref strtab) = link_strtab {
                if let Ok(data) = section_bytes(bytes, vd_hdr) {
                    verdefs = parse_verdefs(&data, strtab);
                }
            }
        }
    }
    if let Some(vn_hdr) = headers.iter().find(|h| h.sh_type == SHT_GNU_VERNEED) {
        if vn_hdr.size > 0 {
            let link_strtab = if (vn_hdr.link as usize) < headers.len() {
                section_bytes(bytes, &headers[vn_hdr.link as usize]).ok()
            } else {
                None
            };
            if let Some(ref strtab) = link_strtab {
                if let Ok(data) = section_bytes(bytes, vn_hdr) {
                    verneeds = parse_verneeds(&data, strtab);
                }
            }
        }
    }

    Ok(Image {
        machine,
        sections,
        symbols,
        program_headers,
        relocations,
        dynamic_entries,
        entry: (entry != 0).then_some(entry),
        gnu_hash,
        sysv_hash,
        notes,
        verdefs,
        verneeds,
    })
}

/// `e_machine` for x86-64.
pub const EM_X86_64: u16 = 62;
/// `e_machine` for AArch64.
pub const EM_AARCH64: u16 = 183;
