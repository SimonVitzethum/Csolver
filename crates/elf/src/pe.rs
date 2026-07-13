//! A from-scratch PE/COFF (Windows) object reader → the common [`Image`].
//!
//! Parses a Portable Executable image or a COFF object (`.exe`/`.dll`/`.sys`/`.obj`):
//! the DOS stub + PE signature, the COFF file header, the optional header (PE32/PE32+),
//! the section table, and — to enumerate functions — the COFF **symbol table** (present
//! in objects) and/or the **export directory** (the named entry points of a linked
//! image). The output is the same [`Image`] the ELF loader produces, so the assembly
//! frontend decodes a Windows binary through exactly the same path as a Linux one.
//!
//! Little-endian only (Windows targets x86-64 / ARM64, both LE). Bounds-checked
//! throughout — a truncated/malformed file yields [`Error`], never a panic (the loader
//! is the trust boundary between an untrusted file and the analysis).

use super::*;
use crate::reloc::{read_u16, read_u32, u64_to_usize};

const IMAGE_FILE_MACHINE_AMD64: u16 = 0x8664;
const IMAGE_FILE_MACHINE_ARM64: u16 = 0xaa64;
const MAGIC_PE32: u16 = 0x010b;
const MAGIC_PE32PLUS: u16 = 0x020b;

// Section characteristics.
const SCN_CNT_CODE: u32 = 0x0000_0020;
const SCN_CNT_UNINIT: u32 = 0x0000_0080; // .bss-like
const SCN_MEM_EXECUTE: u32 = 0x2000_0000;
const SCN_MEM_WRITE: u32 = 0x8000_0000;

/// Whether `bytes` is a PE/COFF file: either a **linked image** (the DOS `MZ` stub)
/// or a raw **COFF object** (`.obj`/`.lib` member — no DOS stub, the COFF header's
/// `Machine` field is at offset 0). Only the decodable machines are matched for the
/// object case, so arbitrary data does not masquerade as COFF.
pub fn is_pe(bytes: &[u8]) -> bool {
    (bytes.len() >= 2 && bytes[0] == b'M' && bytes[1] == b'Z')
        || matches!(read_u16(bytes, 0), Ok(IMAGE_FILE_MACHINE_AMD64 | IMAGE_FILE_MACHINE_ARM64))
}

/// Parse a PE/COFF image into the common [`Image`].
pub fn load(bytes: &[u8]) -> Result<Image> {
    // A linked image has the `MZ` DOS stub with `e_lfanew`→`PE\0\0`→COFF header; a raw
    // COFF object has the COFF header at offset 0 (no DOS/PE signature).
    let coff = if bytes.first() == Some(&b'M') && bytes.get(1) == Some(&b'Z') {
        let pe_off = u64_to_usize(read_u32(bytes, 0x3c)? as u64, "PE header offset")?;
        if bytes.get(pe_off..pe_off + 4) != Some(b"PE\0\0") {
            return Err(Error::parse("PE: missing 'PE\\0\\0' signature"));
        }
        pe_off + 4
    } else if matches!(read_u16(bytes, 0), Ok(IMAGE_FILE_MACHINE_AMD64 | IMAGE_FILE_MACHINE_ARM64)) {
        0
    } else {
        return Err(Error::parse("PE: not a PE image or COFF object"));
    };
    let machine_raw = read_u16(bytes, coff)?;
    let machine = match machine_raw {
        IMAGE_FILE_MACHINE_AMD64 => EM_X86_64,
        IMAGE_FILE_MACHINE_ARM64 => EM_AARCH64,
        other => {
            return Err(Error::unsupported(format!(
                "PE: machine {other:#06x} is not decodable (only AMD64 and ARM64)"
            )))
        }
    };
    let num_sections = read_u16(bytes, coff + 2)? as usize;
    let ptr_symtab = read_u32(bytes, coff + 8)? as usize;
    let num_symbols = read_u32(bytes, coff + 12)? as usize;
    let opt_size = read_u16(bytes, coff + 16)? as usize;
    let opt = coff + 20; // optional header follows the 20-byte COFF header

    // Optional header: entry point + the export data-directory (index 0). PE32 vs PE32+
    // differ only in the ImageBase width, which shifts the data-directory array.
    let (entry_rva, export_rva, export_size) = if opt_size >= 2 {
        let magic = read_u16(bytes, opt)?;
        let entry = read_u32(bytes, opt + 16).ok(); // AddressOfEntryPoint (RVA)
        // NumberOfRvaAndSizes then the directory array: at opt+92 (PE32) / opt+108 (PE32+).
        let dir_count_off = match magic {
            MAGIC_PE32 => opt + 92,
            MAGIC_PE32PLUS => opt + 108,
            _ => opt, // unknown optional-header magic → no directories
        };
        let dirs = dir_count_off + 4;
        let n_dirs = read_u32(bytes, dir_count_off).unwrap_or(0);
        let (erva, esz) = if matches!(magic, MAGIC_PE32 | MAGIC_PE32PLUS) && n_dirs >= 1 {
            (read_u32(bytes, dirs).unwrap_or(0), read_u32(bytes, dirs + 4).unwrap_or(0))
        } else {
            (0, 0)
        };
        (entry, erva, esz)
    } else {
        (None, 0, 0)
    };

    // Section table: `num_sections` × 40 bytes, right after the optional header.
    let sec_base = opt + opt_size;
    // A long section name is `/N` — an offset into the COFF string table (after the
    // symbols). Only present when there is a symbol table (`.obj`); `None` otherwise.
    let str_tab_off = (ptr_symtab > 0 && num_symbols > 0)
        .then(|| ptr_symtab.checked_add(num_symbols.checked_mul(18).unwrap_or(0)))
        .flatten();
    let mut sections: Vec<Section> = vec![null_section()]; // index 0 = placeholder (SectionNumber is 1-based)
    for i in 0..num_sections {
        let b = sec_base + i * 40;
        let name = section_name(bytes, b, str_tab_off)?;
        let vsize = read_u32(bytes, b + 8)? as u64;
        let vaddr = read_u32(bytes, b + 12)? as u64;
        let raw_size = read_u32(bytes, b + 16)? as u64;
        let raw_ptr = read_u32(bytes, b + 20)? as u64;
        let chars = read_u32(bytes, b + 36)?;
        let executable = chars & SCN_MEM_EXECUTE != 0 || chars & SCN_CNT_CODE != 0;
        let writable = chars & SCN_MEM_WRITE != 0;
        let uninit = chars & SCN_CNT_UNINIT != 0;
        // The in-memory size is VirtualSize; a section may have less raw data (tail
        // zero-filled). Use VirtualSize for bounds so a function at the tail is found.
        let size = if vsize > 0 { vsize } else { raw_size };
        sections.push(Section {
            name,
            address: vaddr,
            size,
            file_offset: raw_ptr,
            has_data: !uninit && raw_ptr > 0 && raw_size > 0,
            writable,
            executable,
            compressed: false,
            // Every PE section maps to a global program region; the read flag is
            // implied for a loaded section and its perms ride on writable/executable.
            region: RegionKind::Global,
        });
    }

    // Symbols: prefer the COFF symbol table (objects); fall back to exports (images).
    let mut symbols = if ptr_symtab > 0 && num_symbols > 0 {
        parse_coff_symbols(bytes, ptr_symtab, num_symbols)?
    } else {
        Vec::new()
    };
    if symbols.iter().all(|s| !s.is_function) {
        symbols.extend(parse_exports(bytes, &sections, export_rva, export_size));
    }
    // A linked `.exe` with neither a COFF symbol table nor exports (a stripped image)
    // still has an entry point: synthesize a function there so at least the entry is
    // analysable. `entry` is an RVA into an executable section.
    if symbols.iter().all(|s| !s.is_function) {
        if let Some(e) = entry_rva.map(u64::from) {
            if let Some(si) = sections.iter().position(|s| s.executable && s.size > 0 && e >= s.address && e < s.address + s.size) {
                symbols.push(Symbol { name: "entry".into(), address: e, size: 0, is_function: true, section_index: si as u16 });
            }
        }
    }
    estimate_sizes(&mut symbols, &sections);

    Ok(Image {
        machine,
        sections,
        symbols,
        entry: entry_rva.map(u64::from),
        ..Image::default()
    })
}

fn null_section() -> Section {
    Section {
        name: String::new(),
        address: 0,
        size: 0,
        file_offset: 0,
        has_data: false,
        writable: false,
        executable: false,
        compressed: false,
        region: RegionKind::Global,
    }
}

/// A section's name: inline (8 bytes, NUL-padded) or `/N` → COFF string table offset.
fn section_name(bytes: &[u8], b: usize, str_tab_off: Option<usize>) -> Result<String> {
    let raw = bytes.get(b..b + 8).ok_or_else(|| Error::parse("PE: truncated section name"))?;
    if raw[0] == b'/' {
        // `/<decimal>` — an offset into the string table for a long name.
        let digits: String = raw[1..].iter().take_while(|&&c| c.is_ascii_digit()).map(|&c| c as char).collect();
        if let (Ok(off), Some(base)) = (digits.parse::<usize>(), str_tab_off) {
            if let Ok(name) = crate::reloc::read_str(bytes.get(base..).unwrap_or(&[]), off as u32) {
                return Ok(name);
            }
        }
    }
    let end = raw.iter().position(|&c| c == 0).unwrap_or(8);
    Ok(String::from_utf8_lossy(&raw[..end]).into_owned())
}

/// Parse the COFF symbol table: 18-byte records, function symbols kept. Names are
/// inline (≤8 bytes) or a string-table offset (first 4 bytes zero → u32 at +4).
fn parse_coff_symbols(bytes: &[u8], ptr: usize, count: usize) -> Result<Vec<Symbol>> {
    let str_base = ptr + count * 18;
    let str_tab = bytes.get(str_base..).unwrap_or(&[]);
    let mut out = Vec::new();
    let mut i = 0;
    while i < count {
        let b = ptr + i * 18;
        let rec = match bytes.get(b..b + 18) {
            Some(r) => r,
            None => break,
        };
        let name = if rec[0..4] == [0, 0, 0, 0] {
            let off = u32::from_le_bytes([rec[4], rec[5], rec[6], rec[7]]);
            crate::reloc::read_str(str_tab, off).unwrap_or_default()
        } else {
            let end = rec[..8].iter().position(|&c| c == 0).unwrap_or(8);
            String::from_utf8_lossy(&rec[..end]).into_owned()
        };
        let value = u32::from_le_bytes([rec[8], rec[9], rec[10], rec[11]]) as u64;
        let sect = i16::from_le_bytes([rec[12], rec[13]]);
        let sym_type = u16::from_le_bytes([rec[14], rec[15]]);
        let aux = rec[17] as usize;
        // A function symbol: complex type FUNCTION (high nibble 0x20) and a real section.
        let is_function = (sym_type & 0xf0) == 0x20 && sect > 0;
        if is_function && !name.is_empty() {
            out.push(Symbol {
                name,
                address: value,
                size: 0, // COFF has no size; estimated later
                is_function: true,
                section_index: sect as u16,
            });
        }
        i += 1 + aux; // skip auxiliary records
    }
    Ok(out)
}

/// Parse the export directory (data-directory 0): named entry points of a linked
/// image. Each export is a function at an RVA; the section index and offset are
/// recovered from the section table. Sizes are estimated later.
fn parse_exports(bytes: &[u8], sections: &[Section], export_rva: u32, export_size: u32) -> Vec<Symbol> {
    if export_rva == 0 || export_size == 0 {
        return Vec::new();
    }
    let Some(dir) = rva_to_off(sections, export_rva as u64) else { return Vec::new() };
    let dir = dir as usize;
    let (n_names, af_rva, an_rva, ao_rva) = match (
        read_u32(bytes, dir + 24),
        read_u32(bytes, dir + 28),
        read_u32(bytes, dir + 32),
        read_u32(bytes, dir + 36),
    ) {
        (Ok(a), Ok(b), Ok(c), Ok(d)) => (a as usize, b, c, d),
        _ => return Vec::new(),
    };
    let mut out = Vec::new();
    for i in 0..n_names.min(65536) {
        let name_ptr = an_rva as u64 + (i * 4) as u64;
        let ord_ptr = ao_rva as u64 + (i * 2) as u64;
        let (Some(np), Some(op)) = (rva_to_off(sections, name_ptr), rva_to_off(sections, ord_ptr)) else { continue };
        let (Ok(name_rva), Ok(ordinal)) = (read_u32(bytes, np as usize), read_u16(bytes, op as usize)) else { continue };
        let func_ptr = af_rva as u64 + (ordinal as u64) * 4;
        let (Some(fp), Some(nameo)) = (rva_to_off(sections, func_ptr), rva_to_off(sections, name_rva as u64)) else { continue };
        let Ok(func_rva) = read_u32(bytes, fp as usize) else { continue };
        let name = crate::reloc::read_str(bytes.get(nameo as usize..).unwrap_or(&[]), 0).unwrap_or_default();
        // The export must land in an executable section to be a decodable function.
        let sec_idx = sections.iter().position(|s| {
            s.executable && s.size > 0 && (func_rva as u64) >= s.address && (func_rva as u64) < s.address + s.size
        });
        if let Some(si) = sec_idx {
            if !name.is_empty() {
                out.push(Symbol { name, address: func_rva as u64, size: 0, is_function: true, section_index: si as u16 });
            }
        }
    }
    out
}

/// Convert an RVA to a file offset via the section it falls in.
fn rva_to_off(sections: &[Section], rva: u64) -> Option<u64> {
    let s = sections.iter().find(|s| s.size > 0 && rva >= s.address && rva < s.address + s.size)?;
    Some(s.file_offset + (rva - s.address))
}

/// COFF/export symbols carry no size. Estimate each function's size as the gap to the
/// next function in the same section (sorted by address), clamped to the section end —
/// the standard `nm`-style heuristic; a function that is the section's last runs to the
/// section end. Sound for decoding: an over-estimate stops at the first `ret`/bad byte.
fn estimate_sizes(symbols: &mut [Symbol], sections: &[Section]) {
    let mut idx: Vec<usize> = (0..symbols.len()).filter(|&i| symbols[i].is_function).collect();
    idx.sort_by_key(|&i| (symbols[i].section_index, symbols[i].address));
    for k in 0..idx.len() {
        let i = idx[k];
        let sec_end = sections
            .get(symbols[i].section_index as usize)
            .map(|s| s.address + s.size)
            .unwrap_or(symbols[i].address);
        let next = idx
            .get(k + 1)
            .filter(|&&j| symbols[j].section_index == symbols[i].section_index)
            .map(|&j| symbols[j].address)
            .unwrap_or(sec_end)
            .min(sec_end);
        if symbols[i].size == 0 {
            symbols[i].size = next.saturating_sub(symbols[i].address);
        }
    }
}

#[cfg(test)]
#[path = "pe_tests.rs"]
mod tests;
