//! A from-scratch Mach-O (macOS/iOS) 64-bit object reader → the common [`Image`].
//!
//! Parses a thin 64-bit Mach-O (`MH_MAGIC_64`) or selects the x86-64 / ARM64 slice of a
//! universal ("fat") binary, then walks the load commands: `LC_SEGMENT_64` for sections
//! (with the segment's protection flags) and `LC_SYMTAB` for the symbol table. A symbol
//! defined in an executable section is treated as a function (Mach-O's `nlist` carries no
//! size, so sizes are estimated from the gap to the next symbol — the `nm`/`atos` style).
//! The output is the same [`Image`] the ELF/PE loaders produce.
//!
//! Little-endian 64-bit only (`x86_64`/`arm64`; the only Mach-O targets the decoders
//! handle). Bounds-checked throughout — the loader is the untrusted-file trust boundary.

use super::*;
use crate::reloc::{read_u32, read_u64};

const MH_MAGIC_64: u32 = 0xfeed_facf; // little-endian file: CF FA ED FE
const FAT_MAGIC_BE: u32 = 0xcafe_babe; // fat header is BIG-endian
const CPU_TYPE_X86_64: u32 = 0x0100_0007;
const CPU_TYPE_ARM64: u32 = 0x0100_000c;

const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x02;

// nlist_64 n_type bits.
const N_STAB: u8 = 0xe0;
const N_TYPE: u8 = 0x0e;
const N_SECT: u8 = 0x0e;

// Segment initprot bits.
const VM_PROT_WRITE: i32 = 0x2;
const VM_PROT_EXECUTE: i32 = 0x4;

/// Whether `bytes` begins with a thin 64-bit Mach-O or a fat (universal) magic.
pub fn is_macho(bytes: &[u8]) -> bool {
    matches!(read_u32(bytes, 0), Ok(MH_MAGIC_64))
        || matches!(read_u32_be(bytes, 0), Ok(FAT_MAGIC_BE))
}

/// Parse a Mach-O image (thin 64-bit, or the x86-64/arm64 slice of a fat binary).
pub fn load(bytes: &[u8]) -> Result<Image> {
    // A universal binary: pick the x86-64 or arm64 slice, parse it, then rebase its
    // file offsets by the slice start so they address the ORIGINAL file (the caller
    // slices the whole file, not the slice).
    if matches!(read_u32_be(bytes, 0), Ok(FAT_MAGIC_BE)) {
        let (off, size) = fat_slice(bytes)?;
        let slice = bytes.get(off..off + size).ok_or_else(|| Error::parse("Mach-O: fat slice out of range"))?;
        let mut img = load_thin(slice)?;
        for s in &mut img.sections {
            if s.has_data {
                s.file_offset += off as u64;
            }
        }
        return Ok(img);
    }
    load_thin(bytes)
}

/// Parse a thin 64-bit Mach-O from `bytes` (offsets are file-relative to `bytes`).
fn load_thin(bytes: &[u8]) -> Result<Image> {
    if read_u32(bytes, 0)? != MH_MAGIC_64 {
        return Err(Error::parse("Mach-O: not a 64-bit little-endian image (MH_MAGIC_64)"));
    }
    let cputype = read_u32(bytes, 4)?;
    let machine = match cputype {
        CPU_TYPE_X86_64 => EM_X86_64,
        CPU_TYPE_ARM64 => EM_AARCH64,
        other => {
            return Err(Error::unsupported(format!(
                "Mach-O: cputype {other:#010x} is not decodable (only x86_64 and arm64)"
            )))
        }
    };
    let ncmds = read_u32(bytes, 16)? as usize;
    // Load commands follow the 32-byte mach_header_64.
    let mut sections: Vec<Section> = vec![null_section()]; // index 0 = placeholder (n_sect is 1-based)
    let mut symbols: Vec<Symbol> = Vec::new();
    let mut entry: Option<u64> = None;
    let mut symtab: Option<(usize, usize, usize, usize)> = None; // (symoff, nsyms, stroff, strsize)
    let mut p = 32usize;
    for _ in 0..ncmds {
        let cmd = read_u32(bytes, p)?;
        let cmdsize = read_u32(bytes, p + 4)? as usize;
        if cmdsize < 8 {
            return Err(Error::parse("Mach-O: load command too small"));
        }
        match cmd {
            LC_SEGMENT_64 => parse_segment(bytes, p, &mut sections)?,
            LC_SYMTAB => {
                symtab = Some((
                    read_u32(bytes, p + 8)? as usize,
                    read_u32(bytes, p + 12)? as usize,
                    read_u32(bytes, p + 16)? as usize,
                    read_u32(bytes, p + 20)? as usize,
                ));
            }
            // LC_MAIN (0x80000028): entryoff is a FILE offset of the entry point.
            0x8000_0028 => entry = read_u64(bytes, p + 8).ok(),
            _ => {}
        }
        p = p.checked_add(cmdsize).ok_or_else(|| Error::parse("Mach-O: load-command overflow"))?;
    }
    if let Some((symoff, nsyms, stroff, strsize)) = symtab {
        let strtab = bytes.get(stroff..stroff + strsize).unwrap_or(&[]);
        symbols = parse_symbols(bytes, symoff, nsyms, strtab, &sections);
    }
    estimate_sizes(&mut symbols, &sections);
    Ok(Image { machine, sections, symbols, entry, ..Image::default() })
}

/// Parse an `LC_SEGMENT_64` command's `nsects` `section_64` records (80 bytes each),
/// carrying the segment's protection flags onto each section.
fn parse_segment(bytes: &[u8], p: usize, sections: &mut Vec<Section>) -> Result<()> {
    // segment_command_64: cmd, cmdsize, segname[16], vmaddr, vmsize, fileoff, filesize,
    // maxprot, initprot, nsects, flags.
    let initprot = read_u32(bytes, p + 60)? as i32;
    let nsects = read_u32(bytes, p + 64)? as usize;
    let seg_writable = initprot & VM_PROT_WRITE != 0;
    let seg_exec = initprot & VM_PROT_EXECUTE != 0;
    let mut s = p + 72; // sections follow the 72-byte segment_command_64 header
    for _ in 0..nsects {
        let sectname = cstr16(bytes, s)?;
        let addr = read_u64(bytes, s + 32)?;
        let size = read_u64(bytes, s + 40)?;
        let offset = read_u32(bytes, s + 48)? as u64;
        // Section flags low byte: S_ZEROFILL (0x1) / S_GB_ZEROFILL (0xc) are bss-like.
        let flags = read_u32(bytes, s + 64)?;
        let zerofill = matches!(flags & 0xff, 0x1 | 0xc);
        sections.push(Section {
            name: sectname,
            address: addr,
            size,
            file_offset: offset,
            has_data: !zerofill && size > 0,
            writable: seg_writable,
            executable: seg_exec,
            compressed: false,
            region: RegionKind::Global,
        });
        s += 80;
    }
    Ok(())
}

/// Parse the `LC_SYMTAB` `nlist_64` array (16 bytes each). A symbol DEFINED in an
/// executable section (`N_SECT`, `n_sect` an executable section) is a function.
fn parse_symbols(bytes: &[u8], symoff: usize, nsyms: usize, strtab: &[u8], sections: &[Section]) -> Vec<Symbol> {
    let mut out = Vec::new();
    for i in 0..nsyms.min(1 << 22) {
        let b = symoff + i * 16;
        let (Ok(n_strx), Some(&n_type), Some(&n_sect), Ok(n_value)) = (
            read_u32(bytes, b),
            bytes.get(b + 4),
            bytes.get(b + 5),
            read_u64(bytes, b + 8),
        ) else {
            break;
        };
        // Skip debug (STAB) symbols and undefined ones (n_sect == 0, N_UNDF).
        if n_type & N_STAB != 0 || (n_type & N_TYPE) != N_SECT || n_sect == 0 {
            continue;
        }
        let exec = sections.get(n_sect as usize).is_some_and(|s| s.executable);
        if !exec {
            continue;
        }
        let name = crate::reloc::read_str(strtab, n_strx).unwrap_or_default();
        // Mach-O C symbols carry a leading underscore; strip it for readability.
        let name = name.strip_prefix('_').unwrap_or(&name).to_string();
        if !name.is_empty() {
            out.push(Symbol { name, address: n_value, size: 0, is_function: true, section_index: n_sect as u16 });
        }
    }
    out
}

/// Pick the x86-64 or arm64 slice of a fat (universal) binary; returns `(offset, size)`.
/// The fat header and `fat_arch` records are **big-endian**.
fn fat_slice(bytes: &[u8]) -> Result<(usize, usize)> {
    let nfat = read_u32_be(bytes, 4)? as usize;
    let mut fallback = None;
    for i in 0..nfat.min(64) {
        let a = 8 + i * 20; // fat_arch: cputype, cpusubtype, offset, size, align (each u32 BE)
        let cputype = read_u32_be(bytes, a)?;
        let offset = read_u32_be(bytes, a + 8)? as usize;
        let size = read_u32_be(bytes, a + 12)? as usize;
        if matches!(cputype, CPU_TYPE_X86_64 | CPU_TYPE_ARM64) {
            return Ok((offset, size));
        }
        fallback.get_or_insert((offset, size));
    }
    fallback.ok_or_else(|| Error::unsupported("Mach-O: fat binary has no x86_64/arm64 slice"))
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

/// A NUL-terminated (or 16-byte-fixed) name field.
fn cstr16(bytes: &[u8], off: usize) -> Result<String> {
    let raw = bytes.get(off..off + 16).ok_or_else(|| Error::parse("Mach-O: truncated name field"))?;
    let end = raw.iter().position(|&c| c == 0).unwrap_or(16);
    Ok(String::from_utf8_lossy(&raw[..end]).into_owned())
}

/// A big-endian `u32` (for the fat header, which is always big-endian).
fn read_u32_be(bytes: &[u8], off: usize) -> Result<u32> {
    let b = bytes.get(off..off + 4).ok_or_else(|| Error::parse("Mach-O: truncated (u32 BE)"))?;
    Ok(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

/// Estimate each function's size from the gap to the next symbol in the same section,
/// clamped to the section end (Mach-O `nlist` carries no size). Sound for decoding.
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
#[path = "macho_tests.rs"]
mod tests;
