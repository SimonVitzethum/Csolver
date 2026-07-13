//! A focused ISO 9660 (CD/DVD image) directory reader → the files it contains.
//!
//! An `.iso` is a *container*, not an object file: it holds a filesystem. This walks the
//! ISO 9660 volume — the Primary (or Joliet Supplementary) Volume Descriptor and the
//! directory tree — and returns each regular file as `(path, byte offset, size)` so the
//! pipeline can slice it out and hand any object file inside (a UEFI `.efi`/PE, a loose
//! `.exe`/`.dll`, a Linux ELF) to [`crate::load_object`]. UEFI boot applications are PE,
//! so this is the route to "check the binaries on a boot/install image".
//!
//! Joliet (UTF-16BE long names) is preferred when present; otherwise the plain ISO 9660
//! names are used, upgraded to the Rock Ridge (SUSP `NM`) POSIX long name when the record
//! carries one. El Torito boot images (the BIOS/UEFI boot loader referenced by the boot-
//! record volume descriptor) are enumerated too, so a boot image's PE is analysed. Bounds-
//! checked throughout — a malformed image yields [`Error`], never a panic (an ISO is
//! untrusted input). A nested `install.wim` is handled by [`crate::wim`].

use super::*;
use crate::reloc::read_u32;

const SECTOR: usize = 2048;
const DIR_FLAG: u8 = 0x02;
const MAX_FILES: usize = 100_000;
const MAX_DEPTH: usize = 32;

/// One regular file found in an ISO: its path, byte offset in the image, and size.
#[derive(Debug, Clone)]
pub struct IsoFile {
    /// Slash-separated path within the image (e.g. `EFI/BOOT/BOOTX64.EFI`).
    pub path: String,
    /// Byte offset of the file's first extent within the image.
    pub offset: usize,
    /// File size in bytes.
    pub size: usize,
}

/// Whether `bytes` looks like an ISO 9660 image (the `CD001` identifier of the first
/// volume descriptor at sector 16).
pub fn is_iso(bytes: &[u8]) -> bool {
    bytes.get(0x8001..0x8006) == Some(b"CD001")
}

/// Enumerate the regular files in an ISO 9660 image.
pub fn list_files(bytes: &[u8]) -> Result<Vec<IsoFile>> {
    if !is_iso(bytes) {
        return Err(Error::parse("ISO: missing 'CD001' volume-descriptor identifier"));
    }
    // Scan the volume-descriptor set (sector 16 onward): prefer a Joliet supplementary
    // descriptor (type 2, UTF-16BE names) over the primary (type 1).
    let mut primary_root: Option<[u8; 34]> = None;
    let mut joliet_root: Option<[u8; 34]> = None;
    let mut vd = 16 * SECTOR;
    for _ in 0..64 {
        let ty = *bytes.get(vd).ok_or_else(|| Error::parse("ISO: truncated volume descriptor"))?;
        if bytes.get(vd + 1..vd + 6) != Some(b"CD001") {
            break;
        }
        match ty {
            1 => primary_root = root_record(bytes, vd),
            2 if is_joliet(bytes, vd) => joliet_root = root_record(bytes, vd),
            255 => break, // volume-descriptor set terminator
            _ => {}
        }
        vd += SECTOR;
    }
    let (root, joliet) = match (joliet_root, primary_root) {
        (Some(r), _) => (r, true),
        (None, Some(r)) => (r, false),
        (None, None) => return Err(Error::parse("ISO: no primary volume descriptor")),
    };
    let mut out = Vec::new();
    walk_dir(bytes, &root, "", joliet, 0, &mut out)?;
    // El Torito boot images (a UEFI/BIOS boot image referenced by the boot-record volume
    // descriptor, not the directory tree) — often a PE bootloader worth analysing.
    out.extend(el_torito_boot_images(bytes));
    Ok(out)
}

/// The boot image(s) an El Torito boot-record volume descriptor points at. The BRVD sits
/// at sector 17 with the `EL TORITO SPECIFICATION` identifier; its pointer (offset 71) is
/// the boot catalog LBA. The catalog's initial/default entry (offset 32) gives the boot
/// image's LBA (offset 8) and its declared sector count (offset 6). Returns an empty vec
/// when absent or malformed (bounds-checked — an ISO is untrusted input).
fn el_torito_boot_images(bytes: &[u8]) -> Vec<IsoFile> {
    let mut out = Vec::new();
    let brvd = 17 * SECTOR;
    // type 0 + "CD001" + "EL TORITO SPECIFICATION" boot-system identifier.
    if bytes.get(brvd) != Some(&0)
        || bytes.get(brvd + 1..brvd + 6) != Some(b"CD001")
        || bytes.get(brvd + 7..brvd + 30) != Some(b"EL TORITO SPECIFICATION")
    {
        return out;
    }
    let Ok(cat_lba) = read_u32(bytes, brvd + 71) else { return out };
    let cat = (cat_lba as usize).saturating_mul(SECTOR);
    // Validation entry (32 bytes) then the initial/default entry at +32.
    let entry = cat + 32;
    // Byte 0 == 0x88 marks a bootable entry.
    if bytes.get(entry) != Some(&0x88) {
        return out;
    }
    let Ok(sectors) = read_u16_le(bytes, entry + 6) else { return out };
    let Ok(img_lba) = read_u32(bytes, entry + 8) else { return out };
    let offset = (img_lba as usize).saturating_mul(SECTOR);
    // The count is in 512-byte virtual sectors (the declared initial load size).
    let size = (sectors as usize).saturating_mul(512);
    if offset < bytes.len() && size > 0 {
        out.push(IsoFile { path: "[EL TORITO] boot image".to_string(), offset, size });
    }
    out
}

/// Read a little-endian u16 at `off` (bounds-checked).
fn read_u16_le(bytes: &[u8], off: usize) -> Result<u16> {
    let b = bytes.get(off..off + 2).ok_or_else(|| Error::parse("ISO: truncated u16"))?;
    Ok(u16::from_le_bytes([b[0], b[1]]))
}

/// The 34-byte root directory record embedded at offset 156 of a volume descriptor.
fn root_record(bytes: &[u8], vd: usize) -> Option<[u8; 34]> {
    bytes.get(vd + 156..vd + 190)?.try_into().ok()
}

/// Whether a supplementary volume descriptor selects Joliet (a UCS-2 escape sequence
/// `%/@`, `%/C`, or `%/E` in the escape-sequences field at offset 88).
fn is_joliet(bytes: &[u8], vd: usize) -> bool {
    let esc = bytes.get(vd + 88..vd + 120).unwrap_or(&[]);
    esc.windows(3).any(|w| w == b"%/@" || w == b"%/C" || w == b"%/E")
}

/// Recursively walk a directory record's extent, collecting regular files.
fn walk_dir(
    bytes: &[u8],
    record: &[u8],
    prefix: &str,
    joliet: bool,
    depth: usize,
    out: &mut Vec<IsoFile>,
) -> Result<()> {
    if depth > MAX_DEPTH || out.len() >= MAX_FILES {
        return Ok(());
    }
    let lba = read_u32(record, 2)? as usize; // extent location (LE half of the both-endian field)
    let len = read_u32(record, 10)? as usize; // data length
    let start = lba.checked_mul(SECTOR).ok_or_else(|| Error::parse("ISO: extent offset overflow"))?;
    let data = bytes.get(start..start + len).ok_or_else(|| Error::parse("ISO: directory extent out of range"))?;

    let mut p = 0usize;
    while p < data.len() {
        let rec_len = data[p] as usize;
        if rec_len == 0 {
            // No more records in this sector — advance to the next sector boundary.
            p = (p / SECTOR + 1) * SECTOR;
            continue;
        }
        if p + rec_len > data.len() || rec_len < 34 {
            break;
        }
        let rec = &data[p..p + rec_len];
        let flags = rec[25];
        let name_len = rec[32] as usize;
        let name_bytes = rec.get(33..33 + name_len).unwrap_or(&[]);
        // Skip the `.` (self, name 0x00) and `..` (parent, 0x01) entries.
        let is_special = name_len == 1 && matches!(name_bytes.first(), Some(0) | Some(1));
        if !is_special {
            // Rock Ridge (SUSP "NM" entries in the System Use area) carries the real POSIX
            // long name on Linux ISOs — prefer it over the truncated ISO 9660 name. Not
            // used for Joliet (which already has the full Unicode name).
            let name = if joliet {
                decode_name(name_bytes, joliet)
            } else {
                let sys_use_start = 33 + name_len + (1 - (name_len & 1));
                let sys_use = rec.get(sys_use_start..).unwrap_or(&[]);
                rock_ridge_name(sys_use).unwrap_or_else(|| decode_name(name_bytes, joliet))
            };
            let child_prefix = if prefix.is_empty() { name.clone() } else { format!("{prefix}/{name}") };
            if flags & DIR_FLAG != 0 {
                walk_dir(bytes, rec, &child_prefix, joliet, depth + 1, out)?;
            } else if out.len() < MAX_FILES {
                let f_lba = read_u32(rec, 2)? as usize;
                let f_len = read_u32(rec, 10)? as usize;
                out.push(IsoFile {
                    path: child_prefix,
                    offset: f_lba.saturating_mul(SECTOR),
                    size: f_len,
                });
            }
        }
        p += rec_len;
    }
    Ok(())
}

/// Recover the Rock Ridge alternate name from a directory record's System Use area: the
/// concatenation of the `NM` (SUSP) entries' bodies. Each SUSP entry is
/// `[sig(2)][len(1)][ver(1)][data…]`; an `NM` body is `[flags(1)][chars…]`. The CONTINUE
/// flag (bit 0) chains parts; the CURRENT (`.`) / PARENT (`..`) flags mark self/parent and
/// yield no name. Returns `None` when no `NM` entry is present. Bounds-checked.
fn rock_ridge_name(sys_use: &[u8]) -> Option<String> {
    let mut name = String::new();
    let mut found = false;
    let mut p = 0usize;
    while p + 4 <= sys_use.len() {
        let len = sys_use[p + 2] as usize;
        if len < 4 || p + len > sys_use.len() {
            break;
        }
        if &sys_use[p..p + 2] == b"NM" && len >= 5 {
            let flags = sys_use[p + 3];
            if flags & 0b110 != 0 {
                return None; // CURRENT (.) or PARENT (..) — not a real file name
            }
            if let Ok(s) = std::str::from_utf8(&sys_use[p + 5..p + len]) {
                name.push_str(s);
                found = true;
            }
        }
        p += len;
    }
    (found && !name.is_empty()).then_some(name)
}

/// Decode a file-identifier: UTF-16BE for Joliet, ASCII otherwise; strip the `;1`
/// version suffix ISO 9660 appends.
fn decode_name(raw: &[u8], joliet: bool) -> String {
    let s = if joliet {
        let units: Vec<u16> = raw.chunks_exact(2).map(|c| u16::from_be_bytes([c[0], c[1]])).collect();
        String::from_utf16_lossy(&units)
    } else {
        String::from_utf8_lossy(raw).into_owned()
    };
    s.rsplit_once(';').map(|(n, _)| n).unwrap_or(&s).to_string()
}

#[cfg(test)]
#[path = "iso_tests.rs"]
mod tests;
