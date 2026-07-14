//! A focused UDF (Universal Disk Format, ECMA-167 / ISO 13346) reader → the files it contains.
//!
//! Modern install/boot ISOs (every Windows `.iso`, macOS images, large hybrids) are **UDF**:
//! the ISO 9660 side is a compatibility stub while the real files (a `bootx64.efi` PE, a
//! `sources/install.wim` over 4 GB) live in the UDF filesystem. This walks UDF — the Anchor
//! Volume Descriptor Pointer, the Volume Descriptor Sequence (partition + logical volume), the
//! File Set Descriptor, and the directory tree of File Entries / File Identifier Descriptors —
//! and returns each regular file as `(path, byte offset, size)` so the pipeline can slice it out
//! and hand any object file inside to [`crate::load_object`], or an `install.wim` to [`crate::wim`].
//!
//! Little-endian throughout; 2048-byte logical blocks (the near-universal case; a differing
//! logical-block size in the Logical Volume Descriptor is honoured). A file's bytes are located
//! by its **first** allocation extent (Windows/most authored images write files contiguously); a
//! fragmented file's reported size is its whole length, so a later slice covers the first extent.
//! Bounds-checked throughout — a malformed image yields [`Error`], never a panic.

use super::*;
use crate::reloc::{read_u16, read_u32, read_u64};

const SECTOR: usize = 2048;
const MAX_FILES: usize = 200_000;
const MAX_DEPTH: usize = 40;

// Descriptor tag identifiers (ECMA-167).
const TAG_AVDP: u16 = 2; // Anchor Volume Descriptor Pointer
const TAG_PARTITION: u16 = 5;
const TAG_LOGICAL_VOLUME: u16 = 6;
const TAG_FILE_SET: u16 = 256;
const TAG_FILE_ENTRY: u16 = 261;
const TAG_EXT_FILE_ENTRY: u16 = 266;
const TAG_FID: u16 = 257; // File Identifier Descriptor

/// One regular file found in a UDF image: its path, byte offset in the image, and size.
#[derive(Debug, Clone)]
pub struct UdfFile {
    /// Slash-separated path within the image (e.g. `sources/install.wim`).
    pub path: String,
    /// Byte offset of the file's first extent within the image.
    pub offset: usize,
    /// File size in bytes (the information length).
    pub size: usize,
}

/// Whether `bytes` carries a UDF volume: a `BEA01`/`NSR0x` descriptor in the volume-recognition
/// area (sectors 16..=18 typically) — the marker that an ISO is a UDF (or UDF-hybrid) image.
pub fn is_udf(bytes: &[u8]) -> bool {
    (16..24).any(|s| {
        let at = s * SECTOR + 1;
        matches!(bytes.get(at..at + 5), Some(b"NSR02" | b"NSR03" | b"BEA01"))
    })
}

/// The 16-bit descriptor-tag identifier at byte offset `at` (0 if out of range).
fn tag_id(bytes: &[u8], at: usize) -> u16 {
    read_u16(bytes, at).unwrap_or(0)
}

/// Enumerate the regular files in a UDF image.
pub fn list_files(bytes: &[u8]) -> Result<Vec<UdfFile>> {
    // --- Anchor Volume Descriptor Pointer at logical sector 256 ---
    let avdp = 256 * SECTOR;
    if tag_id(bytes, avdp) != TAG_AVDP {
        return Err(Error::parse("UDF: no Anchor Volume Descriptor Pointer at sector 256"));
    }
    // Main Volume Descriptor Sequence extent: length (bytes) @16, location (sector) @20.
    let vds_len = read_u32(bytes, avdp + 16)? as usize;
    let vds_loc = read_u32(bytes, avdp + 20)? as usize;
    let vds_sectors = (vds_len / SECTOR).min(256);

    // --- scan the VDS for the Partition and Logical Volume descriptors ---
    let mut part_start: Option<usize> = None; // partition start, in sectors
    let mut lb_size = SECTOR; // logical block size
    let mut fsd_block: Option<u32> = None; // File Set Descriptor location, in logical blocks
    for i in 0..vds_sectors {
        let d = (vds_loc + i).checked_mul(SECTOR).ok_or_else(|| Error::parse("UDF: VDS offset overflow"))?;
        match tag_id(bytes, d) {
            TAG_PARTITION => part_start = Some(read_u32(bytes, d + 188)? as usize),
            TAG_LOGICAL_VOLUME => {
                let s = read_u32(bytes, d + 212)?;
                if s as usize >= 512 {
                    lb_size = s as usize; // honour a non-2048 logical block size (rare)
                }
                // The File Set Descriptor's long_ad sits in LogicalVolumeContentsUse @248.
                fsd_block = Some(read_u32(bytes, d + 252)?);
            }
            _ => {}
        }
    }
    let part_start = part_start.ok_or_else(|| Error::parse("UDF: no Partition Descriptor"))?;
    let fsd_block = fsd_block.ok_or_else(|| Error::parse("UDF: no Logical Volume Descriptor"))?;

    // physical byte offset of a partition logical block.
    let block_off = |blk: u32| -> Option<usize> {
        part_start.checked_add(blk as usize)?.checked_mul(lb_size)
    };

    // --- File Set Descriptor → root directory ICB (a long_ad @400) ---
    let fsd = block_off(fsd_block).ok_or_else(|| Error::parse("UDF: FSD offset overflow"))?;
    if tag_id(bytes, fsd) != TAG_FILE_SET {
        return Err(Error::parse("UDF: File Set Descriptor tag mismatch"));
    }
    let root_block = read_u32(bytes, fsd + 404)?; // long_ad location @ (400 + 4)

    let mut out = Vec::new();
    walk_dir(bytes, root_block, part_start, lb_size, "", 0, &mut out)?;
    Ok(out)
}

/// The data extent `(byte offset, byte length)` of a File Entry / Extended File Entry — its first
/// allocation descriptor. `None` for an unsupported (embedded/absent) descriptor.
fn file_entry_extent(bytes: &[u8], fe: usize, part_start: usize, lb_size: usize) -> Option<(usize, u64)> {
    let tag = tag_id(bytes, fe);
    if tag != TAG_FILE_ENTRY && tag != TAG_EXT_FILE_ENTRY {
        return None;
    }
    let info_len = read_u64(bytes, fe + 56).ok()?; // InformationLength @56 (both variants)
    // ICB tag flags @ (16 + 18); low 3 bits select the allocation-descriptor form.
    let icb_flags = read_u16(bytes, fe + 34).ok()?;
    let ad_type = icb_flags & 0x7;
    // The allocation-descriptor area follows the extended attributes; its base and the L_EA/L_AD
    // field offsets differ between a File Entry (176 / 168 / 172) and an Extended File Entry
    // (216 / 208 / 212).
    let (ad_base, lea_off) = if tag == TAG_EXT_FILE_ENTRY { (216usize, 208usize) } else { (176usize, 168usize) };
    let l_ea = read_u32(bytes, fe + lea_off).ok()? as usize;
    let ad = fe.checked_add(ad_base)?.checked_add(l_ea)?;
    // ad_type 0 = short_ad (8 bytes: len@0, block@4); 1 = long_ad (16 bytes: len@0, block@4).
    // ad_type 3 = the data is embedded in the entry itself (at `ad`).
    match ad_type {
        0 | 1 => {
            let blk = read_u32(bytes, ad + 4).ok()?;
            let off = part_start.checked_add(blk as usize)?.checked_mul(lb_size)?;
            Some((off, info_len))
        }
        3 => Some((ad, info_len)), // immediate data
        _ => None,
    }
}

/// Recursively walk a directory whose File Entry is at partition logical block `dir_block`.
fn walk_dir(
    bytes: &[u8],
    dir_block: u32,
    part_start: usize,
    lb_size: usize,
    prefix: &str,
    depth: usize,
    out: &mut Vec<UdfFile>,
) -> Result<()> {
    if depth > MAX_DEPTH || out.len() >= MAX_FILES {
        return Ok(());
    }
    let fe = part_start.checked_add(dir_block as usize).and_then(|b| b.checked_mul(lb_size))
        .ok_or_else(|| Error::parse("UDF: directory entry offset overflow"))?;
    let Some((data_off, data_len)) = file_entry_extent(bytes, fe, part_start, lb_size) else {
        return Ok(()); // not a readable directory extent — skip (sound)
    };
    let end = data_off.checked_add(data_len as usize).ok_or_else(|| Error::parse("UDF: dir extent overflow"))?;
    let data = bytes.get(data_off..end.min(bytes.len())).unwrap_or(&[]);

    // The directory data is a sequence of File Identifier Descriptors.
    let mut p = 0usize;
    while p + 38 <= data.len() {
        if tag_id(data, p) != TAG_FID {
            break;
        }
        let characteristics = *data.get(p + 18).unwrap_or(&0);
        let l_fi = *data.get(p + 19).unwrap_or(&0) as usize;
        let child_block = read_u32(data, p + 20 + 4).unwrap_or(0); // ICB long_ad location
        let l_iu = read_u16(data, p + 36).unwrap_or(0) as usize;
        let name_at = p + 38 + l_iu;
        let fid_len = 38 + l_iu + l_fi;
        let padded = fid_len.div_ceil(4) * 4; // FIDs are padded to a 4-byte boundary

        // Skip the parent entry (characteristics bit 3 = 0x08) and deleted entries (bit 2 = 0x04).
        let is_parent = characteristics & 0x08 != 0;
        let is_deleted = characteristics & 0x04 != 0;
        let is_dir = characteristics & 0x02 != 0;
        if !is_parent && !is_deleted && l_fi > 0 {
            if let Some(name) = decode_name(data.get(name_at..name_at + l_fi).unwrap_or(&[])) {
                let child = if prefix.is_empty() { name.clone() } else { format!("{prefix}/{name}") };
                if is_dir {
                    walk_dir(bytes, child_block, part_start, lb_size, &child, depth + 1, out)?;
                } else if out.len() < MAX_FILES {
                    let cfe = part_start.checked_add(child_block as usize).and_then(|b| b.checked_mul(lb_size));
                    if let Some((off, len)) = cfe.and_then(|c| file_entry_extent(bytes, c, part_start, lb_size)) {
                        out.push(UdfFile { path: child, offset: off, size: len as usize });
                    }
                }
            }
        }
        if padded == 0 {
            break;
        }
        p += padded;
    }
    Ok(())
}

/// Decode a UDF file identifier: a leading compression-id byte (8 = 8-bit chars, 16 = UTF-16BE)
/// then the characters. `None` for an empty/invalid identifier.
fn decode_name(raw: &[u8]) -> Option<String> {
    let (&comp, rest) = raw.split_first()?;
    match comp {
        8 => Some(String::from_utf8_lossy(rest).into_owned()),
        16 => {
            let units: Vec<u16> = rest.chunks_exact(2).map(|c| u16::from_be_bytes([c[0], c[1]])).collect();
            Some(String::from_utf16_lossy(&units))
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "udf_tests.rs"]
mod tests;
