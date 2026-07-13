use super::*;

/// The GNU hash function (a DJB2 variant with shift=33, init=5381).
pub fn gnu_hash(name: &[u8]) -> u32 {
    let mut h: u32 = 5381;
    for &b in name {
        h = h.wrapping_mul(33).wrapping_add(b as u32);
    }
    h
}

/// Parse a GNU hash table from raw bytes.
pub(crate) fn parse_gnu_hash(bytes: &[u8]) -> Result<GnuHash> {
    let nbuckets = read_u32(bytes, 0)?;
    let symoffset = read_u32(bytes, 4)?;
    let bloom_size = read_u32(bytes, 8)?;
    let _bloom_shift = read_u32(bytes, 12)?;
    let bloom_count = usize::try_from(bloom_size).map_err(|_| Error::parse("ELF: bloom_size overflow"))?;
    let bloom_start = 16usize;
    let bloom_end = bloom_start
        .checked_add(bloom_count.checked_mul(8).ok_or_else(|| Error::parse("ELF: bloom table overflow"))?)
        .ok_or_else(|| Error::parse("ELF: bloom table end overflow"))?;
    if bloom_end > bytes.len() {
        return Err(Error::parse("ELF: GNU hash bloom filter truncated"));
    }
    let mut bloom = Vec::with_capacity(bloom_count);
    for i in 0..bloom_count {
        let off = bloom_start + i * 8;
        bloom.push(read_u64(bytes, off)?);
    }
    let nbuckets_us = usize::try_from(nbuckets).map_err(|_| Error::parse("ELF: nbuckets overflow"))?;
    let buckets_start = bloom_end;
    let buckets_end = buckets_start
        .checked_add(nbuckets_us.checked_mul(4).ok_or_else(|| Error::parse("ELF: bucket table overflow"))?)
        .ok_or_else(|| Error::parse("ELF: bucket table end overflow"))?;
    if buckets_end > bytes.len() {
        return Err(Error::parse("ELF: GNU hash bucket table truncated"));
    }
    let mut buckets = Vec::with_capacity(nbuckets_us);
    for i in 0..nbuckets_us {
        let off = buckets_start + i * 4;
        buckets.push(read_u32(bytes, off)?);
    }
    // Chains follow buckets and extend to the end of the section.
    let chain_count = (bytes.len().saturating_sub(buckets_end)) / 4;
    let mut chains = Vec::with_capacity(chain_count);
    for i in 0..chain_count {
        let off = buckets_end + i * 4;
        if off + 4 > bytes.len() {
            break;
        }
        chains.push(read_u32(bytes, off)?);
    }
    Ok(GnuHash {
        nbuckets,
        symoffset,
        bloom,
        buckets,
        chains,
    })
}

/// Parse a SysV-format hash table (`.hash` / `SHT_HASH`).
///
/// The table is an array of `u32` words: `[nbucket, nchain, buckets..., chains...]`.
pub(crate) fn parse_hash(bytes: &[u8]) -> Result<(Vec<u32>, Vec<u32>)> {
    let nbucket = read_u32(bytes, 0)? as usize;
    let nchain = read_u32(bytes, 4)? as usize;
    let bucket_start = 8usize;
    let bucket_end = bucket_start
        .checked_add(nbucket.checked_mul(4).ok_or_else(|| Error::parse("ELF: SysV hash nbucket overflow"))?)
        .ok_or_else(|| Error::parse("ELF: SysV hash bucket end overflow"))?;
    if bucket_end > bytes.len() {
        return Err(Error::parse("ELF: SysV hash bucket table truncated"));
    }
    let chain_end = bucket_end
        .checked_add(nchain.checked_mul(4).ok_or_else(|| Error::parse("ELF: SysV hash nchain overflow"))?)
        .ok_or_else(|| Error::parse("ELF: SysV hash chain end overflow"))?;
    if chain_end > bytes.len() {
        return Err(Error::parse("ELF: SysV hash chain table truncated"));
    }
    let mut buckets = Vec::with_capacity(nbucket);
    for i in 0..nbucket {
        buckets.push(read_u32(bytes, bucket_start + i * 4)?);
    }
    let mut chains = Vec::with_capacity(nchain);
    for i in 0..nchain {
        chains.push(read_u32(bytes, bucket_end + i * 4)?);
    }
    Ok((buckets, chains))
}

/// Parse ELF notes from raw section/program-header bytes.
pub(crate) fn parse_notes(bytes: &[u8]) -> Vec<Note> {
    let mut notes = Vec::new();
    let mut off = 0;
    while off + 12 <= bytes.len() {
        let namesz = u32::from_le_bytes([
            bytes[off],
            bytes[off + 1],
            bytes[off + 2],
            bytes[off + 3],
        ]);
        let descsz = u32::from_le_bytes([
            bytes[off + 4],
            bytes[off + 5],
            bytes[off + 6],
            bytes[off + 7],
        ]);
        let type_ = u32::from_le_bytes([
            bytes[off + 8],
            bytes[off + 9],
            bytes[off + 10],
            bytes[off + 11],
        ]);
        let name_len = usize::try_from(namesz).unwrap_or(0);
        let desc_len = usize::try_from(descsz).unwrap_or(0);
        let name_start = off + 12;
        let desc_start = name_start
            .checked_add(name_len).map(|s| s + (4 - (name_len % 4)) % 4)
            .unwrap_or(bytes.len());
        let desc_end = desc_start
            .checked_add(desc_len).map(|s| s + (4 - (desc_len % 4)) % 4)
            .unwrap_or(bytes.len());
        if name_start + name_len > bytes.len() || desc_start + desc_len > bytes.len() {
            break;
        }
        let name = String::from_utf8_lossy(&bytes[name_start..name_start + name_len]).trim_end_matches('\0').to_string();
        let desc = bytes[desc_start..desc_start + desc_len.min(bytes.len().saturating_sub(desc_start))].to_vec();
        notes.push(Note {
            type_,
            name,
            desc,
        });
        off = desc_end.max(off + 12);
        if off > 0 && desc_end <= off {
            break;
        }
        off = desc_end;
    }
    notes
}

/// Parse version-definition entries from a `SHT_GNU_verdef` section.
pub(crate) fn parse_verdefs(bytes: &[u8], strtab: &[u8]) -> Vec<VerDef> {
    let mut defs = Vec::new();
    let mut off: usize = 0;
    while off + 16 <= bytes.len() {
        let vd_version = u16::from_le_bytes([bytes[off], bytes[off + 1]]);
        if vd_version != 1 {
            break;
        }
        let vd_flags = u16::from_le_bytes([bytes[off + 2], bytes[off + 3]]);
        let vd_ndx = u16::from_le_bytes([bytes[off + 4], bytes[off + 5]]);
        let _vd_cnt = u16::from_le_bytes([bytes[off + 6], bytes[off + 7]]);
        let _vd_hash = u32::from_le_bytes([bytes[off + 8], bytes[off + 9], bytes[off + 10], bytes[off + 11]]);
        let vd_aux = u32::from_le_bytes([bytes[off + 12], bytes[off + 13], bytes[off + 14], bytes[off + 15]]);
        let vd_next = u32::from_le_bytes([bytes[off + 16], bytes[off + 17], bytes[off + 18], bytes[off + 19]]);
        let aux_off = off.checked_add(usize::try_from(vd_aux).unwrap_or(0));
        let name = aux_off
            .and_then(|a| {
                if a + 8 > bytes.len() {
                    return None;
                }
                let vda_name = u32::from_le_bytes([bytes[a], bytes[a + 1], bytes[a + 2], bytes[a + 3]]);
                read_str(strtab, vda_name).ok()
            })
            .unwrap_or_default();
        defs.push(VerDef {
            ndx: vd_ndx,
            flags: vd_flags,
            name,
        });
        if vd_next == 0 {
            break;
        }
        off = off.checked_add(usize::try_from(vd_next).unwrap_or(0)).unwrap_or(bytes.len());
    }
    defs
}

/// Parse version-need entries from a `SHT_GNU_verneed` section.
pub(crate) fn parse_verneeds(bytes: &[u8], strtab: &[u8]) -> Vec<VerNeed> {
    let mut needs = Vec::new();
    let mut off: usize = 0;
    while off + 16 <= bytes.len() {
        let vn_version = u16::from_le_bytes([bytes[off], bytes[off + 1]]);
        if vn_version != 1 {
            break;
        }
        let vn_cnt = u16::from_le_bytes([bytes[off + 2], bytes[off + 3]]);
        let vn_file = u32::from_le_bytes([bytes[off + 4], bytes[off + 5], bytes[off + 6], bytes[off + 7]]);
        let vn_aux = u32::from_le_bytes([bytes[off + 8], bytes[off + 9], bytes[off + 10], bytes[off + 11]]);
        let vn_next = u32::from_le_bytes([bytes[off + 12], bytes[off + 13], bytes[off + 14], bytes[off + 15]]);
        let aux_off = off.checked_add(usize::try_from(vn_aux).unwrap_or(0));
        let file = read_str(strtab, vn_file).unwrap_or_default();
        let mut versions = Vec::new();
        if let Some(mut aoff) = aux_off {
            for _ in 0..vn_cnt {
                if aoff + 16 > bytes.len() {
                    break;
                }
                let _vna_hash = u32::from_le_bytes([bytes[aoff], bytes[aoff + 1], bytes[aoff + 2], bytes[aoff + 3]]);
                let _vna_flags = u16::from_le_bytes([bytes[aoff + 4], bytes[aoff + 5]]);
                let vna_other = u16::from_le_bytes([bytes[aoff + 6], bytes[aoff + 7]]);
                let vna_name = u32::from_le_bytes([bytes[aoff + 8], bytes[aoff + 9], bytes[aoff + 10], bytes[aoff + 11]]);
                let vna_next = u32::from_le_bytes([bytes[aoff + 12], bytes[aoff + 13], bytes[aoff + 14], bytes[aoff + 15]]);
                let version_name = read_str(strtab, vna_name).unwrap_or_default();
                versions.push((vna_other, version_name));
                if vna_next == 0 {
                    break;
                }
                aoff = aoff.checked_add(usize::try_from(vna_next).unwrap_or(0)).unwrap_or(bytes.len());
            }
        }
        needs.push(VerNeed { file, versions });
        if vn_next == 0 {
            break;
        }
        off = off.checked_add(usize::try_from(vn_next).unwrap_or(0)).unwrap_or(bytes.len());
    }
    needs
}

/// Return the file bytes that a section header refers to (empty for NOBITS),
/// bounds-checked. Returns an error for compressed sections (not yet supported).
pub(crate) fn section_bytes(bytes: &[u8], hdr: &SecHdr) -> Result<Vec<u8>> {
    if hdr.sh_type == SHT_NOBITS || hdr.size == 0 {
        return Ok(Vec::new());
    }
    if hdr.flags & SHF_COMPRESSED != 0 {
        return Err(Error::unsupported("ELF: compressed sections not yet supported"));
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
