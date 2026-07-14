//! A focused WIM (Windows Imaging Format, `install.wim`/`boot.wim`) container reader.
//!
//! A `.wim` is a *container* like an ISO: it holds a deduplicated pool of file-data
//! *resources* (each a distinct file's contents, keyed by SHA-1), plus per-image metadata
//! resources describing the directory tree, plus an XML block naming the images. To "check
//! the binaries inside a Windows install image" the useful primitive is: enumerate the data
//! resources, decompress each, and hand every blob that looks like an object file to
//! [`crate::load_object`] (a `.exe`/`.dll`/`.sys` inside the WIM is PE). Path *names* live
//! in the metadata tree and are a nice-to-have; the extractable unit is the resource.
//!
//! ## Compression
//!
//! Resources are stored uncompressed or chunked (32 KiB uncompressed chunks). WIM chunk
//! compression is XPRESS-Huffman, LZX, or LZMS. **XPRESS-Huffman** (MS-XCA §2.1) **and LZX**
//! (the default for a Windows `install.wim`/`boot.wim`; see [`crate::lzx`]) are implemented; a
//! chunk stored raw (compressed size == uncompressed size) is copied verbatim. **LZMS is not
//! decoded** — [`extract`] returns [`Error::unsupported`] for it, the honest sound outcome
//! (never fabricated bytes). Decompression is *size-checked*: a chunk that does not decode to
//! its expected length is an error, so a decoder mistake yields a clean failure, never garbage.
//! (The LZX decoder is additionally byte-exact — cross-checked against 1475 real `boot.wim`
//! resources by their stored SHA-1.)
//!
//! Bounds-checked throughout — a malformed image yields [`Error`], never a panic.

use super::*;
use crate::reloc::{read_u32, read_u64};

const MAGIC: &[u8] = b"MSWIM\0\0\0";
const CHUNK_SIZE: usize = 32768;
const LOOKUP_ENTRY_LEN: usize = 50;
const MAX_RESOURCES: usize = 500_000;

// dwFlags (header) — compression selector.
const FLAG_COMPRESS_XPRESS: u32 = 0x0002_0000;
const FLAG_COMPRESS_LZX: u32 = 0x0004_0000;
const FLAG_COMPRESS_LZMS: u32 = 0x0008_0000;

// RESHDR flags (top byte of the first u64).
const RESHDR_FREE: u8 = 0x01;
const RESHDR_METADATA: u8 = 0x02;
const RESHDR_COMPRESSED: u8 = 0x04;

/// The chunk-compression algorithm a WIM uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Compression {
    /// Resources are stored uncompressed.
    None,
    /// XPRESS-Huffman (MS-XCA) — implemented.
    Xpress,
    /// LZX — not decoded (returns [`Error::unsupported`]).
    Lzx,
    /// LZMS — not decoded (returns [`Error::unsupported`]).
    Lzms,
}

/// A resource header (`RESHDR_DISK_SHORT`, 24 bytes): where a resource's bytes live, how
/// big they are in the file, and (if compressed) their uncompressed size.
#[derive(Debug, Clone, Copy)]
pub struct ResHdr {
    /// Byte offset of the resource within the WIM file.
    pub offset: u64,
    /// Size of the resource *in the file* (compressed size when compressed).
    pub size_in_file: u64,
    /// Uncompressed size.
    pub original_size: u64,
    /// RESHDR flag byte (`FREE`/`METADATA`/`COMPRESSED`/`SPANNED`).
    pub flags: u8,
}

impl ResHdr {
    /// Whether the resource's stored bytes are chunk-compressed.
    pub fn compressed(&self) -> bool {
        self.flags & RESHDR_COMPRESSED != 0
    }
    /// Whether this resource is an image's metadata (directory tree), not file data.
    pub fn metadata(&self) -> bool {
        self.flags & RESHDR_METADATA != 0
    }
}

/// One entry of the WIM lookup (offset) table: a data resource and its SHA-1.
#[derive(Debug, Clone)]
pub struct LookupEntry {
    /// The resource's location/size header.
    pub resource: ResHdr,
    /// Reference count (how many directory entries share this blob).
    pub ref_count: u32,
    /// SHA-1 of the uncompressed contents (the deduplication key).
    pub hash: [u8; 20],
}

/// The parsed WIM header (the fields the extractor needs).
#[derive(Debug, Clone)]
pub struct WimHeader {
    /// Chunk-compression algorithm.
    pub compression: Compression,
    /// Number of images in the WIM.
    pub image_count: u32,
    /// The lookup (offset) table resource.
    pub lookup_table: ResHdr,
    /// The XML data resource (UTF-16LE image descriptions).
    pub xml_data: ResHdr,
}

/// Whether `bytes` begins with the WIM `MSWIM\0\0\0` magic.
pub fn is_wim(bytes: &[u8]) -> bool {
    bytes.len() >= 208 && bytes.get(0..8) == Some(MAGIC)
}

/// Parse a 24-byte resource header at `off`.
fn res_hdr(bytes: &[u8], off: usize) -> Result<ResHdr> {
    let packed = read_u64(bytes, off)?;
    Ok(ResHdr {
        // Low 56 bits are the size; the top byte is the flags.
        size_in_file: packed & 0x00ff_ffff_ffff_ffff,
        flags: (packed >> 56) as u8,
        offset: read_u64(bytes, off + 8)?,
        original_size: read_u64(bytes, off + 16)?,
    })
}

/// Parse the WIM header.
pub fn header(bytes: &[u8]) -> Result<WimHeader> {
    if !is_wim(bytes) {
        return Err(Error::parse("WIM: missing 'MSWIM' magic"));
    }
    let flags = read_u32(bytes, 0x10)?;
    let compression = if flags & FLAG_COMPRESS_LZMS != 0 {
        Compression::Lzms
    } else if flags & FLAG_COMPRESS_LZX != 0 {
        Compression::Lzx
    } else if flags & FLAG_COMPRESS_XPRESS != 0 {
        Compression::Xpress
    } else {
        Compression::None
    };
    Ok(WimHeader {
        compression,
        image_count: read_u32(bytes, 0x2c)?,
        lookup_table: res_hdr(bytes, 0x30)?,
        xml_data: res_hdr(bytes, 0x48)?,
    })
}

/// Parse the lookup (offset) table — every data/metadata resource in the WIM.
pub fn lookup_table(bytes: &[u8], hdr: &WimHeader) -> Result<Vec<LookupEntry>> {
    // The lookup table itself is a resource (conventionally uncompressed).
    let table = read_resource(bytes, &hdr.lookup_table, hdr.compression)?;
    let mut out = Vec::new();
    let mut p = 0usize;
    while p + LOOKUP_ENTRY_LEN <= table.len() {
        if out.len() >= MAX_RESOURCES {
            break;
        }
        let resource = res_hdr(&table, p)?;
        let ref_count = read_u32(&table, p + 26)?;
        let hash: [u8; 20] = table
            .get(p + 30..p + 50)
            .and_then(|h| h.try_into().ok())
            .ok_or_else(|| Error::parse("WIM: truncated lookup entry hash"))?;
        out.push(LookupEntry { resource, ref_count, hash });
        p += LOOKUP_ENTRY_LEN;
    }
    Ok(out)
}

/// Read (and decompress if necessary) a resource's full uncompressed bytes.
pub fn read_resource(bytes: &[u8], res: &ResHdr, compression: Compression) -> Result<Vec<u8>> {
    let start = usize::try_from(res.offset).map_err(|_| Error::parse("WIM: resource offset overflow"))?;
    let in_len = usize::try_from(res.size_in_file).map_err(|_| Error::parse("WIM: resource size overflow"))?;
    let orig = usize::try_from(res.original_size).map_err(|_| Error::parse("WIM: resource size overflow"))?;
    let raw = bytes
        .get(start..start.checked_add(in_len).ok_or_else(|| Error::parse("WIM: resource extent overflow"))?)
        .ok_or_else(|| Error::parse("WIM: resource out of range"))?;

    if !res.compressed() {
        return Ok(raw.to_vec());
    }
    match compression {
        Compression::None => Ok(raw.to_vec()),
        Compression::Xpress | Compression::Lzx => decompress_chunked(raw, orig, compression),
        Compression::Lzms => Err(Error::unsupported("WIM: LZMS-compressed resource (not decoded)")),
    }
}

/// Decompress a chunk-compressed resource: a chunk-offset table followed by compressed chunks
/// (XPRESS or LZX per `compression`; a chunk stored raw when compression did not shrink it).
fn decompress_chunked(data: &[u8], original: usize, compression: Compression) -> Result<Vec<u8>> {
    if original == 0 {
        return Ok(Vec::new());
    }
    let num_chunks = original.div_ceil(CHUNK_SIZE);
    // Chunk-offset entries are u32 unless the uncompressed size exceeds 4 GiB. The first
    // chunk's offset is an implicit 0, so the table holds (num_chunks - 1) entries.
    let entry_size = if original > u32::MAX as usize { 8 } else { 4 };
    let table_entries = num_chunks - 1;
    let table_len = table_entries.checked_mul(entry_size).ok_or_else(|| Error::parse("WIM: chunk table overflow"))?;
    if table_len > data.len() {
        return Err(Error::parse("WIM: chunk table out of range"));
    }
    let mut offsets = Vec::with_capacity(num_chunks + 1);
    offsets.push(0usize);
    for i in 0..table_entries {
        let o = if entry_size == 8 {
            usize::try_from(read_u64(data, i * 8)?).map_err(|_| Error::parse("WIM: chunk offset overflow"))?
        } else {
            read_u32(data, i * 4)? as usize
        };
        offsets.push(o);
    }
    let body = table_len; // compressed chunk data begins right after the offset table
    let comp_span = data.len() - body;
    offsets.push(comp_span); // sentinel end for the last chunk

    let mut out = Vec::with_capacity(original);
    for i in 0..num_chunks {
        let cstart = body.checked_add(offsets[i]).ok_or_else(|| Error::parse("WIM: chunk start overflow"))?;
        let cend = body.checked_add(offsets[i + 1]).ok_or_else(|| Error::parse("WIM: chunk end overflow"))?;
        if cstart > cend || cend > data.len() {
            return Err(Error::parse("WIM: chunk extent out of range"));
        }
        let chunk = &data[cstart..cend];
        let this_out = (original - out.len()).min(CHUNK_SIZE);
        if chunk.len() == this_out {
            // Stored uncompressed (compression did not help this chunk).
            out.extend_from_slice(chunk);
        } else {
            let decoded = match compression {
                Compression::Lzx => crate::lzx::decompress(chunk, this_out)?,
                _ => xpress_decompress(chunk, this_out)?,
            };
            out.extend_from_slice(&decoded);
        }
    }
    if out.len() != original {
        return Err(Error::parse("WIM: decompressed size mismatch"));
    }
    Ok(out)
}

/// The UTF-16LE XML block describing the images (names, sizes), if present.
pub fn xml(bytes: &[u8], hdr: &WimHeader) -> Option<String> {
    let raw = read_resource(bytes, &hdr.xml_data, hdr.compression).ok()?;
    let units: Vec<u16> = raw.chunks_exact(2).map(|c| u16::from_le_bytes([c[0], c[1]])).collect();
    Some(String::from_utf16_lossy(&units))
}

/// Enumerate the *data* resources in a WIM (skipping free and metadata resources): each is
/// a distinct file's contents. Pair with [`extract`] to get the bytes for [`crate::load_object`].
pub fn data_resources(bytes: &[u8]) -> Result<Vec<LookupEntry>> {
    let hdr = header(bytes)?;
    Ok(lookup_table(bytes, &hdr)?
        .into_iter()
        .filter(|e| e.resource.flags & RESHDR_FREE == 0 && !e.resource.metadata())
        .collect())
}

/// Decompress a lookup entry's resource to its uncompressed bytes.
pub fn extract(bytes: &[u8], entry: &LookupEntry) -> Result<Vec<u8>> {
    let hdr = header(bytes)?;
    read_resource(bytes, &entry.resource, hdr.compression)
}

// --- XPRESS-Huffman (MS-XCA §2.1) chunk decompressor ------------------------

const XPRESS_NUM_SYMBOLS: usize = 512;
const XPRESS_TABLE_BYTES: usize = XPRESS_NUM_SYMBOLS / 2; // 256 bytes = 512 4-bit lengths
const XPRESS_MIN_MATCH: usize = 3;

/// Decompress one XPRESS-Huffman chunk to exactly `out_size` bytes.
fn xpress_decompress(input: &[u8], out_size: usize) -> Result<Vec<u8>> {
    if input.len() < XPRESS_TABLE_BYTES {
        return Err(Error::parse("WIM: XPRESS chunk shorter than code table"));
    }
    // The chunk opens with 256 bytes holding 512 4-bit code lengths (low nibble first).
    let mut lengths = [0u8; XPRESS_NUM_SYMBOLS];
    for i in 0..XPRESS_TABLE_BYTES {
        let b = input[i];
        lengths[2 * i] = b & 0x0f;
        lengths[2 * i + 1] = b >> 4;
    }
    let table = HuffTable::build(&lengths);
    let mut br = BitReader::new(&input[XPRESS_TABLE_BYTES..]);

    let mut out: Vec<u8> = Vec::with_capacity(out_size);
    while out.len() < out_size {
        let sym = table.decode(&mut br).ok_or_else(|| Error::parse("WIM: XPRESS invalid Huffman code"))?;
        if (sym as usize) < 256 {
            out.push(sym as u8);
            continue;
        }
        // Match: low nibble = length header, next nibble = offset bit count.
        let m = sym as usize - 256;
        let offset_bits = (m >> 4) & 0x0f;
        let mut length = m & 0x0f;
        let offset = (1usize << offset_bits) | br.read_bits(offset_bits).ok_or_else(|| Error::parse("WIM: XPRESS truncated offset"))? as usize;
        if length == 15 {
            // Extended length: one byte, then a 16-bit value if that byte is 255.
            let extra = br.read_aligned_byte().ok_or_else(|| Error::parse("WIM: XPRESS truncated length byte"))?;
            if extra == 255 {
                let lo = br.read_aligned_byte().ok_or_else(|| Error::parse("WIM: XPRESS truncated length"))?;
                let hi = br.read_aligned_byte().ok_or_else(|| Error::parse("WIM: XPRESS truncated length"))?;
                length = u16::from_le_bytes([lo, hi]) as usize;
            } else {
                length += extra as usize;
            }
        }
        length += XPRESS_MIN_MATCH;
        if offset > out.len() {
            return Err(Error::parse("WIM: XPRESS match offset before window start"));
        }
        // Copy the (possibly overlapping) back-reference byte by byte.
        let src = out.len() - offset;
        for k in 0..length {
            if out.len() >= out_size {
                break;
            }
            out.push(out[src + k]);
        }
    }
    Ok(out)
}

/// A canonical-Huffman decode table (zlib/puff style): symbols ordered by (length, value).
struct HuffTable {
    counts: [u16; 16],
    symbols: Vec<u16>,
}

impl HuffTable {
    fn build(lengths: &[u8]) -> HuffTable {
        let mut counts = [0u16; 16];
        for &l in lengths {
            if (l as usize) < 16 {
                counts[l as usize] += 1;
            }
        }
        counts[0] = 0;
        let mut offsets = [0u16; 16];
        for len in 1..16 {
            offsets[len] = offsets[len - 1] + counts[len - 1];
        }
        let total: usize = counts[1..].iter().map(|&c| c as usize).sum();
        let mut symbols = vec![0u16; total];
        let mut next = offsets;
        for (sym, &l) in lengths.iter().enumerate() {
            if l > 0 && (l as usize) < 16 {
                symbols[next[l as usize] as usize] = sym as u16;
                next[l as usize] += 1;
            }
        }
        HuffTable { counts, symbols }
    }

    /// Decode one symbol, reading bits MSB-first (canonical Huffman).
    fn decode(&self, br: &mut BitReader) -> Option<u16> {
        let (mut code, mut first, mut index) = (0i32, 0i32, 0i32);
        for len in 1..16 {
            code |= br.read_bit()? as i32;
            let count = self.counts[len] as i32;
            if code - first < count {
                return self.symbols.get((index + (code - first)) as usize).copied();
            }
            index += count;
            first += count;
            first <<= 1;
            code <<= 1;
        }
        None
    }
}

/// The XPRESS bitstream: 16-bit little-endian words, bits consumed MSB-first, with a
/// separate byte cursor for the aligned extended-length reads.
struct BitReader<'a> {
    data: &'a [u8],
    pos: usize,
    bitbuf: u32,
    bitcount: u32,
}

impl<'a> BitReader<'a> {
    fn new(data: &'a [u8]) -> BitReader<'a> {
        BitReader { data, pos: 0, bitbuf: 0, bitcount: 0 }
    }

    /// Refill from the next 16-bit little-endian word while there is room and input left.
    fn refill(&mut self) {
        while self.bitcount <= 16 && self.pos + 2 <= self.data.len() {
            let w = u16::from_le_bytes([self.data[self.pos], self.data[self.pos + 1]]) as u32;
            self.pos += 2;
            self.bitbuf |= w << (16 - self.bitcount);
            self.bitcount += 16;
        }
    }

    fn read_bit(&mut self) -> Option<u32> {
        if self.bitcount == 0 {
            self.refill();
            if self.bitcount == 0 {
                return None;
            }
        }
        let bit = self.bitbuf >> 31;
        self.bitbuf <<= 1;
        self.bitcount -= 1;
        Some(bit)
    }

    fn read_bits(&mut self, n: usize) -> Option<u32> {
        let mut v = 0u32;
        for _ in 0..n {
            v = (v << 1) | self.read_bit()?;
        }
        Some(v)
    }

    /// Read a byte from the underlying stream at the next unconsumed 16-bit word boundary
    /// (extended match lengths bypass the bit buffer). Any buffered whole words are consumed
    /// first so the cursor tracks the true byte position.
    fn read_aligned_byte(&mut self) -> Option<u8> {
        // Rewind the byte cursor by the whole 16-bit words still sitting in the bit buffer,
        // then take the next byte and re-sync.
        let buffered_words = (self.bitcount / 16) as usize;
        let cursor = self.pos.checked_sub(buffered_words * 2)?;
        let b = *self.data.get(cursor)?;
        self.pos = cursor + 1;
        // Drop the buffered bits; the bit reader re-refills from the new cursor on demand.
        self.bitbuf = 0;
        self.bitcount = 0;
        Some(b)
    }
}

#[cfg(test)]
#[path = "wim_tests.rs"]
mod tests;
