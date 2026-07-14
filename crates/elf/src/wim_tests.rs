use super::*;

/// Write a little-endian u64 into `buf` at `off`.
fn put_u64(buf: &mut [u8], off: usize, v: u64) {
    buf[off..off + 8].copy_from_slice(&v.to_le_bytes());
}
fn put_u32(buf: &mut [u8], off: usize, v: u32) {
    buf[off..off + 4].copy_from_slice(&v.to_le_bytes());
}

/// Pack a RESHDR (size:56 | flags:8, offset, original_size) into a 24-byte record.
fn put_reshdr(buf: &mut [u8], off: usize, size: u64, flags: u8, offset: u64, original: u64) {
    put_u64(buf, off, (size & 0x00ff_ffff_ffff_ffff) | ((flags as u64) << 56));
    put_u64(buf, off + 8, offset);
    put_u64(buf, off + 16, original);
}

/// Build a minimal uncompressed WIM: header + one-entry lookup table + one data resource.
fn minimal_wim(data: &[u8]) -> Vec<u8> {
    let header_len = 208usize;
    let lookup_off = header_len;
    let lookup_len = LOOKUP_ENTRY_LEN;
    let data_off = lookup_off + lookup_len;

    let mut buf = vec![0u8; data_off + data.len()];
    buf[0..8].copy_from_slice(MAGIC);
    put_u32(&mut buf, 0x08, 208); // cbSize
    put_u32(&mut buf, 0x0c, 0x0001_0d00); // dwVersion
    put_u32(&mut buf, 0x10, 0); // dwFlags: uncompressed
    put_u32(&mut buf, 0x2c, 1); // dwImageCount
    // rhOffsetTable → the lookup table resource (uncompressed).
    put_reshdr(&mut buf, 0x30, lookup_len as u64, 0, lookup_off as u64, lookup_len as u64);

    // One lookup entry: a data resource + SHA-1.
    let e = lookup_off;
    put_reshdr(&mut buf, e, data.len() as u64, 0, data_off as u64, data.len() as u64);
    put_u32(&mut buf, e + 26, 1); // ref_count
    buf[e + 30..e + 50].copy_from_slice(&[0xabu8; 20]); // hash

    buf[data_off..].copy_from_slice(data);
    buf
}

#[test]
fn header_and_lookup_table_parse() {
    let wim = minimal_wim(b"MZ\x90\x00fake-pe");
    assert!(is_wim(&wim));
    let hdr = header(&wim).unwrap();
    assert_eq!(hdr.compression, Compression::None);
    assert_eq!(hdr.image_count, 1);
    let table = lookup_table(&wim, &hdr).unwrap();
    assert_eq!(table.len(), 1);
    assert_eq!(table[0].ref_count, 1);
    assert_eq!(table[0].hash, [0xab; 20]);
}

#[test]
fn extract_returns_the_uncompressed_resource_bytes() {
    let payload = b"MZ\x90\x00this-would-be-a-pe-binary";
    let wim = minimal_wim(payload);
    let resources = data_resources(&wim).unwrap();
    assert_eq!(resources.len(), 1, "one data resource, metadata filtered out");
    let bytes = extract(&wim, &resources[0]).unwrap();
    assert_eq!(bytes, payload);
}

#[test]
fn lzx_resource_is_a_clean_unsupported_error() {
    // A compressed resource under LZX must error, never fabricate bytes.
    let res = ResHdr { offset: 0, size_in_file: 4, original_size: 100, flags: RESHDR_COMPRESSED };
    let data = vec![0u8; 8];
    let err = read_resource(&data, &res, Compression::Lzx);
    assert!(err.is_err(), "LZX must not be silently decoded");
}

// --- XPRESS round-trip via a tiny reference encoder --------------------------

/// A bit writer mirroring `BitReader`: bits packed MSB-first into 16-bit LE words.
struct BitWriter {
    out: Vec<u8>,
    word: u32,
    nbits: u32,
}
impl BitWriter {
    fn new() -> BitWriter {
        BitWriter { out: Vec::new(), word: 0, nbits: 0 }
    }
    /// Write `n` bits of `v`, most-significant bit first.
    fn write(&mut self, v: u32, n: u32) {
        for i in (0..n).rev() {
            let bit = (v >> i) & 1;
            self.word = (self.word << 1) | bit;
            self.nbits += 1;
            if self.nbits == 16 {
                self.out.extend_from_slice(&(self.word as u16).to_le_bytes());
                self.word = 0;
                self.nbits = 0;
            }
        }
    }
    fn finish(mut self) -> Vec<u8> {
        if self.nbits > 0 {
            self.word <<= 16 - self.nbits; // left-justify the partial word
            self.out.extend_from_slice(&(self.word as u16).to_le_bytes());
        }
        self.out
    }
}

/// Encode an XPRESS-Huffman chunk with all 512 symbols at code length 9 — then the
/// canonical code of symbol `s` is exactly its 9-bit value, so encoding is trivial and
/// unambiguous. `stream` is a list of `(symbol, extra_value, extra_bits)` tokens.
fn encode_xpress(stream: &[(u16, u32, u32)]) -> Vec<u8> {
    let mut out = vec![0x99u8; XPRESS_TABLE_BYTES]; // 0x99 → both nibbles = 9
    let mut bw = BitWriter::new();
    for &(sym, extra, ebits) in stream {
        bw.write(sym as u32, 9);
        if ebits > 0 {
            bw.write(extra, ebits);
        }
    }
    out.extend_from_slice(&bw.finish());
    out
}

#[test]
fn xpress_decodes_literals() {
    // Three literal bytes 'a','b','c'.
    let chunk = encode_xpress(&[(0x61, 0, 0), (0x62, 0, 0), (0x63, 0, 0)]);
    let got = xpress_decompress(&chunk, 3).unwrap();
    assert_eq!(&got, b"abc");
}

#[test]
fn xpress_decodes_a_back_reference() {
    // "abc" then a match: offset 3, length 3 → "abcabc".
    // match symbol = 256 + (offset_bits<<4) + length_nibble.
    // length 3 = min-match(3) + 0 → length_nibble 0.
    // offset 3 = (1<<1) | 1 → offset_bits 1, extra offset bit = 1.
    let length_nibble = 0;
    let sym = 256 + (1 << 4) + length_nibble;
    let chunk = encode_xpress(&[(0x61, 0, 0), (0x62, 0, 0), (0x63, 0, 0), (sym as u16, 1, 1)]);
    let got = xpress_decompress(&chunk, 6).unwrap();
    assert_eq!(&got, b"abcabc");
}

#[test]
fn chunked_uncompressed_chunk_passes_through() {
    // A single 5-byte chunk stored raw (compressed size == uncompressed size) round-trips
    // through the chunk pipeline without invoking the XPRESS decoder.
    let out = decompress_chunked(b"hello", 5, Compression::Xpress).unwrap();
    assert_eq!(&out, b"hello");
}
