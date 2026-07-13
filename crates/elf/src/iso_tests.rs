use super::*;

#[test]
fn is_iso_detects_cd001() {
    let mut b = vec![0u8; 0x8006];
    b[0x8001..0x8006].copy_from_slice(b"CD001");
    assert!(iso::is_iso(&b));
    assert!(!iso::is_iso(b"\x7fELF"));
    assert!(!iso::is_iso(&[0u8; 0x8006]));
}

/// Build a minimal single-file ISO 9660 by hand: a primary volume descriptor whose root
/// directory record points at a one-sector directory holding `.`, `..`, and one file.
fn synth_iso(filename: &str, file_data: &[u8]) -> Vec<u8> {
    const SECTOR: usize = 2048;
    // Sector layout: [0..16 system area][16 PVD][17 terminator][18 root dir][19 file data].
    let mut img = vec![0u8; 20 * SECTOR];
    // --- Primary Volume Descriptor at sector 16 ---
    let pvd = 16 * SECTOR;
    img[pvd] = 1; // type = primary
    img[pvd + 1..pvd + 6].copy_from_slice(b"CD001");
    img[pvd + 6] = 1; // version
    // Root directory record at offset 156 (34 bytes): extent = sector 18, len = one sector.
    let root = pvd + 156;
    img[root] = 34; // record length
    write_both_u32(&mut img, root + 2, 18); // extent LBA
    write_both_u32(&mut img, root + 10, SECTOR as u32); // data length
    img[root + 25] = 0x02; // directory flag
    img[root + 32] = 1; // name length
    img[root + 33] = 0; // name = 0x00 (self)
    // --- Volume descriptor set terminator at sector 17 ---
    let term = 17 * SECTOR;
    img[term] = 255;
    img[term + 1..term + 6].copy_from_slice(b"CD001");
    // --- Root directory extent at sector 18 ---
    let dir = 18 * SECTOR;
    // `.` (self) record.
    let mut p = dir;
    p = write_dir_record(&mut img, p, &[0], 18, SECTOR as u32, true);
    // `..` (parent) record.
    p = write_dir_record(&mut img, p, &[1], 18, SECTOR as u32, true);
    // the file, at sector 19.
    let id = format!("{filename};1");
    write_dir_record(&mut img, p, id.as_bytes(), 19, file_data.len() as u32, false);
    // --- File data at sector 19 ---
    let f = 19 * SECTOR;
    img[f..f + file_data.len()].copy_from_slice(file_data);
    img
}

fn write_both_u32(img: &mut [u8], off: usize, v: u32) {
    img[off..off + 4].copy_from_slice(&v.to_le_bytes());
    img[off + 4..off + 8].copy_from_slice(&v.to_be_bytes());
}

fn write_dir_record(img: &mut [u8], p: usize, name: &[u8], lba: u32, len: u32, is_dir: bool) -> usize {
    let mut rec_len = 33 + name.len();
    if rec_len % 2 == 1 {
        rec_len += 1; // pad to even
    }
    img[p] = rec_len as u8;
    write_both_u32(img, p + 2, lba);
    write_both_u32(img, p + 10, len);
    img[p + 25] = if is_dir { 0x02 } else { 0x00 };
    img[p + 32] = name.len() as u8;
    img[p + 33..p + 33 + name.len()].copy_from_slice(name);
    p + rec_len
}

#[test]
fn lists_a_single_file() {
    let img = synth_iso("BOOTX64.EFI", &[0x4d, 0x5a, 0x90, 0x00]); // MZ… (a PE)
    let files = iso::list_files(&img).expect("ISO parses");
    assert_eq!(files.len(), 1, "one regular file: {files:?}");
    assert_eq!(files[0].path, "BOOTX64.EFI");
    assert_eq!(files[0].size, 4);
    // The sliced bytes are the file's content.
    let f = &files[0];
    assert_eq!(&img[f.offset..f.offset + f.size], &[0x4d, 0x5a, 0x90, 0x00]);
}

#[test]
fn strips_version_suffix() {
    let img = synth_iso("KERNEL.BIN", b"data");
    let files = iso::list_files(&img).unwrap();
    assert_eq!(files[0].path, "KERNEL.BIN", "the `;1` version suffix is stripped");
}

#[test]
fn rejects_non_iso() {
    assert!(iso::list_files(b"not an iso").is_err());
    assert!(iso::list_files(&[0u8; 100]).is_err());
}
