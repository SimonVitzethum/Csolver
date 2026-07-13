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

#[test]
fn rock_ridge_nm_name_overrides_the_short_name() {
    // A System Use area with one NM entry carrying "linux-kernel.efi".
    let long = b"linux-kernel.efi";
    let mut su = vec![b'N', b'M', (5 + long.len()) as u8, 1, 0];
    su.extend_from_slice(long);
    assert_eq!(rock_ridge_name(&su).as_deref(), Some("linux-kernel.efi"));
    // The CURRENT (.) flag (bit 1) yields no name.
    let dot = vec![b'N', b'M', 5u8, 1, 0b010];
    assert_eq!(rock_ridge_name(&dot), None);
    // No NM entry at all → None.
    assert_eq!(rock_ridge_name(&[b'P', b'X', 4, 1]), None);
}

#[test]
fn el_torito_boot_image_is_enumerated() {
    const SECTOR: usize = 2048;
    let mut img = vec![0u8; 22 * SECTOR];
    // Boot-record volume descriptor at sector 17.
    let brvd = 17 * SECTOR;
    img[brvd] = 0;
    img[brvd + 1..brvd + 6].copy_from_slice(b"CD001");
    img[brvd + 6] = 1;
    img[brvd + 7..brvd + 30].copy_from_slice(b"EL TORITO SPECIFICATION");
    img[brvd + 71..brvd + 75].copy_from_slice(&19u32.to_le_bytes()); // boot catalog @ sector 19
    // Boot catalog at sector 19: validation entry then initial/default entry at +32.
    let cat = 19 * SECTOR;
    img[cat] = 0x01; // validation header
    img[cat + 30] = 0x55;
    img[cat + 31] = 0xaa;
    let entry = cat + 32;
    img[entry] = 0x88; // bootable
    img[entry + 6..entry + 8].copy_from_slice(&4u16.to_le_bytes()); // 4 virtual sectors
    img[entry + 8..entry + 12].copy_from_slice(&20u32.to_le_bytes()); // image @ sector 20
    // Put a PE magic at the boot image so it would be recognised.
    let bootimg = 20 * SECTOR;
    img[bootimg..bootimg + 4].copy_from_slice(&[0x4d, 0x5a, 0x90, 0x00]);

    let boots = el_torito_boot_images(&img);
    assert_eq!(boots.len(), 1);
    assert_eq!(boots[0].offset, 20 * SECTOR);
    assert_eq!(boots[0].size, 4 * 512);
}
