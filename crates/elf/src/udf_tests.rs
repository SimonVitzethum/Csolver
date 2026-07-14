use super::*;

fn put16(b: &mut [u8], off: usize, v: u16) {
    b[off..off + 2].copy_from_slice(&v.to_le_bytes());
}
fn put32(b: &mut [u8], off: usize, v: u32) {
    b[off..off + 4].copy_from_slice(&v.to_le_bytes());
}
fn put64(b: &mut [u8], off: usize, v: u64) {
    b[off..off + 8].copy_from_slice(&v.to_le_bytes());
}

#[test]
fn is_udf_detects_nsr() {
    let mut b = vec![0u8; 20 * SECTOR];
    b[17 * SECTOR + 1..17 * SECTOR + 6].copy_from_slice(b"NSR02");
    assert!(is_udf(&b));
    assert!(!is_udf(&[0u8; 20 * SECTOR]));
}

/// Build a minimal synthetic UDF image (partition start 304) with one directory holding one
/// regular file, exercising the whole walk: AVDP → VDS(partition+LVD) → FSD → root File Entry →
/// File Identifier Descriptor → the file's File Entry → its data extent.
#[test]
fn lists_a_file_from_a_synthetic_udf_volume() {
    const PART: usize = 304; // partition start sector
    let mut b = vec![0u8; 320 * SECTOR];

    // Anchor Volume Descriptor Pointer @ sector 256: Main VDS = 2 sectors @ 257.
    let avdp = 256 * SECTOR;
    put16(&mut b, avdp, TAG_AVDP);
    put32(&mut b, avdp + 16, 2 * SECTOR as u32);
    put32(&mut b, avdp + 20, 257);

    // Partition Descriptor @ 257: partition starts at sector 304.
    let pd = 257 * SECTOR;
    put16(&mut b, pd, TAG_PARTITION);
    put32(&mut b, pd + 188, PART as u32);

    // Logical Volume Descriptor @ 258: 2048-byte blocks, FSD at partition block 0.
    let lvd = 258 * SECTOR;
    put16(&mut b, lvd, TAG_LOGICAL_VOLUME);
    put32(&mut b, lvd + 212, SECTOR as u32);
    put32(&mut b, lvd + 252, 0); // FSD long_ad location (block 0)

    // File Set Descriptor @ partition block 0 (sector 304): root ICB at partition block 2.
    let fsd = PART * SECTOR;
    put16(&mut b, fsd, TAG_FILE_SET);
    put32(&mut b, fsd + 404, 2); // root ICB long_ad location

    // Root directory File Entry @ partition block 2 (sector 306): a long_ad to its data at block 3.
    let root = (PART + 2) * SECTOR;
    put16(&mut b, root, TAG_FILE_ENTRY);
    put16(&mut b, root + 34, 1); // ICB flags: long_ad
    put64(&mut b, root + 56, SECTOR as u64); // information length
    put32(&mut b, root + 172, 16); // L_AD = one long_ad
    put32(&mut b, root + 176, SECTOR as u32); // AD extent length
    put32(&mut b, root + 180, 3); // AD extent location (block 3)

    // Root directory data @ block 3 (sector 307): one FID naming "hello.efi", ICB at block 4.
    let dir = (PART + 3) * SECTOR;
    put16(&mut b, dir, TAG_FID);
    let name = b"\x08hello.efi"; // compression id 8 + ascii
    b[dir + 18] = 0; // characteristics: a regular file (not parent/dir/deleted)
    b[dir + 19] = name.len() as u8; // L_FI
    put32(&mut b, dir + 24, 4); // child ICB long_ad location (block 4)
    put16(&mut b, dir + 36, 0); // L_IU
    b[dir + 38..dir + 38 + name.len()].copy_from_slice(name);

    // The file's File Entry @ block 4 (sector 308): 4-byte data at block 5.
    let fe = (PART + 4) * SECTOR;
    put16(&mut b, fe, TAG_FILE_ENTRY);
    put16(&mut b, fe + 34, 1); // long_ad
    put64(&mut b, fe + 56, 4); // information length = 4 bytes
    put32(&mut b, fe + 172, 16);
    put32(&mut b, fe + 176, 4);
    put32(&mut b, fe + 180, 5); // data at block 5

    // The file data @ block 5 (sector 309): a fake PE magic.
    let data = (PART + 5) * SECTOR;
    b[data..data + 4].copy_from_slice(&[0x4d, 0x5a, 0x90, 0x00]);

    let files = list_files(&b).expect("UDF parses");
    assert_eq!(files.len(), 1, "one regular file: {files:?}");
    assert_eq!(files[0].path, "hello.efi");
    assert_eq!(files[0].size, 4);
    assert_eq!(&b[files[0].offset..files[0].offset + 4], &[0x4d, 0x5a, 0x90, 0x00]);
}

#[test]
fn rejects_without_anchor() {
    assert!(list_files(&[0u8; 300 * SECTOR]).is_err());
}
