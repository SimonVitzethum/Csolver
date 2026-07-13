use crate::load;

/// Build a minimal ELF32 object (one `.text` section + `.shstrtab`) with the given
/// endianness, so the class/endian-generic reader can be exercised without a toolchain.
fn minimal_elf32(be: bool) -> Vec<u8> {
    let u16b = |v: u16| if be { v.to_be_bytes().to_vec() } else { v.to_le_bytes().to_vec() };
    let u32b = |v: u32| if be { v.to_be_bytes().to_vec() } else { v.to_le_bytes().to_vec() };

    let text = [0x01u8, 0x02, 0x03, 0x04];
    let shstrtab = b"\0.text\0.shstrtab\0"; // .text @1, .shstrtab @7
    let ehsize = 52usize;
    let text_off = ehsize;
    let shstr_off = text_off + text.len();
    let shoff = shstr_off + shstrtab.len();
    let shentsize = 40usize;

    let mut buf = vec![0u8; shoff + 3 * shentsize];
    buf[0..4].copy_from_slice(b"\x7fELF");
    buf[4] = 1; // ELFCLASS32
    buf[5] = if be { 2 } else { 1 };
    buf[6] = 1; // version
    buf[16..18].copy_from_slice(&u16b(1)); // e_type = ET_REL
    buf[18..20].copy_from_slice(&u16b(40)); // e_machine = EM_ARM
    buf[20..24].copy_from_slice(&u32b(1)); // e_version
    buf[24..28].copy_from_slice(&u32b(0x8000)); // e_entry
    buf[32..36].copy_from_slice(&u32b(shoff as u32)); // e_shoff
    buf[40..42].copy_from_slice(&u16b(ehsize as u16));
    buf[46..48].copy_from_slice(&u16b(shentsize as u16));
    buf[48..50].copy_from_slice(&u16b(3)); // e_shnum
    buf[50..52].copy_from_slice(&u16b(2)); // e_shstrndx

    buf[text_off..text_off + text.len()].copy_from_slice(&text);
    buf[shstr_off..shstr_off + shstrtab.len()].copy_from_slice(shstrtab);

    // Section header helper.
    let mut put_sh = |idx: usize, name: u32, ty: u32, flags: u32, addr: u32, off: u32, size: u32| {
        let b = shoff + idx * shentsize;
        buf[b..b + 4].copy_from_slice(&u32b(name));
        buf[b + 4..b + 8].copy_from_slice(&u32b(ty));
        buf[b + 8..b + 12].copy_from_slice(&u32b(flags));
        buf[b + 12..b + 16].copy_from_slice(&u32b(addr));
        buf[b + 16..b + 20].copy_from_slice(&u32b(off));
        buf[b + 20..b + 24].copy_from_slice(&u32b(size));
        buf[b + 32..b + 36].copy_from_slice(&u32b(1)); // addralign
    };
    put_sh(0, 0, 0, 0, 0, 0, 0); // null
    put_sh(1, 1, 1, 0x2 | 0x4, 0x1000, text_off as u32, text.len() as u32); // .text SHF_ALLOC|EXEC
    put_sh(2, 7, 3, 0, 0, shstr_off as u32, shstrtab.len() as u32); // .shstrtab
    buf
}

#[test]
fn elf32_little_endian_sections_and_entry() {
    let img = load(&minimal_elf32(false)).unwrap();
    assert_eq!(img.machine, 40, "EM_ARM");
    assert_eq!(img.entry, Some(0x8000));
    let text = img.sections.iter().find(|s| s.name == ".text").expect(".text present");
    assert!(text.executable);
    assert_eq!(text.address, 0x1000);
    assert_eq!(text.size, 4);
}

#[test]
fn elf32_big_endian_is_parsed_not_rejected() {
    let img = load(&minimal_elf32(true)).unwrap();
    // The 16-bit / 32-bit fields must be decoded big-endian.
    assert_eq!(img.machine, 40);
    assert_eq!(img.entry, Some(0x8000));
    assert!(img.sections.iter().any(|s| s.name == ".text" && s.executable));
}

#[test]
fn elf64_little_endian_still_uses_the_fast_path() {
    // A truncated ELF64-LE must still hit the detailed loader (not the generic one),
    // which is asserted indirectly: the generic path is only reachable for 32/BE.
    let mut buf = vec![0u8; 64];
    buf[0..4].copy_from_slice(b"\x7fELF");
    buf[4] = 2; // ELFCLASS64
    buf[5] = 1; // LE
    buf[18..20].copy_from_slice(&62u16.to_le_bytes()); // EM_X86_64
    buf[52..54].copy_from_slice(&64u16.to_le_bytes()); // e_ehsize
    let img = load(&buf).unwrap();
    assert_eq!(img.machine, 62);
}
