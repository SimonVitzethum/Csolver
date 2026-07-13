#![allow(clippy::unwrap_used, clippy::expect_used)]
use super::*;

pub(crate) fn put_u16(out: &mut [u8], off: usize, v: u16) {
    out[off..off + 2].copy_from_slice(&v.to_le_bytes());
}

pub(crate) fn put_u32(out: &mut [u8], off: usize, v: u32) {
    out[off..off + 4].copy_from_slice(&v.to_le_bytes());
}

pub(crate) fn put_u64(out: &mut [u8], off: usize, v: u64) {
    out[off..off + 8].copy_from_slice(&v.to_le_bytes());
}

/// Build a minimal but valid ELF64 image with one `.text` section (4 bytes)
/// and one function symbol `myfunc` of size 4 at vaddr 0x1000.
pub(crate) fn sample_elf() -> Vec<u8> {
    // Layout: [header 64][.text 4][.shstrtab][.strtab][.symtab][shdrs].
    let text: [u8; 4] = [0x31, 0xc0, 0xc3, 0x90]; // xor eax,eax; ret; nop
    let shstr: &[u8] = b"\0.text\0.shstrtab\0.symtab\0.strtab\0";
    let strtab: &[u8] = b"\0myfunc\0";

    let text_off = ELF_HEADER_LEN as u64;
    let shstr_off = text_off + text.len() as u64;
    let strtab_off = shstr_off + shstr.len() as u64;
    let symtab_off = strtab_off + strtab.len() as u64;
    let symtab_size = 2 * SYM_ENTRY_LEN; // null + myfunc
    let shoff = symtab_off + symtab_size;

    let mut out = vec![0u8; (shoff + 5 * SECTION_HEADER_LEN as u64) as usize];
    out[0..4].copy_from_slice(b"\x7fELF");
    out[4] = 2; // ELF64
    out[5] = 1; // little-endian
    out[6] = 1; // version
    put_u16(&mut out, 16, 2); // e_type = ET_EXEC
    put_u16(&mut out, 18, 62); // e_machine = x86-64
    put_u32(&mut out, 20, 1); // e_version
    put_u64(&mut out, 24, 0x1000); // e_entry
    put_u64(&mut out, 40, shoff); // e_shoff
    put_u16(&mut out, 52, ELF_HEADER_LEN as u16); // e_ehsize
    put_u16(&mut out, 58, SECTION_HEADER_LEN as u16); // e_shentsize
    put_u16(&mut out, 60, 5); // e_shnum
    put_u16(&mut out, 62, 2); // e_shstrndx (.shstrtab is section 2)

    out[text_off as usize..(text_off as usize + 4)].copy_from_slice(&text);
    out[shstr_off as usize..(shstr_off as usize + shstr.len())].copy_from_slice(shstr);
    out[strtab_off as usize..(strtab_off as usize + strtab.len())].copy_from_slice(strtab);

    // symtab[1] = myfunc.
    let s1 = symtab_off as usize + SYM_ENTRY_LEN as usize;
    put_u32(&mut out, s1, 1); // st_name -> "myfunc"
    out[s1 + 4] = (1 << 4) | STT_FUNC; // GLOBAL | FUNC
    put_u16(&mut out, s1 + 6, 1); // st_shndx = .text
    put_u64(&mut out, s1 + 8, 0x1000); // st_value
    put_u64(&mut out, s1 + 16, 4); // st_size

    // Section headers (5 × 64); [0]=NULL stays zero.
    let mut sh = |idx: usize, fields: &[(usize, u64, u8)]| {
        let base = shoff as usize + idx * SECTION_HEADER_LEN;
        for &(off, val, width) in fields {
            match width {
                4 => put_u32(&mut out, base + off, val as u32),
                _ => put_u64(&mut out, base + off, val),
            }
        }
    };
    sh(1, &[(0, 1, 4), (4, 1, 4), (8, 0x6, 8), (16, 0x1000, 8), (24, text_off, 8), (32, 4, 8), (48, 16, 8)]);
    sh(2, &[(0, 7, 4), (4, 3, 4), (24, shstr_off, 8), (32, shstr.len() as u64, 8)]);
    sh(3, &[(0, 17, 4), (4, 2, 4), (24, symtab_off, 8), (32, symtab_size, 8), (40, 4, 4), (44, 1, 4), (56, SYM_ENTRY_LEN, 8)]);
    sh(4, &[(0, 25, 4), (4, 3, 4), (24, strtab_off, 8), (32, strtab.len() as u64, 8)]);

    out
}

/// Build an ELF with named sections, proper shstrtab, a symtab, and
/// program headers for more thorough testing.
///
/// Section layout:
///   0: NULL
///   1: .text        (SHT_PROGBITS, addr 0x1000, 8 bytes)
///   2: .data        (SHT_PROGBITS, addr 0x2000, 4 bytes)
///   3: .shstrtab    (SHT_STRTAB)
///   4: .symtab      (SHT_SYMTAB, link=5, info=1)
///   5: .strtab      (SHT_STRTAB)
/// shstrndx = 3 (section 3 is .shstrtab)
pub(crate) fn sample_elf_with_phdr() -> Vec<u8> {
    let text: [u8; 8] = [0x31, 0xc0, 0x31, 0xdb, 0xc3, 0x90, 0x90, 0x90];
    let data: [u8; 4] = [0x01, 0x00, 0x00, 0x00];
    let shstrtab: &[u8] = b"\0.text\0.data\0.shstrtab\0.symtab\0.strtab\0";
    let strtab: &[u8] = b"\0myfunc\0myvar\0";

    // Offsets within shstrtab:
    //   \0  .text\0  .data\0  .shstrtab\0  .symtab\0  .strtab\0
    //   0   1-5     7-11     13-21        23-29      31-37
    // Offsets within strtab:
    //   \0  myfunc\0  myvar\0
    //   0   1-6      8-12
    const SH_NAME_TEXT: u32 = 1;
    const SH_NAME_DATA: u32 = 7;
    const SH_NAME_SHSTRTAB: u32 = 13;
    const SH_NAME_SYMTAB: u32 = 23;
    const SH_NAME_STRTAB: u32 = 31;
    const SY_NAME_MYFUNC: u32 = 1;
    const SY_NAME_OBJECT: u32 = 8;

    let text_off = ELF_HEADER_LEN as u64;
    let data_off = text_off + text.len() as u64;
    let shstr_off = data_off + data.len() as u64;
    let strtab_off = shstr_off + shstrtab.len() as u64;
    let symtab_off = strtab_off + strtab.len() as u64;
    let symtab_size = 3 * SYM_ENTRY_LEN;
    let shnum = 6usize;
    let shoff = symtab_off + symtab_size;
    let phoff = shoff + shnum as u64 * SECTION_HEADER_LEN as u64;

    let total = phoff + 2 * PROGRAM_HEADER_LEN as u64;
    let mut out = vec![0u8; total as usize];

    // ELF header
    out[0..4].copy_from_slice(b"\x7fELF");
    out[4] = 2;
    out[5] = 1;
    out[6] = 1;
    put_u16(&mut out, 16, 2);                        // e_type
    put_u16(&mut out, 18, 62);                       // e_machine = x86-64
    put_u32(&mut out, 20, 1);                        // e_version
    put_u64(&mut out, 24, 0x1000);                   // e_entry
    put_u64(&mut out, 32, phoff);                    // e_phoff
    put_u64(&mut out, 40, shoff);                    // e_shoff
    put_u32(&mut out, 48, 0);                        // e_flags
    put_u16(&mut out, 52, ELF_HEADER_LEN as u16);    // e_ehsize
    put_u16(&mut out, 54, PROGRAM_HEADER_LEN as u16); // e_phentsize
    put_u16(&mut out, 56, 2);                        // e_phnum
    put_u16(&mut out, 58, SECTION_HEADER_LEN as u16); // e_shentsize
    put_u16(&mut out, 60, shnum as u16);             // e_shnum
    put_u16(&mut out, 62, 3);                        // e_shstrndx = .shstrtab

    // Section content
    out[text_off as usize..][..text.len()].copy_from_slice(&text);
    out[data_off as usize..][..data.len()].copy_from_slice(&data);
    out[shstr_off as usize..][..shstrtab.len()].copy_from_slice(shstrtab);
    out[strtab_off as usize..][..strtab.len()].copy_from_slice(strtab);

    // symtab: null entry, myfunc, myvar
    let s1 = symtab_off as usize + SYM_ENTRY_LEN as usize;
    put_u32(&mut out, s1, SY_NAME_MYFUNC);
    out[s1 + 4] = (1 << 4) | STT_FUNC;     // GLOBAL | FUNC
    put_u16(&mut out, s1 + 6, 1);           // st_shndx = .text
    put_u64(&mut out, s1 + 8, 0x1000);      // st_value
    put_u64(&mut out, s1 + 16, 8);          // st_size
    let s2 = symtab_off as usize + 2 * SYM_ENTRY_LEN as usize;
    put_u32(&mut out, s2, SY_NAME_OBJECT);
    out[s2 + 4] = (1 << 4) | STT_OBJECT;   // GLOBAL | OBJECT
    put_u16(&mut out, s2 + 6, 2);           // st_shndx = .data
    put_u64(&mut out, s2 + 8, 0x2000);      // st_value
    put_u64(&mut out, s2 + 16, 4);          // st_size

    // Section headers (6 entries, 64 bytes each)
    let mut w = |idx: usize, off: usize, val: u64, width: u8| {
        let pos = shoff as usize + idx * 64 + off;
        match width {
            4 => put_u32(&mut out, pos, val as u32),
            _ => put_u64(&mut out, pos, val),
        }
    };
    // Section 0: NULL (all zeros already)
    // Section 1: .text
    w(1, 0, SH_NAME_TEXT as u64, 4);
    w(1, 4, 1, 4);            // SHT_PROGBITS
    w(1, 8, 0x6, 8);          // flags (AX)
    w(1, 16, 0x1000, 8);      // addr
    w(1, 24, text_off, 8);    // offset
    w(1, 32, text.len() as u64, 8); // size
    w(1, 48, 16, 8);          // addralign
    // Section 2: .data
    w(2, 0, SH_NAME_DATA as u64, 4);
    w(2, 4, 1, 4);            // SHT_PROGBITS
    w(2, 8, 0x3, 8);          // flags (WA)
    w(2, 16, 0x2000, 8);      // addr
    w(2, 24, data_off, 8);    // offset
    w(2, 32, data.len() as u64, 8); // size
    w(2, 48, 4, 8);           // addralign
    // Section 3: .shstrtab
    w(3, 0, SH_NAME_SHSTRTAB as u64, 4);
    w(3, 4, 3, 4);            // SHT_STRTAB
    w(3, 24, shstr_off, 8);   // offset
    w(3, 32, shstrtab.len() as u64, 8); // size
    // Section 4: .symtab
    w(4, 0, SH_NAME_SYMTAB as u64, 4);
    w(4, 4, 2, 4);            // SHT_SYMTAB
    w(4, 24, symtab_off, 8);  // offset
    w(4, 32, symtab_size, 8); // size
    w(4, 40, 5, 4);           // link -> .strtab
    w(4, 44, 1, 4);           // info (first non-local symbol)
    w(4, 56, SYM_ENTRY_LEN, 8); // entsize
    // Section 5: .strtab
    w(5, 0, SH_NAME_STRTAB as u64, 4);
    w(5, 4, 3, 4);            // SHT_STRTAB
    w(5, 24, strtab_off, 8);  // offset
    w(5, 32, strtab.len() as u64, 8); // size

    // Program headers: PT_LOAD for text and data
    put_u32(&mut out, phoff as usize, 1);             // p_type = PT_LOAD
    put_u32(&mut out, phoff as usize + 4, 5);         // p_flags = R+X
    put_u64(&mut out, phoff as usize + 8, text_off);  // p_offset
    put_u64(&mut out, phoff as usize + 16, 0x1000);   // p_vaddr
    put_u64(&mut out, phoff as usize + 24, 0x1000);   // p_paddr
    put_u64(&mut out, phoff as usize + 32, text.len() as u64); // p_filesz
    put_u64(&mut out, phoff as usize + 40, text.len() as u64); // p_memsz
    put_u64(&mut out, phoff as usize + 48, 0x1000);   // p_align
    let ph2 = phoff as usize + PROGRAM_HEADER_LEN;
    put_u32(&mut out, ph2, 1);                        // p_type = PT_LOAD
    put_u32(&mut out, ph2 + 4, 6);                    // p_flags = R+W
    put_u64(&mut out, ph2 + 8, data_off);             // p_offset
    put_u64(&mut out, ph2 + 16, 0x2000);              // p_vaddr
    put_u64(&mut out, ph2 + 24, 0x2000);              // p_paddr
    put_u64(&mut out, ph2 + 32, data.len() as u64);   // p_filesz
    put_u64(&mut out, ph2 + 40, data.len() as u64);   // p_memsz
    put_u64(&mut out, ph2 + 48, 0x1000);              // p_align

    out
}

// ------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------

#[test]
fn parses_sections_symbols_and_code() {
    let image = sample_elf();
    let img = load(&image).expect("valid ELF");
    assert_eq!(img.entry, Some(0x1000));

    let text = img.sections.iter().find(|s| s.name == ".text").expect(".text");
    assert!(text.executable && !text.writable);
    assert_eq!(text.address, 0x1000);

    let funcs: Vec<_> = img.functions().collect();
    assert_eq!(funcs.len(), 1);
    assert_eq!(funcs[0].name, "myfunc");
    assert_eq!(funcs[0].address, 0x1000);

    let code = img.function_code(funcs[0], &image).expect("code bytes");
    assert_eq!(code, &[0x31, 0xc0, 0xc3, 0x90]);
}

#[test]
fn rejects_non_elf_and_truncation() {
    assert!(load(b"not an elf at all").is_err());
    assert!(load(b"\x7fELF").is_err()); // magic only, truncated
}

#[test]
fn section_lookup_by_address() {
    let image = sample_elf();
    let img = load(&image).unwrap();
    assert_eq!(img.section_at(0x1002).map(|s| s.name.as_str()), Some(".text"));
    assert!(img.section_at(0x9999).is_none());
}

#[test]
fn rejects_truncated_magic_only() {
    assert!(load(&b"\x7fELF"[..4]).is_err());
}

#[test]
fn rejects_header_shorter_than_64() {
    assert!(load(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]).is_err());
}

#[test]
fn elf32_and_big_endian_are_routed_to_the_generic_reader_without_panic() {
    // ELF32 / big-endian are no longer rejected — they dispatch to the class/endian-generic
    // reader (positively tested in load_generic_tests). Flipping only the class/data byte of
    // an ELF64-LE image yields a malformed image; the contract here is merely that parsing is
    // bounds-safe (returns a value, never panics) on such adversarial input.
    let mut e32 = sample_elf();
    e32[4] = 1; // ELFCLASS32
    let _ = load(&e32);
    let mut ebe = sample_elf();
    ebe[5] = 2; // big-endian
    let _ = load(&ebe);
}

#[test]
fn handles_empty_section_table() {
    let mut bytes = vec![0u8; ELF_HEADER_LEN];
    bytes[0..4].copy_from_slice(b"\x7fELF");
    bytes[4] = 2;
    bytes[5] = 1;
    bytes[6] = 1;
    put_u16(&mut bytes, 52, ELF_HEADER_LEN as u16); // e_ehsize = 64
    // shnum = 0
    put_u16(&mut bytes, 60, 0);
    let img = load(&bytes).expect("ELF with no sections should parse");
    assert!(img.sections.is_empty());
    assert!(img.symbols.is_empty());
}

#[test]
fn handles_section_size_overflow() {
    // A section with offset = u64::MAX should not panic.
    let mut elf = sample_elf();
    // Patch the symtab section's offset to a huge value (the symtab
    // is read via section_bytes, so u64::MAX will hit overflow).
    let shoff = read_u64(&elf, 40).unwrap() as usize;
    // Section 3 is .symtab (index 3, byte offset 3*64 within shoff).
    put_u64(&mut elf, shoff + 3 * 64 + 24, u64::MAX); // sh_offset of .symtab
    let result = load(&elf);
    // Must be an error, not a panic.
    assert!(result.is_err());
}

#[test]
fn rejects_shstrndx_out_of_range() {
    let mut elf = sample_elf();
    // Set shstrndx to an index beyond the section table.
    put_u16(&mut elf, 62, 99);
    let img = load(&elf).expect("should still parse (strtab becomes empty)");
    // Sections should parse, but names may be <bad-name-offset-...>
    assert!(!img.sections.is_empty());
}

#[test]
fn rejects_shentsize_too_small() {
    let mut elf = sample_elf();
    put_u16(&mut elf, 58, 48); // shentsize smaller than 64
    assert!(load(&elf).is_err());
}

#[test]
fn function_code_returns_none_for_sizeless_symbol() {
    let elf = sample_elf();
    let img = load(&elf).unwrap();
    let sym = Symbol {
        name: "no_size".into(),
        address: 0x1000,
        size: 0,
        is_function: true,
        section_index: 1,
    };
    assert!(img.function_code(&sym, &elf).is_none());
}

#[test]
fn function_code_returns_none_for_out_of_range() {
    let elf = sample_elf();
    let img = load(&elf).unwrap();
    let sym = Symbol {
        name: "gone".into(),
        address: 0x9999,
        size: 4,
        is_function: true,
        section_index: 1,
    };
    assert!(img.function_code(&sym, &elf).is_none());
}

#[test]
fn function_code_handles_overflow() {
    let elf = sample_elf();
    let img = load(&elf).unwrap();
    let sym = Symbol {
        name: "huge".into(),
        address: u64::MAX - 3,
        size: 8,
        is_function: true,
        section_index: 1,
    };
    // Should return None, not panic.
    assert!(img.function_code(&sym, &elf).is_none());
}

/// Regression: in a relocatable object every section has address 0, so the
/// symbol's section must be resolved by its `section_index`, not by address —
/// otherwise a colliding earlier section slices the wrong bytes (this made
/// every `.o` function decode into garbage → UNKNOWN).
#[test]
fn function_code_resolves_by_section_index_not_address() {
    let bytes = vec![0xAA, 0xBB, 0x31, 0xc0, 0xc3]; // [.other | .text]
    let sec = |name: &str, addr, size, off, exec| Section {
        name: name.into(),
        address: addr,
        size,
        file_offset: off,
        has_data: true,
        writable: false,
        executable: exec,
        compressed: false,
        region: RegionKind::Global,
    };
    let mut null = sec("", 0, 0, 0, false);
    null.has_data = false;
    let img = Image {
        sections: vec![
            null,                          // index 0: NULL
            sec(".other", 0, 2, 0, false), // index 1: also at address 0
            sec(".text", 0, 3, 2, true),   // index 2: the real function bytes
        ],
        ..Default::default()
    };
    let sym = Symbol {
        name: "f".into(),
        address: 0,
        size: 3,
        is_function: true,
        section_index: 2,
    };
    assert_eq!(
        img.function_code(&sym, &bytes),
        Some(&[0x31, 0xc0, 0xc3][..]),
        "must slice from section index 2 (.text), not the colliding .other at address 0"
    );
}
