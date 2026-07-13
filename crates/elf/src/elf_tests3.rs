use super::*;
use super::tests::*;

/// Build a minimal ELF64 that includes a GNU hash section, a note
/// section, and a version-definition section.
fn elf_with_gnu_hash_and_notes() -> Vec<u8> {
    let text: [u8; 4] = [0xc3, 0x90, 0x90, 0x90];
    // Build-ID note (namesz=4, descsz=20, type=3, name="GNU\0", desc=20 bytes)
    let mut note_section = Vec::new();
    note_section.extend(4u32.to_le_bytes()); // namesz
    note_section.extend(20u32.to_le_bytes()); // descsz
    note_section.extend(3u32.to_le_bytes()); // NT_GNU_BUILD_ID
    note_section.extend(b"GNU\0");
    note_section.extend([0xab; 20]);
    // GNU hash: nbuckets=1, symoffset=0, bloom_size=1, bloom_shift=0,
    //           bloom=[0], buckets=[1], chains=[0]
    let mut gnu_hash_section = Vec::new();
    gnu_hash_section.extend(1u32.to_le_bytes());
    gnu_hash_section.extend(0u32.to_le_bytes());
    gnu_hash_section.extend(1u32.to_le_bytes());
    gnu_hash_section.extend(0u32.to_le_bytes());
    gnu_hash_section.extend(0u64.to_le_bytes());
    gnu_hash_section.extend(1u32.to_le_bytes());
    gnu_hash_section.extend(0u32.to_le_bytes());
    // String tables
    let shstrtab: &[u8] = b"\0.text\0.note\0.gnu.hash\0.shstrtab\0.symtab\0.strtab\0";
    let strtab: &[u8] = b"\0myfunc\0";
    // Offsets within shstrtab:
    //   0: ""  1: ".text"  7: ".note"  13: ".gnu.hash"
    //   23: ".shstrtab"  33: ".symtab"  40: ".strtab"
    // Compute layout
    let text_off = ELF_HEADER_LEN as u64;
    let note_off = text_off + text.len() as u64;
    let ghash_off = note_off + note_section.len() as u64;
    let shstr_off = ghash_off + gnu_hash_section.len() as u64;
    let strtab_off = shstr_off + shstrtab.len() as u64;
    let symtab_off = strtab_off + strtab.len() as u64;
    let symtab_size = 2 * SYM_ENTRY_LEN;
    let shnum = 7usize;
    let shoff = symtab_off + symtab_size;
    let total = shoff + (shnum as u64 * SECTION_HEADER_LEN as u64);
    let mut out = vec![0u8; total as usize];
    // ELF header
    out[0..4].copy_from_slice(b"\x7fELF");
    out[4] = 2; out[5] = 1; out[6] = 1;
    put_u16(&mut out, 16, 2);
    put_u16(&mut out, 18, 62);
    put_u32(&mut out, 20, 1);
    put_u64(&mut out, 40, shoff);
    put_u16(&mut out, 52, ELF_HEADER_LEN as u16);
    put_u16(&mut out, 58, SECTION_HEADER_LEN as u16);
    put_u16(&mut out, 60, shnum as u16);
    put_u16(&mut out, 62, 3); // shstrndx = .shstrtab (section 3)
    // Section content
    let mut fill = |off: u64, data: &[u8]| {
        out[off as usize..][..data.len()].copy_from_slice(data);
    };
    fill(text_off, &text);
    fill(note_off, &note_section);
    fill(ghash_off, &gnu_hash_section);
    fill(shstr_off, shstrtab);
    fill(strtab_off, strtab);
    // Symtab: null + myfunc
    let s1 = symtab_off as usize + SYM_ENTRY_LEN as usize;
    put_u32(&mut out, s1, 1);
    out[s1 + 4] = (1 << 4) | STT_FUNC;
    put_u16(&mut out, s1 + 6, 1);
    put_u64(&mut out, s1 + 8, 0x1000);
    put_u64(&mut out, s1 + 16, 4);
    // Section headers
    let mut w = |idx: usize, off: usize, val: u64, width: u8| {
        let pos = shoff as usize + idx * 64 + off;
        match width { 4 => put_u32(&mut out, pos, val as u32), _ => put_u64(&mut out, pos, val) }
    };
    // Section 0: NULL (all zeros)
    // Section 1: .text
    w(1, 0,   1, 4);          // name_off -> ".text"
    w(1, 4,   1, 4);          // SHT_PROGBITS
    w(1, 8,   0x6, 8);        // AX
    w(1, 16,  0x1000, 8);     // addr
    w(1, 24,  text_off, 8);
    w(1, 32,  text.len() as u64, 8);
    w(1, 48,  16, 8);
    // Section 2: .note
    w(2, 0,   7, 4);
    w(2, 4,   SHT_NOTE as u64, 4);
    w(2, 24,  note_off, 8);
    w(2, 32,  note_section.len() as u64, 8);
    w(2, 48,  4, 8);
    // Section 3: .shstrtab
    w(3, 0,   23, 4);         // name_off = 23
    w(3, 4,   3, 4);          // SHT_STRTAB
    w(3, 24,  shstr_off, 8);
    w(3, 32,  shstrtab.len() as u64, 8);
    w(3, 48,  1, 8);
    // Section 4: .gnu.hash
    w(4, 0,   13, 4);         // name_off = 13
    w(4, 4,   SHT_GNU_HASH as u64, 4);
    w(4, 24,  ghash_off, 8);
    w(4, 32,  gnu_hash_section.len() as u64, 8);
    w(4, 48,  4, 8);
    // Section 5: .symtab
    w(5, 0,   33, 4);
    w(5, 4,   2, 4);
    w(5, 24,  symtab_off, 8);
    w(5, 32,  symtab_size, 8);
    w(5, 40,  6, 4);          // link -> .strtab
    w(5, 44,  1, 4);
    w(5, 56,  SYM_ENTRY_LEN, 8);
    // Section 6: .strtab
    w(6, 0,   41, 4);
    w(6, 4,   3, 4);
    w(6, 24,  strtab_off, 8);
    w(6, 32,  strtab.len() as u64, 8);
    out
}

#[test]
fn loads_elf_with_gnu_hash_and_notes() {
    let elf = elf_with_gnu_hash_and_notes();
    let img = load(&elf).expect("ELF with GNU hash and notes should load");
    // GNU hash
    let gh = img.gnu_hash.as_ref().expect("gnu_hash should be present");
    assert_eq!(gh.nbuckets, 1);
    assert_eq!(gh.buckets, vec![1]);
    assert_eq!(gh.chains, vec![0]);
    // Notes
    assert_eq!(img.notes.len(), 1);
    assert_eq!(img.notes[0].type_, 3);
    assert_eq!(img.notes[0].name, "GNU");
    assert_eq!(img.notes[0].desc.len(), 20);
    // Sections / symbols still parse
    assert!(img.sections.len() >= 2);
    let funcs: Vec<_> = img.functions().collect();
    assert_eq!(funcs.len(), 1);
}

#[test]
fn parse_hash_parses_minimal_table() {
    // SysV hash with 1 bucket, 1 chain (nbucket=1, nchain=1, bucket=0, chain=0)
    let mut data = [0u8; 16];
    put_u32(&mut data, 0, 1); // nbucket
    put_u32(&mut data, 4, 1); // nchain
    put_u32(&mut data, 8, 0); // bucket[0]
    put_u32(&mut data, 12, 0); // chain[0]
    let (buckets, chains) = parse_hash(&data).expect("minimal hash");
    assert_eq!(buckets, vec![0]);
    assert_eq!(chains, vec![0]);
}

#[test]
fn parse_hash_rejects_truncated_buckets() {
    // nbucket=2, nchain=1, but only 1 bucket present
    let mut data = [0u8; 12];
    put_u32(&mut data, 0, 2);
    put_u32(&mut data, 4, 1);
    put_u32(&mut data, 8, 0);
    assert!(parse_hash(&data).is_err());
}

#[test]
fn parse_hash_rejects_truncated_chains() {
    // nbucket=1, nchain=1, bucket present but chain missing
    let mut data = [0u8; 12];
    put_u32(&mut data, 0, 1);
    put_u32(&mut data, 4, 1);
    put_u32(&mut data, 8, 0);
    assert!(parse_hash(&data).is_err());
}

#[test]
fn ifunc_symbol_is_function() {
    // Create a symbol with st_type = STT_GNU_IFUNC (10).
    let mut elf = sample_elf();
    let symtab_off = 0x120;
    elf[symtab_off + 4] = (1 << 4) | STT_GNU_IFUNC; // GLOBAL | IFUNC
    let img = load(&elf).expect("ELF with IFUNC should load");
    let ifunc_syms: Vec<_> = img.symbols.iter().filter(|s| s.is_function).collect();
    assert!(!ifunc_syms.is_empty(), "IFUNC symbol should be is_function");
}

#[test]
fn compressed_section_rejected() {
    let mut elf = sample_elf();
    // Find the first non-null section header (.text)
    let shoff = u64::from_le_bytes([elf[40], elf[41], elf[42], elf[43], elf[44], elf[45], elf[46], elf[47]]) as usize;
    let text_shdr = shoff + SECTION_HEADER_LEN;
    // Read current sh_flags (at offset 8) and add SHF_COMPRESSED
    let old_flags = u64::from_le_bytes([
        elf[text_shdr + 8], elf[text_shdr + 9], elf[text_shdr + 10], elf[text_shdr + 11],
        elf[text_shdr + 12], elf[text_shdr + 13], elf[text_shdr + 14], elf[text_shdr + 15],
    ]);
    put_u64(&mut elf, text_shdr + 8, old_flags | SHF_COMPRESSED);
    let img = load(&elf).expect("ELF with SHF_COMPRESSED should load");
    // Compressed .text section: section_bytes returns an error,
    // so function_code should return None.
    for sym in &img.symbols {
        if sym.is_function {
            assert!(img.function_code(sym, &elf).is_none(),
                "compressed section should make function_code return None");
        }
    }
}

#[test]
fn sysv_hash_in_image() {
    let mut elf = sample_elf();
    // Determine the current section-header table offset and end.
    let shoff = u64::from_le_bytes([elf[40], elf[41], elf[42], elf[43], elf[44], elf[45], elf[46], elf[47]]) as usize;
    let old_shnum = u16::from_le_bytes([elf[0x3c], elf[0x3d]]);
    let sht_end = shoff + old_shnum as usize * SECTION_HEADER_LEN;
    // Place hash data right after the section headers.
    let hash_data_off = sht_end + SECTION_HEADER_LEN; // leave room for new shdr
    let hash_data_size = 16usize;
    // Resize the ELF to fit the extra section header + hash data
    let needed = hash_data_off + hash_data_size;
    if elf.len() < needed {
        elf.resize(needed, 0);
    }
    // New section header at offset sht_end (first free slot)
    put_u32(&mut elf, sht_end, 0); // sh_name
    put_u32(&mut elf, sht_end + 4, SHT_HASH); // sh_type
    put_u64(&mut elf, sht_end + 8, 0); // sh_flags
    put_u64(&mut elf, sht_end + 16, 0); // sh_addr
    put_u64(&mut elf, sht_end + 24, hash_data_off as u64); // sh_offset
    put_u64(&mut elf, sht_end + 32, hash_data_size as u64); // sh_size
    put_u32(&mut elf, sht_end + 40, 0); // sh_link
    put_u32(&mut elf, sht_end + 44, 0); // sh_info
    put_u64(&mut elf, sht_end + 48, 0); // sh_entsize
    // Hash data: nbucket=1, nchain=1, bucket[0]=0, chain[0]=0
    put_u32(&mut elf, hash_data_off, 1);
    put_u32(&mut elf, hash_data_off + 4, 1);
    put_u32(&mut elf, hash_data_off + 8, 0);
    put_u32(&mut elf, hash_data_off + 12, 0);
    // Update e_shnum
    let new_shnum = old_shnum + 1;
    put_u16(&mut elf, 0x3c, new_shnum);
    let img = load(&elf).expect("ELF with SHT_HASH should load");
    let sv = img.sysv_hash.as_ref().expect("sysv_hash should be present");
    assert_eq!(sv.0, vec![0]); // buckets
    assert_eq!(sv.1, vec![0]); // chains
}
