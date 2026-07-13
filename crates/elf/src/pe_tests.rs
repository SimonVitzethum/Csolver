use super::*;

/// Build a minimal PE32+ **object** (`.obj`-style: sections have RVA 0, a COFF symbol
/// table names one function) with a single `.text` section holding `code`, and one
/// function symbol `name` at offset 0. Little-endian, as on x86-64 Windows.
fn synth_pe_obj(machine: u16, name: &str, code: &[u8]) -> Vec<u8> {
    let mut b = vec![0u8; 0x40];
    b[0] = b'M';
    b[1] = b'Z';
    let pe_off = 0x40u32;
    b[0x3c..0x40].copy_from_slice(&pe_off.to_le_bytes());
    // PE signature.
    b.extend_from_slice(b"PE\0\0");
    // COFF header (20 bytes).
    let opt_size = 0u16; // an object has no optional header

    // Layout: [COFF hdr 20][section table 40][code][symtab N*18][strtab]
    let sec_base = pe_off as usize + 4 + 20;
    let text_ptr = sec_base + 40;
    let symtab_ptr = text_ptr + code.len();
    let num_symbols = 1u32;
    let mut coff = Vec::new();
    coff.extend_from_slice(&machine.to_le_bytes()); // Machine
    coff.extend_from_slice(&1u16.to_le_bytes()); // NumberOfSections
    coff.extend_from_slice(&0u32.to_le_bytes()); // TimeDateStamp
    coff.extend_from_slice(&(symtab_ptr as u32).to_le_bytes()); // PointerToSymbolTable
    coff.extend_from_slice(&num_symbols.to_le_bytes()); // NumberOfSymbols
    coff.extend_from_slice(&opt_size.to_le_bytes()); // SizeOfOptionalHeader
    coff.extend_from_slice(&0u16.to_le_bytes()); // Characteristics
    b.extend_from_slice(&coff);
    // Section table: one `.text`.
    let mut sec = Vec::new();
    let mut nm = [0u8; 8];
    nm[..5].copy_from_slice(b".text");
    sec.extend_from_slice(&nm);
    sec.extend_from_slice(&(code.len() as u32).to_le_bytes()); // VirtualSize
    sec.extend_from_slice(&0u32.to_le_bytes()); // VirtualAddress (0 in an object)
    sec.extend_from_slice(&(code.len() as u32).to_le_bytes()); // SizeOfRawData
    sec.extend_from_slice(&(text_ptr as u32).to_le_bytes()); // PointerToRawData
    sec.extend_from_slice(&0u32.to_le_bytes()); // PointerToRelocations
    sec.extend_from_slice(&0u32.to_le_bytes()); // PointerToLinenumbers
    sec.extend_from_slice(&0u16.to_le_bytes()); // NumberOfRelocations
    sec.extend_from_slice(&0u16.to_le_bytes()); // NumberOfLinenumbers
    sec.extend_from_slice(&0x6000_0020u32.to_le_bytes()); // CNT_CODE | MEM_EXECUTE | MEM_READ
    b.extend_from_slice(&sec);
    // Code.
    b.extend_from_slice(code);
    // COFF symbol table: one function symbol at section 1, value 0.
    let mut symrec = [0u8; 18];
    let nb = name.as_bytes();
    if nb.len() <= 8 {
        symrec[..nb.len()].copy_from_slice(nb);
    } else {
        // long name: string-table offset (4 at +4). Put it at strtab offset 4.
        symrec[4..8].copy_from_slice(&4u32.to_le_bytes());
    }
    symrec[8..12].copy_from_slice(&0u32.to_le_bytes()); // Value = 0
    symrec[12..14].copy_from_slice(&1i16.to_le_bytes()); // SectionNumber = 1
    symrec[14..16].copy_from_slice(&0x20u16.to_le_bytes()); // Type = FUNCTION (0x20 high nibble)
    symrec[16] = 2; // StorageClass EXTERNAL
    symrec[17] = 0; // no aux
    b.extend_from_slice(&symrec);
    // String table: size prefix + (long name if any).
    let mut strtab = Vec::new();
    if nb.len() > 8 {
        let mut s = Vec::new();
        s.extend_from_slice(nb);
        s.push(0);
        strtab.extend_from_slice(&((s.len() + 4) as u32).to_le_bytes());
        strtab.extend_from_slice(&s);
    } else {
        strtab.extend_from_slice(&4u32.to_le_bytes());
    }
    b.extend_from_slice(&strtab);
    b
}

#[test]
fn is_pe_detects_mz() {
    assert!(pe::is_pe(b"MZ\x90\x00"));
    assert!(!pe::is_pe(b"\x7fELF"));
    assert!(!pe::is_pe(b"M"));
}

#[test]
fn parses_a_coff_object_function() {
    // `ret` (0xc3) as the whole function body.
    let img_bytes = synth_pe_obj(0x8664, "myfunc", &[0xc3]);
    let img = pe::load(&img_bytes).expect("PE loads");
    assert_eq!(img.machine, EM_X86_64);
    let f = img.functions().next().expect("one function");
    assert_eq!(f.name, "myfunc");
    assert_eq!(f.section_index, 1);
    let code = img.function_code(f, &img_bytes).expect("code sliced");
    assert_eq!(code, &[0xc3], "the function's bytes are the `ret`");
}

#[test]
fn arm64_machine_maps() {
    let img_bytes = synth_pe_obj(0xaa64, "f", &[0xc0, 0x03, 0x5f, 0xd6]); // ret (arm64)
    let img = pe::load(&img_bytes).expect("PE loads");
    assert_eq!(img.machine, EM_AARCH64);
}

#[test]
fn long_section_or_symbol_name_via_string_table() {
    let name = "a_very_long_function_name_beyond_eight";
    let img_bytes = synth_pe_obj(0x8664, name, &[0xc3]);
    let img = pe::load(&img_bytes).expect("PE loads");
    assert_eq!(img.functions().next().unwrap().name, name);
}

#[test]
fn rejects_unknown_machine() {
    let img_bytes = synth_pe_obj(0x014c, "f", &[0xc3]); // IMAGE_FILE_MACHINE_I386 (32-bit)
    assert!(pe::load(&img_bytes).is_err(), "i386 is not decodable");
}

#[test]
fn parses_a_raw_coff_object_without_mz() {
    // A `.obj` / `.lib` member has NO DOS `MZ` stub — the COFF header is at offset 0.
    // Layout (all offsets from the COFF start): [COFF 20][section 40][code][sym 18][strtab].
    let code: &[u8] = &[0xc3];
    let sec_base = 20;
    let text_ptr = sec_base + 40;
    let symtab_ptr = text_ptr + code.len();
    let mut b = Vec::new();
    b.extend_from_slice(&0x8664u16.to_le_bytes()); // Machine AMD64 (offset 0 — no DOS stub)
    b.extend_from_slice(&1u16.to_le_bytes()); // NumberOfSections
    b.extend_from_slice(&0u32.to_le_bytes()); // TimeDateStamp
    b.extend_from_slice(&(symtab_ptr as u32).to_le_bytes());
    b.extend_from_slice(&1u32.to_le_bytes()); // NumberOfSymbols
    b.extend_from_slice(&0u16.to_le_bytes()); // SizeOfOptionalHeader (0 for an object)
    b.extend_from_slice(&0u16.to_le_bytes()); // Characteristics
    let mut nm = [0u8; 8];
    nm[..5].copy_from_slice(b".text");
    b.extend_from_slice(&nm);
    b.extend_from_slice(&(code.len() as u32).to_le_bytes()); // VirtualSize
    b.extend_from_slice(&0u32.to_le_bytes()); // VirtualAddress
    b.extend_from_slice(&(code.len() as u32).to_le_bytes()); // SizeOfRawData
    b.extend_from_slice(&(text_ptr as u32).to_le_bytes()); // PointerToRawData
    b.extend_from_slice(&[0u8; 12]); // reloc/lineno pointers + counts
    b.extend_from_slice(&0x6000_0020u32.to_le_bytes()); // Characteristics: code|exec|read
    b.extend_from_slice(code);
    let mut sym = [0u8; 18];
    sym[..1].copy_from_slice(b"f");
    sym[12..14].copy_from_slice(&1i16.to_le_bytes()); // SectionNumber
    sym[14..16].copy_from_slice(&0x20u16.to_le_bytes()); // FUNCTION
    sym[16] = 2;
    b.extend_from_slice(&sym);
    b.extend_from_slice(&4u32.to_le_bytes()); // empty string table

    assert!(pe::is_pe(&b), "a raw COFF object is recognised by its machine magic");
    let img = pe::load(&b).expect("raw COFF object loads");
    assert_eq!(img.machine, EM_X86_64);
    let f = img.functions().next().expect("one function");
    assert_eq!(img.function_code(f, &b), Some(code));
}

#[test]
fn rejects_truncated_and_non_pe() {
    assert!(pe::load(b"MZ").is_err());
    assert!(pe::load(b"not an exe").is_err());
}
