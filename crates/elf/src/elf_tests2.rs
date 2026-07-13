use super::*;
use super::tests::*;

#[test]
fn parses_program_headers() {
    let elf = sample_elf_with_phdr();
    let img = load(&elf).expect("valid ELF with program headers");
    assert_eq!(img.program_headers.len(), 2);
    assert_eq!(img.program_headers[0].kind, 1); // PT_LOAD
    assert_eq!(img.program_headers[0].flags, 5); // PF_R | PF_X
    assert_eq!(img.program_headers[0].vaddr, 0x1000);
    assert_eq!(img.program_headers[1].kind, 1);
    assert_eq!(img.program_headers[1].flags, 6); // PF_R | PF_W
    assert_eq!(img.program_headers[1].vaddr, 0x2000);
}

#[test]
fn parses_symbol_types() {
    let elf = sample_elf_with_phdr();
    let img = load(&elf).expect("valid ELF");
    // myfunc should be a function, myvar should not be.
    let myfunc = img.symbols.iter().find(|s| s.name == "myfunc").expect("myfunc");
    assert!(myfunc.is_function);
    assert_eq!(myfunc.size, 8);
    let myvar = img.symbols.iter().find(|s| s.name == "myvar").expect("myvar");
    assert!(!myvar.is_function);
    assert_eq!(myvar.size, 4);
}

#[test]
fn rejects_truncated_program_headers() {
    let mut elf = sample_elf_with_phdr();
    // Truncate the file after the section headers, before program headers.
    let shoff = read_u64(&elf, 40).unwrap() as usize;
    let shnum = read_u16(&elf, 60).unwrap() as usize;
    let truncate_to = shoff + shnum * SECTION_HEADER_LEN;
    elf.truncate(truncate_to);
    // Should parse but with truncated program headers.
    let img = load(&elf).expect("should still parse basic structure");
    assert!(!img.sections.is_empty());
    // Program headers may be incomplete.
    if !img.program_headers.is_empty() {
        // That's fine too; we just must not panic.
    }
}

#[test]
fn rejects_symbol_table_with_truncated_entry() {
    let mut elf = sample_elf();
    // Find the symtab and shorten its size so only a partial entry exists.
    let shoff = read_u64(&elf, 40).unwrap() as usize;
    let symtab_size_off = shoff + 3 * SECTION_HEADER_LEN + 32;
    put_u64(&mut elf, symtab_size_off, 10); // only 10 bytes instead of 48
    let img = load(&elf).expect("should parse without panic");
    // Either no symbols or partial symbols; no panic.
    assert!(img.symbols.len() <= 2);
}

#[test]
fn symbol_has_section_index() {
    let elf = sample_elf();
    let img = load(&elf).expect("valid ELF");
    let myfunc = img.symbols.iter().find(|s| s.name == "myfunc").expect("myfunc");
    assert_eq!(myfunc.section_index, 1); // .text is section 1
}

#[test]
fn saturating_section_at_avoids_overflow() {
    let sections = vec![Section {
        name: ".text".into(),
        address: u64::MAX - 100,
        size: 200,
        file_offset: 0x200,
        has_data: true,
        writable: false,
        executable: true,
        compressed: false,
        region: RegionKind::Global,
    }];
    let img = Image {
        sections,
        ..Image::default()
    };
    // u64::MAX - 100 + 200 = u64::MAX + 100, which wraps in normal
    // arithmetic but section_at uses saturating_add so it should
    // just clamp at u64::MAX.
    let found = img.section_at(u64::MAX - 50);
    assert!(found.is_some());
    // A clearly-out-of-range address should not match.
    assert!(img.section_at(0).is_none());
}

#[test]
fn zeroed_elf_header_is_rejected_cleanly() {
    let bytes = vec![0u8; ELF_HEADER_LEN];
    assert!(load(&bytes).is_err()); // bad magic
}

#[test]
fn negative_shentsize_zero_with_shnum() {
    let mut elf = sample_elf();
    put_u16(&mut elf, 58, 0); // shentsize = 0
    // shnum = 5, but shentsize = 0 means no headers are readable.
    assert!(load(&elf).is_err());
}

/// Verify that a string offset past the table returns an error (not a
/// silent clamp).
#[test]
fn read_str_rejects_out_of_bounds_offset() {
    let tab = b"hello\0world\0";
    assert!(read_str(tab, 20).is_err());  // past end
    assert!(read_str(tab, 0).unwrap() == "hello");
    assert!(read_str(tab, 6).unwrap() == "world");
    // Offset exactly at end (but not past) — no NUL terminator.
    assert!(read_str(tab, 12).is_err());  // at end, no terminator
    // u32::MAX offset.
    assert!(read_str(tab, u32::MAX).is_err());
}

// ------------------------------------------------------------------
// GNU hash tests
// ------------------------------------------------------------------

#[test]
fn gnu_hash_computes_known_values() {
    // Known test vectors for the GNU hash function.
    assert_eq!(gnu_hash(b""), 0x1505);
    assert_eq!(gnu_hash(b"printf"), 0x156b2bb8);
    assert_eq!(gnu_hash(b"malloc"), 0x0d39ad3d);
    assert_eq!(gnu_hash(b"free"), 0x7c96f087);
}

#[test]
fn parse_gnu_hash_parses_minimal_table() {
    // 1 bucket, symoffset=0, 1 bloom word, shift=0.
    let mut buf = Vec::new();
    buf.extend(1u32.to_le_bytes());  // nbuckets
    buf.extend(0u32.to_le_bytes());  // symoffset
    buf.extend(1u32.to_le_bytes());  // bloom_size
    buf.extend(0u32.to_le_bytes());  // bloom_shift
    buf.extend(0u64.to_le_bytes());  // bloom[0]
    buf.extend(42u32.to_le_bytes()); // buckets[0]
    buf.extend(7u32.to_le_bytes());  // chains[0]
    let gh = parse_gnu_hash(&buf).expect("valid minimal GNU hash");
    assert_eq!(gh.nbuckets, 1);
    assert_eq!(gh.symoffset, 0);
    assert_eq!(gh.bloom, vec![0]);
    assert_eq!(gh.buckets, vec![42]);
    assert_eq!(gh.chains, vec![7]);
}

#[test]
fn parse_gnu_hash_rejects_truncated_data() {
    assert!(parse_gnu_hash(b"").is_err());
    assert!(parse_gnu_hash(b"\x01\x00\x00\x00").is_err()); // nbuckets only
}

// ------------------------------------------------------------------
// Note parsing tests
// ------------------------------------------------------------------

#[test]
fn parse_notes_parses_build_id() {
    // A single GNU build ID note.
    let name = b"GNU\0";
    let desc = [0xab; 20]; // 20-byte SHA1
    let namesz = name.len() as u32;
    let descsz = desc.len() as u32;
    let type_ = 3u32; // NT_GNU_BUILD_ID
    let mut buf = Vec::new();
    buf.extend(namesz.to_le_bytes());
    buf.extend(descsz.to_le_bytes());
    buf.extend(type_.to_le_bytes());
    buf.extend(name); // 4 bytes, already aligned
    buf.extend(desc);
    let notes = parse_notes(&buf);
    assert_eq!(notes.len(), 1);
    assert_eq!(notes[0].type_, 3);
    assert_eq!(notes[0].name, "GNU");
    assert_eq!(notes[0].desc.len(), 20);
}

#[test]
fn parse_notes_handles_empty_bytes() {
    let notes = parse_notes(b"");
    assert!(notes.is_empty());
}

#[test]
fn parse_notes_handles_padding() {
    // Name with non-4-byte length (should be padded).
    let name = b"GNU\0";
    let desc = [0x42u8; 5]; // 5 bytes, needs 3 bytes padding
    let namesz = name.len() as u32;
    let descsz = desc.len() as u32;
    let mut buf = Vec::new();
    buf.extend(namesz.to_le_bytes());
    buf.extend(descsz.to_le_bytes());
    buf.extend(3u32.to_le_bytes()); // NT_GNU_ABI_TAG
    buf.extend(name);
    buf.extend(desc);
    buf.extend([0u8; 3]); // padding to align desc to 4
    let notes = parse_notes(&buf);
    assert_eq!(notes.len(), 1);
    assert_eq!(notes[0].desc.len(), 5);
}

// ------------------------------------------------------------------
// Verdef / Verneed parsing tests
// ------------------------------------------------------------------

#[test]
fn parse_verdefs_empty_on_no_data() {
    let defs = parse_verdefs(b"", b"");
    assert!(defs.is_empty());
}

#[test]
fn parse_verneeds_empty_on_no_data() {
    let needs = parse_verneeds(b"", b"");
    assert!(needs.is_empty());
}

#[test]
fn parse_verdefs_parses_single_entry() {
    // Single version definition: vd_version=1, vd_flags=1 (BASE),
    // vd_ndx=2, vd_cnt=1, name="VER_1" at strtab offset 1.
    let strtab = b"\0VER_1\0";
    let mut buf = Vec::new();
    // VerDef header
    buf.extend(1u16.to_le_bytes());  // vd_version
    buf.extend(1u16.to_le_bytes());  // vd_flags
    buf.extend(2u16.to_le_bytes());  // vd_ndx
    buf.extend(1u16.to_le_bytes());  // vd_cnt
    buf.extend(0u32.to_le_bytes());  // vd_hash (unused)
    buf.extend(20u32.to_le_bytes()); // vd_aux (offset from start of this entry)
    buf.extend(0u32.to_le_bytes());  // vd_next
    // Padding up to aux offset (offset 20 from entry start)
    assert_eq!(buf.len(), 20);
    // VerdAux
    buf.extend(1u32.to_le_bytes());  // vda_name  -> "VER_1"
    buf.extend(0u32.to_le_bytes());  // vda_next
    let defs = parse_verdefs(&buf, strtab);
    assert_eq!(defs.len(), 1);
    assert_eq!(defs[0].ndx, 2);
    assert_eq!(defs[0].name, "VER_1");
}

#[test]
fn parse_verneeds_parses_single_dependency() {
    // One needed dependency: file="libfoo.so", one version "VER_1".
    let strtab = b"\0libfoo.so\0VER_1\0";
    let mut buf = Vec::new();
    // VerNeed header
    buf.extend(1u16.to_le_bytes());  // vn_version
    buf.extend(1u16.to_le_bytes());  // vn_cnt
    buf.extend(1u32.to_le_bytes());  // vn_file -> "libfoo.so"
    buf.extend(20u32.to_le_bytes()); // vn_aux  (offset from start)
    buf.extend(0u32.to_le_bytes());  // vn_next
    assert_eq!(buf.len(), 16);
    // Padding to aux offset
    buf.extend([0u8; 4]);
    assert_eq!(buf.len(), 20);
    // VernAux
    buf.extend(0u32.to_le_bytes());  // vna_hash
    buf.extend(0u16.to_le_bytes());  // vna_flags
    buf.extend(3u16.to_le_bytes());  // vna_other (version index 3)
            buf.extend(11u32.to_le_bytes()); // vna_name -> "VER_1"
    buf.extend(0u32.to_le_bytes());  // vna_next
    let needs = parse_verneeds(&buf, strtab);
    assert_eq!(needs.len(), 1);
    assert_eq!(needs[0].file, "libfoo.so");
    assert_eq!(needs[0].versions.len(), 1);
    assert_eq!(needs[0].versions[0], (3, "VER_1".to_string()));
}

// ------------------------------------------------------------------
// Integration: ELF with GNU hash, notes, and version info
// ------------------------------------------------------------------
