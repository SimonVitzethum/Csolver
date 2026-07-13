use super::*;

/// Build a minimal thin 64-bit Mach-O with one `__TEXT,__text` section holding `code`
/// and one function symbol `name` at the section's address. Little-endian.
fn synth_macho(cputype: u32, name: &str, code: &[u8]) -> Vec<u8> {
    // Layout: [header 32][LC_SEGMENT_64 (72 + 80)][LC_SYMTAB 24][code][symtab][strtab]
    let seg_cmd_size = 72 + 80;
    let symtab_cmd_size = 24;
    let sizeofcmds = seg_cmd_size + symtab_cmd_size;
    let text_off = 32 + sizeofcmds;
    let symoff = text_off + code.len();
    let nsyms = 1usize;
    let stroff = symoff + nsyms * 16;
    // string table: index 0 is a NUL, name at index 1.
    let mut strtab = vec![0u8];
    strtab.extend_from_slice(format!("_{name}").as_bytes());
    strtab.push(0);
    let vmaddr = 0x1000u64;

    let mut b = Vec::new();
    // mach_header_64.
    b.extend_from_slice(&0xfeed_facfu32.to_le_bytes()); // magic
    b.extend_from_slice(&cputype.to_le_bytes());
    b.extend_from_slice(&0u32.to_le_bytes()); // cpusubtype
    b.extend_from_slice(&1u32.to_le_bytes()); // filetype MH_OBJECT
    b.extend_from_slice(&2u32.to_le_bytes()); // ncmds
    b.extend_from_slice(&(sizeofcmds as u32).to_le_bytes());
    b.extend_from_slice(&0u32.to_le_bytes()); // flags
    b.extend_from_slice(&0u32.to_le_bytes()); // reserved
    // LC_SEGMENT_64.
    b.extend_from_slice(&0x19u32.to_le_bytes()); // cmd
    b.extend_from_slice(&(seg_cmd_size as u32).to_le_bytes()); // cmdsize
    b.extend_from_slice(&pad16(b"__TEXT")); // segname[16]
    b.extend_from_slice(&vmaddr.to_le_bytes()); // vmaddr
    b.extend_from_slice(&(code.len() as u64).to_le_bytes()); // vmsize
    b.extend_from_slice(&(text_off as u64).to_le_bytes()); // fileoff
    b.extend_from_slice(&(code.len() as u64).to_le_bytes()); // filesize
    b.extend_from_slice(&7i32.to_le_bytes()); // maxprot rwx
    b.extend_from_slice(&5i32.to_le_bytes()); // initprot r-x
    b.extend_from_slice(&1u32.to_le_bytes()); // nsects
    b.extend_from_slice(&0u32.to_le_bytes()); // flags
    // section_64.
    b.extend_from_slice(&pad16(b"__text")); // sectname[16]
    b.extend_from_slice(&pad16(b"__TEXT")); // segname[16]
    b.extend_from_slice(&vmaddr.to_le_bytes()); // addr
    b.extend_from_slice(&(code.len() as u64).to_le_bytes()); // size
    b.extend_from_slice(&(text_off as u32).to_le_bytes()); // offset
    b.extend_from_slice(&0u32.to_le_bytes()); // align
    b.extend_from_slice(&0u32.to_le_bytes()); // reloff
    b.extend_from_slice(&0u32.to_le_bytes()); // nreloc
    b.extend_from_slice(&0x0000_0400u32.to_le_bytes()); // flags S_ATTR_PURE_INSTRUCTIONS
    b.extend_from_slice(&0u32.to_le_bytes()); // reserved1
    b.extend_from_slice(&0u32.to_le_bytes()); // reserved2
    b.extend_from_slice(&0u32.to_le_bytes()); // reserved3
    // LC_SYMTAB.
    b.extend_from_slice(&0x2u32.to_le_bytes()); // cmd
    b.extend_from_slice(&24u32.to_le_bytes()); // cmdsize
    b.extend_from_slice(&(symoff as u32).to_le_bytes());
    b.extend_from_slice(&(nsyms as u32).to_le_bytes());
    b.extend_from_slice(&(stroff as u32).to_le_bytes());
    b.extend_from_slice(&(strtab.len() as u32).to_le_bytes());
    // code.
    b.extend_from_slice(code);
    // nlist_64: one function symbol at section 1, value = vmaddr.
    b.extend_from_slice(&1u32.to_le_bytes()); // n_strx = 1 (skip the leading NUL)
    b.push(0x0e); // n_type = N_SECT
    b.push(1); // n_sect = 1
    b.extend_from_slice(&0u16.to_le_bytes()); // n_desc
    b.extend_from_slice(&vmaddr.to_le_bytes()); // n_value
    // string table.
    b.extend_from_slice(&strtab);
    b
}

fn pad16(s: &[u8]) -> [u8; 16] {
    let mut a = [0u8; 16];
    a[..s.len().min(16)].copy_from_slice(&s[..s.len().min(16)]);
    a
}

#[test]
fn is_macho_detects_magics() {
    assert!(macho::is_macho(&0xfeed_facfu32.to_le_bytes()));
    assert!(macho::is_macho(&0xcafe_babeu32.to_be_bytes()));
    assert!(!macho::is_macho(b"\x7fELF"));
}

#[test]
fn parses_a_thin_macho_function() {
    let img_bytes = synth_macho(0x0100_0007, "myfunc", &[0xc3]); // x86_64, `ret`
    let img = macho::load(&img_bytes).expect("Mach-O loads");
    assert_eq!(img.machine, EM_X86_64);
    let f = img.functions().next().expect("one function");
    assert_eq!(f.name, "myfunc", "the leading underscore is stripped");
    let code = img.function_code(f, &img_bytes).expect("code sliced");
    assert_eq!(code, &[0xc3]);
}

#[test]
fn arm64_cputype_maps() {
    let img_bytes = synth_macho(0x0100_000c, "f", &[0xc0, 0x03, 0x5f, 0xd6]);
    let img = macho::load(&img_bytes).expect("Mach-O loads");
    assert_eq!(img.machine, EM_AARCH64);
}

#[test]
fn rejects_unknown_cputype() {
    let img_bytes = synth_macho(0x0000_0007, "f", &[0xc3]); // CPU_TYPE_X86 (32-bit)
    assert!(macho::load(&img_bytes).is_err());
}

#[test]
fn rejects_non_macho() {
    assert!(macho::load(b"\x7fELF____").is_err());
    assert!(macho::load(b"MZ").is_err());
}
