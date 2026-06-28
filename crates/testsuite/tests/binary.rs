//! End-to-end binary pipeline: ELF bytes → `csolver-elf` (load + recover a
//! function's machine code) → `csolver-asm` (decode x86-64 → MSIR) →
//! `csolver-verifier`. This verifies a *compiled binary* with no source.
#![allow(clippy::expect_used, clippy::unwrap_used)]

use csolver_core::Verdict;
use csolver_verifier::{verify_module, Config};

/// Wrap raw `.text` machine code into a minimal valid ELF64 with one function
/// symbol `myfunc` of `code.len()` bytes at virtual address 0x1000.
fn elf_with_code(code: &[u8]) -> Vec<u8> {
    const HDR: usize = 64;
    const SH: usize = 64;
    const SYM: u64 = 24;
    let shstr: &[u8] = b"\0.text\0.shstrtab\0.symtab\0.strtab\0";
    let strtab: &[u8] = b"\0myfunc\0";

    let text_off = HDR as u64;
    let shstr_off = text_off + code.len() as u64;
    let strtab_off = shstr_off + shstr.len() as u64;
    let symtab_off = strtab_off + strtab.len() as u64;
    let symtab_size = 2 * SYM;
    let shoff = symtab_off + symtab_size;

    let mut o = vec![0u8; (shoff + 5 * SH as u64) as usize];
    let pu16 = |o: &mut [u8], at: usize, v: u16| o[at..at + 2].copy_from_slice(&v.to_le_bytes());
    let pu32 = |o: &mut [u8], at: usize, v: u32| o[at..at + 4].copy_from_slice(&v.to_le_bytes());
    let pu64 = |o: &mut [u8], at: usize, v: u64| o[at..at + 8].copy_from_slice(&v.to_le_bytes());

    o[0..4].copy_from_slice(b"\x7fELF");
    o[4] = 2; // ELF64
    o[5] = 1; // little-endian
    o[6] = 1;
    pu16(&mut o, 16, 2); // ET_EXEC
    pu16(&mut o, 18, 62); // x86-64
    pu32(&mut o, 20, 1);
    pu64(&mut o, 24, 0x1000); // entry
    pu64(&mut o, 40, shoff); // e_shoff
    pu16(&mut o, 52, HDR as u16);
    pu16(&mut o, 58, SH as u16);
    pu16(&mut o, 60, 5); // e_shnum
    pu16(&mut o, 62, 2); // e_shstrndx

    o[text_off as usize..text_off as usize + code.len()].copy_from_slice(code);
    o[shstr_off as usize..shstr_off as usize + shstr.len()].copy_from_slice(shstr);
    o[strtab_off as usize..strtab_off as usize + strtab.len()].copy_from_slice(strtab);

    let s1 = symtab_off as usize + SYM as usize;
    pu32(&mut o, s1, 1); // st_name -> "myfunc"
    o[s1 + 4] = (1 << 4) | 2; // GLOBAL | STT_FUNC
    pu16(&mut o, s1 + 6, 1); // .text
    pu64(&mut o, s1 + 8, 0x1000);
    pu64(&mut o, s1 + 16, code.len() as u64);

    let mut sh = |idx: usize, fields: &[(usize, u64, u8)]| {
        let base = shoff as usize + idx * SH;
        for &(off, val, w) in fields {
            if w == 4 {
                pu32(&mut o, base + off, val as u32);
            } else {
                pu64(&mut o, base + off, val);
            }
        }
    };
    sh(1, &[(0, 1, 4), (4, 1, 4), (8, 0x6, 8), (16, 0x1000, 8), (24, text_off, 8), (32, code.len() as u64, 8), (48, 16, 8)]);
    sh(2, &[(0, 7, 4), (4, 3, 4), (24, shstr_off, 8), (32, shstr.len() as u64, 8)]);
    sh(3, &[(0, 17, 4), (4, 2, 4), (24, symtab_off, 8), (32, symtab_size, 8), (40, 4, 4), (44, 1, 4), (56, SYM, 8)]);
    sh(4, &[(0, 25, 4), (4, 3, 4), (24, strtab_off, 8), (32, strtab.len() as u64, 8)]);
    o
}

/// Run the whole binary pipeline on raw `.text` bytes and return the verdict.
fn verify_binary(code: &[u8]) -> Verdict {
    let image = elf_with_code(code);
    let img = csolver_elf::load(&image).expect("valid ELF");
    let func = img.functions().next().expect("one function symbol");
    let bytes = img.function_code(func, &image).expect("function code");
    let module = csolver_asm::decode_function(&func.name, bytes);
    verify_module(&module, &Config::default()).verdict
}

#[test]
fn verifies_a_memory_safe_compiled_function() {
    // `xor eax, eax ; ret` — returns 0, touches no memory, so it is trivially
    // memory-safe. The full ELF → decode → MSIR → verify pipeline reports PASS.
    assert_eq!(verify_binary(&[0x31, 0xc0, 0xc3]), Verdict::Pass);
}

#[test]
fn raw_pointer_store_in_a_binary_is_unknown_not_pass() {
    // `mov [rdi], rsi ; ret` — a store through a raw register. Nothing in the
    // binary establishes that `rdi` points to valid, writable memory, so the
    // store cannot be proved safe: UNKNOWN (never a false PASS).
    assert_eq!(verify_binary(&[0x48, 0x89, 0x37, 0xc3]), Verdict::Unknown);
}

#[test]
fn an_undecodable_function_is_unknown() {
    // A syscall (`0f 05`) is outside the decoded subset, so the function is
    // `unanalyzed` and reported UNKNOWN — never silently treated as safe.
    assert_eq!(verify_binary(&[0x0f, 0x05]), Verdict::Unknown);
}
