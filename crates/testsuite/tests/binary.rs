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
fn in_frame_stack_store_in_a_binary_is_proven_safe() {
    // sub rsp,16 ; mov [rsp+8], eax ; add rsp,16 ; ret  — a store at offset 8
    // into a 16-byte stack frame. The frame model proves it in bounds: PASS.
    let code = [0x48, 0x83, 0xec, 0x10, 0x89, 0x44, 0x24, 0x08, 0x48, 0x83, 0xc4, 0x10, 0xc3];
    assert_eq!(verify_binary(&code), Verdict::Pass);
}

#[test]
fn out_of_frame_stack_store_in_a_binary_fails() {
    // sub rsp,16 ; mov [rsp+32], eax ; add rsp,16 ; ret  — offset 32 is past the
    // 16-byte frame: a definite out-of-bounds write. FAIL.
    let code = [0x48, 0x83, 0xec, 0x10, 0x89, 0x44, 0x24, 0x20, 0x48, 0x83, 0xc4, 0x10, 0xc3];
    assert_eq!(verify_binary(&code), Verdict::Fail);
}

#[test]
fn guarded_stack_store_in_a_branchy_binary_is_proven_safe() {
    //   sub rsp, 16
    //   cmp edi, 0
    //   jne .skip          ; conditionally skip the store
    //   mov [rsp+8], eax   ; store, always within the 16-byte frame
    // .skip:
    //   add rsp, 16 ; ret
    // The decoder reconstructs the CFG (a conditional branch + a join), and the
    // state-merging engine verifies the guarded store PASS.
    let code = [
        0x48, 0x83, 0xec, 0x10, // sub rsp, 16
        0x83, 0xff, 0x00, // cmp edi, 0
        0x75, 0x04, // jne +4 (.skip)
        0x89, 0x44, 0x24, 0x08, // mov [rsp+8], eax
        0x48, 0x83, 0xc4, 0x10, // add rsp, 16
        0xc3, // ret
    ];
    assert_eq!(verify_binary(&code), Verdict::Pass);
}

#[test]
fn a_binary_loop_is_handled() {
    //   xor eax, eax
    // .loop:
    //   add eax, 1 ; cmp eax, 4 ; jne .loop
    //   ret
    // A backward branch (loop). The decoder reconstructs the back-edge and the
    // symbolic engine handles it (cut + interval invariant); no memory is
    // touched, so it verifies PASS.
    let code = [
        0x31, 0xc0, // xor eax, eax
        0x83, 0xc0, 0x01, // add eax, 1   (.loop)
        0x83, 0xf8, 0x04, // cmp eax, 4
        0x75, 0xf8, // jne -8 (.loop)
        0xc3, // ret
    ];
    assert_eq!(verify_binary(&code), Verdict::Pass);
}

#[test]
fn guarded_array_store_in_a_binary_is_proven_safe() {
    //   sub rsp, 64            ; a 16-element i32 stack array
    //   cmp ecx, 16
    //   jae .end               ; bounds check: skip if ecx >= 16
    //   mov [rsp + rcx*4], eax  ; arr[rcx] = eax   (indexed addressing)
    // .end:
    //   add rsp, 64 ; ret
    // The guard `rcx < 16` bounds the indexed access to the 64-byte frame: PASS.
    let code = [
        0x48, 0x83, 0xec, 0x40, // sub rsp, 64
        0x83, 0xf9, 0x10, // cmp ecx, 16
        0x73, 0x03, // jae +3 (.end)
        0x89, 0x04, 0x8c, // mov [rsp + rcx*4], eax
        0x48, 0x83, 0xc4, 0x40, // add rsp, 64
        0xc3, // ret
    ];
    assert_eq!(verify_binary(&code), Verdict::Pass);
}

#[test]
fn unguarded_array_store_in_a_binary_fails() {
    //   sub rsp, 64 ; mov [rsp + rcx*4], eax ; add rsp, 64 ; ret
    // No bound on `rcx`, so `rcx = 16` writes one element past the 16-element
    // frame: a definite out-of-bounds write. FAIL.
    let code = [
        0x48, 0x83, 0xec, 0x40, // sub rsp, 64
        0x89, 0x04, 0x8c, // mov [rsp + rcx*4], eax
        0x48, 0x83, 0xc4, 0x40, // add rsp, 64
        0xc3, // ret
    ];
    assert_eq!(verify_binary(&code), Verdict::Fail);
}

/// As [`verify_binary`], but decoding the recovered code as AArch64.
fn verify_arm_binary(code: &[u8]) -> Verdict {
    let image = elf_with_code(code);
    let img = csolver_elf::load(&image).expect("valid ELF");
    let func = img.functions().next().expect("one function symbol");
    let bytes = img.function_code(func, &image).expect("function code");
    let module = csolver_asm::arm64::decode_function(&func.name, bytes);
    verify_module(&module, &Config::default()).verdict
}

#[test]
fn in_frame_arm_stack_store_is_proven_safe() {
    // AArch64: sub sp,sp,#16 ; str w0,[sp,#8] ; add sp,sp,#16 ; ret
    // A store at offset 8 into a 16-byte stack frame: PASS.
    let code = [
        0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16
        0xe0, 0x0b, 0x00, 0xb9, // str w0, [sp, #8]
        0xff, 0x43, 0x00, 0x91, // add sp, sp, #16
        0xc0, 0x03, 0x5f, 0xd6, // ret
    ];
    assert_eq!(verify_arm_binary(&code), Verdict::Pass);
}

#[test]
fn out_of_frame_arm_stack_store_fails() {
    // AArch64: str w0,[sp,#32] is past the 16-byte frame — a definite OOB write.
    let code = [
        0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16
        0xe0, 0x23, 0x00, 0xb9, // str w0, [sp, #32]
        0xff, 0x43, 0x00, 0x91, // add sp, sp, #16
        0xc0, 0x03, 0x5f, 0xd6, // ret
    ];
    assert_eq!(verify_arm_binary(&code), Verdict::Fail);
}

#[test]
fn guarded_arm_stack_store_in_a_branchy_binary_is_proven_safe() {
    //   sub sp, sp, #16
    //   cmp w0, #0
    //   b.ne .skip          ; conditionally skip the store
    //   str w1, [sp, #8]    ; store, within the 16-byte frame
    // .skip:
    //   add sp, sp, #16 ; ret
    // The AArch64 decoder reconstructs the CFG (cmp + b.cond) and the store
    // verifies PASS.
    let code = [
        0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16
        0x1f, 0x00, 0x00, 0x71, // cmp w0, #0
        0x41, 0x00, 0x00, 0x54, // b.ne +8 (.skip)
        0xe1, 0x0b, 0x00, 0xb9, // str w1, [sp, #8]
        0xff, 0x43, 0x00, 0x91, // add sp, sp, #16
        0xc0, 0x03, 0x5f, 0xd6, // ret
    ];
    assert_eq!(verify_arm_binary(&code), Verdict::Pass);
}

#[test]
fn an_undecodable_function_is_unknown() {
    // A syscall (`0f 05`) is outside the decoded subset, so the function is
    // `unanalyzed` and reported UNKNOWN — never silently treated as safe.
    assert_eq!(verify_binary(&[0x0f, 0x05]), Verdict::Unknown);
}
