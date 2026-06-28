# Verification — csolver-elf

## Design
A from-scratch, **pure-Rust** ELF64 reader (no `object`/`gimli`, in keeping with
the project's zero-dependency stance). It parses the ELF header, the section
table (with `.shstrtab` names), and the first symbol table (with its linked
string table), producing an [`Image`] of sections (name, vaddr, size, file
offset, R/W/X permissions) and symbols (name, address, size, is-function).
`Image::function_code` slices a function's machine bytes out of the image — the
hand-off point to the assembly decoder. This is the first layer of "verify a
compiled binary with no source".

## Specification
- ELF64, little-endian only (x86-64 / AArch64); other classes/endianness are a
  clean `Unsupported`, never a mis-parse.
- Section permissions are read from `sh_flags` (`SHF_WRITE`, `SHF_EXECINSTR`);
  `NOBITS` (`.bss`) is flagged as having no file data.
- A function symbol is `STT_FUNC` with a non-zero size; its code is
  `file_offset + (sym.addr − sec.addr) .. + sym.size` within the section that
  contains its address.

## Soundness / robustness
- **Bounds-checked throughout.** Every multi-byte read and every section/symbol
  slice is range-checked against the file length; a truncated or malformed image
  yields `Error::parse`/`Error::unsupported`, never a panic or an out-of-bounds
  read. The loader is the trust boundary between an untrusted file and the
  analysis, so it must not be the thing that crashes.

## Limits (this increment)
- No program headers/segments, relocations, dynamic symbols, DWARF, or PLT/GOT
  yet — so stripped binaries expose fewer symbols and (later) lose typed/frame
  precision. PE / Mach-O are future.
- Only the first `SYMTAB` is read (static symbol table); `.dynsym` is not merged.

## Test strategy
A hand-built minimal ELF64 (one `.text`, one function symbol) is parsed
end-to-end: sections, permissions, the function symbol, and its exact code bytes
are checked; malformed inputs (bad magic, truncation, ELF32) are rejected; and
address→section lookup is verified. Next: a corpus of real `rustc`-compiled ELF
objects cross-checked against `llvm-readobj`, then the x86-64 decoder that turns
`function_code` bytes into MSIR.
