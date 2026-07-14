# Verification — csolver-elf

## Design
A from-scratch, **pure-Rust** object- and container-file reader (no `object`/
`gimli`, in keeping with the project's zero-dependency stance). One format-agnostic
entry point, `load_object(bytes)`, sniffs the leading magic and dispatches to the
ELF, PE/COFF, or Mach-O parser, producing a common `Image`: sections (name, vaddr,
size, file offset, R/W/X permissions), symbols (name, address, size, is-function),
program headers, relocations, and — for ELF — dynamic info and DWARF.
`Image::function_code` slices a function's machine bytes out of the image — the
hand-off point to the assembly decoder. This is the first layer of "verify a
compiled binary with no source": a Linux `.o`, a Windows `.dll`, a macOS Mach-O all
run the SAME decode + verify pipeline; only the front matter differs per OS.

## Specification
- **Object formats:** ELF (Linux/bare-metal), PE/COFF (Windows `.exe`/`.dll`/
  `.sys`/`.obj`), Mach-O (macOS/iOS, thin or the x86-64/arm64 slice of a fat binary).
- **ELF classes/endianness:** ELF64-LE is the fast path (also parses DWARF, GNU/SysV
  hash, version info, dynamic, notes); **ELF32 and big-endian** are handled by a
  class/endian-generic reader (`load_generic`) that produces the core `Image` fields.
- **Architectures decoded:** x86-64 (`e_machine` 62) and AArch64 (183); other machines
  parse but are a clean `Unsupported` at the decode stage.
- **Relocations:** ELF `SHT_RELA`/`SHT_REL` (x86-64/AArch64) drive per-symbol
  RIP-relative global resolution; a linked PE/Mach-O carries none, so `[rip+disp]` is
  resolved self-relatively to the containing section (looser but sound).
- **DWARF:** a focused `.debug_info` reader recovers pointer-parameter pointee sizes
  (cross-language, see `tests/dwarf-corpus`); a `.debug_line` reader maps an instruction
  address to a source line (`line_rows`/`line_at`). `.debug_frame`/CFI and variable types
  are deferred as marginal (the prologue heuristic derives the frame; symbols size globals).
- **Container formats (a filesystem/archive, not an object):**
  - **ISO 9660** (`iso`): the volume descriptors and directory tree → each regular file
    as `(path, offset, size)`; Joliet (UTF-16BE) preferred, **Rock Ridge** (SUSP `NM`)
    POSIX long names recovered, **El Torito** boot images enumerated (a boot loader's PE).
  - **UDF** (`udf`, ISO 13346 / ECMA-167): the filesystem every Windows install ISO and modern
    large hybrid uses (the ISO 9660 side is a compatibility stub). Anchor VD Pointer → Volume
    Descriptor Sequence (partition + logical volume) → File Set Descriptor → root File Entry →
    directory walk (File Identifier Descriptors). Verified on a real Win11 25H2 ISO: 1064 files,
    hundreds of PE objects found (`bootx64.efi`, `setup.exe`, `sources/*.dll`) plus `install.wim`.
  - **WIM** (`wim`, `install.wim`/`boot.wim`): header, RESHDR resource headers, the lookup
    table; `data_resources()`+`extract()` decompress each file resource. **XPRESS-Huffman**
    (MS-XCA §2.1) **and LZX** ([`crate::lzx`], the `install.wim` default) are implemented — the
    LZX decoder is **byte-exact**, cross-checked against 1475 real `boot.wim` resources by their
    stored SHA-1. A raw chunk is copied. **LZMS** returns a clean `Unsupported`. Decompression is
    size-checked, so a decoder mistake is a clean failure, never garbage.
- **Stripped binaries:** with no symbol table, x86-64 function starts are discovered
  heuristically (`endbr64`, `push rbp; mov rbp,rsp`); a spurious start only yields an
  UNKNOWN function, never a false PASS of another.

## Soundness / robustness
- **Bounds-checked throughout.** Every multi-byte read and every section/symbol/resource
  slice is range-checked against the file length; a truncated or malformed image yields
  `Error::parse`/`Error::unsupported`, never a panic or an out-of-bounds read. The loader
  is the trust boundary between an untrusted file and the analysis, so it must not be the
  thing that crashes.
- **WIM decompression is size-checked:** a chunk that does not decode to its expected length
  is an error, so a decoder mistake is a clean failure, never garbage bytes.

## Limits
- WIM LZMS is not decoded (rare; used for `/compress:recovery` solid resources). PE
  base-relocation and Mach-O relocation application are not performed (so RIP-relative globals
  resolve only for ELF's per-symbol relocations); PDB (a separate `.pdb` file, referenced by GUID
  from the PE) and CFI are future.

## Test strategy
Hand-built minimal images (ELF64/ELF32 LE+BE, ISO with a file, El Torito catalog, an NM
Rock Ridge entry, a minimal WIM with an uncompressed resource, an XPRESS round-trip via a
reference bit-encoder) are parsed end-to-end and cross-checked; malformed inputs are
rejected without a panic. Real toolchain output is validated too: clang-cross-compiled
Windows COFF/PE and macOS Mach-O objects, and zig-emitted ELF. `Image::function_code`
resolves a symbol by `section_index` (not address — ambiguous in a relocatable `.o`).
