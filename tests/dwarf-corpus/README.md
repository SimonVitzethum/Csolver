# Cross-language DWARF recovery corpus

Real inputs (C, C++, D, Zig, Swift; more to follow) compiled to `-g` LLVM IR,
validating that CSolver recovers opaque-pointer pointee types from DWARF `!DI…`
metadata — the lever making it usable for any LLVM frontend, not just Rust.

Regenerate the `.ll`:

    clang   -O1 -g -emit-llvm -S c_structs.c      -o c_structs.ll
    clang++ -O1 -g -emit-llvm -S cpp_refs.cpp     -o cpp_refs.ll
    clang++ -O1 -g -emit-llvm -S cpp_refmember.cpp -o cpp_refmember.ll
    ldc2 -g -output-ll -c d_types.d               -of=d_types.ll
    zig build-obj -femit-llvm-ir=z.ll -fno-emit-bin z*.zig   # emits DW_LANG_C99
    swiftc -g -emit-ir swift_types.swift          -o swift_types.ll

## The recovery is language-aware (sound per language)

The pointee *size* alone never makes a pointer valid; validity is the *language's*
guarantee, read from `DICompileUnit(language: DW_LANG_…)`:

| Language | Valid reference (recovered) | Raw pointer (NOT recovered — may dangle) |
|---|---|---|
| Rust  | `&T`/`&mut T` (`DW_TAG_pointer_type` named `&…`) | `*const T`/`*mut T` |
| C++   | `T&` (`DW_TAG_reference_type`)                   | `T*` |
| C     | — (none)                                          | `T*` |
| D     | `ref` (`DW_TAG_reference_type`)                   | `T*`, `class` refs (nullable) |
| Zig   | — (emits `DW_LANG_C99`, indistinguishable from C) | `*const T` |
| Swift | `inout T` (LLVM `dereferenceable(N)` attribute)   | `class` refs (plain `ptr`, non-null by ABI but no IR evidence) |

So `sum_ref(Point&)` (C++) verifies PASS; `sum_pair(Pair*)` (C/D/Zig) is soundly
UNKNOWN — never a false PASS. A `DW_TAG_reference_type` is a valid reference in
every language that emits it, so it is recovered regardless of the language tag;
the Rust `&…` naming rule is gated to `DW_LANG_Rust`.

Swift lowers every aggregate to a **packed struct** (`<{ … }>`, no inter-field
padding); CSolver models packed layout exactly (`Type::Struct { packed: true }`),
so a Swift `Pair` is sized and offset correctly — never oversized. Swift `inout`
carries a `dereferenceable(N)` attribute rather than a DWARF reference, so it is
recovered through the attribute path: `sum_inout(inout Pair)` proves every access
except the alignment obligation (swiftc omits the pointer `align` attribute — the
same residual as C++ `cpp_refmember`). A Swift `class` argument is a non-null
reference by ABI but the IR shows only a plain `ptr`, so it stays soundly UNKNOWN.

Verify: `solver verify <file>.ll`.
