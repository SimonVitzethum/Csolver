# Cross-language DWARF recovery corpus

Real C/C++ (later Swift, other LLVM frontends) inputs validating that CSolver
recovers opaque-pointer pointee types from DWARF `!DI…` metadata — the mechanism
that makes it usable beyond Rust.

Regenerate the `.ll` with debug info (any LLVM version):

    clang   -O1 -g -emit-llvm -S c_structs.c        -o c_structs.ll
    clang++ -O1 -g -emit-llvm -S cpp_refs.cpp        -o cpp_refs.ll
    clang++ -O1 -g -emit-llvm -S cpp_refmember.cpp   -o cpp_refmember.ll

Then `solver verify <file>.ll`.

## Expected, and why (soundness is language-specific)

- **C++ references** (`T&`, `DW_TAG_reference_type`): recovered as valid regions
  — `sum_ref(Point&)` verifies PASS. This is the type-system guarantee.
- **C raw pointers** (`T*`, `DW_TAG_pointer_type`, unnamed): NOT recovered —
  a C pointer may dangle, so `sum_pair(Pair*)` is soundly UNKNOWN (never a false
  PASS). This is correct C semantics, not a tool gap.
- **C++ reference struct members** (`Cell& cell`): the loaded field pointer is
  recovered as a valid reference; size/bounds/liveness/read prove. The alignment
  obligation stays UNKNOWN when clang omits `align:` on the pointee composite
  (a sound limitation — alignment cannot be assumed without the info).
- **C/C++ raw-pointer members** (`Point* inner`): not recovered (raw pointer).
