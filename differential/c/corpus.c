// C differential-validation corpus.
//
// Each `f_*` here is verified **statically** by CSolver (on its `clang -O0 -g
// -emit-llvm` output) and exercised **dynamically** by ASan+UBSan (via the sibling
// driver in `drive.c`). The harness (`run.sh`) compares the two:
//
//   sanitizer UB on some driven input  =>  CSolver must **never** say PASS
//                                          (a PASS here is an unsound false positive)
//   sanitizer clean                    =>  CSolver should ideally PASS
//                                          (UNKNOWN is an acceptable precision miss)
//
// The C soundness oracle is AddressSanitizer (spatial: heap/stack overflow; temporal:
// use-after-free, double-free) plus UndefinedBehaviorSanitizer (array-index bounds,
// signed overflow, misaligned access, null deref). It is the C analogue of Miri.
//
// The functions are **self-contained**: each takes a fuzzable scalar and owns its
// buffer (a fixed local array or a constant-size `malloc`), so CSolver reasons about
// it with no caller — mirroring how the Rust corpus is self-contained via slice types.
// The driver fuzzes the scalar across a range that includes the UB-triggering values.
//
// A function is safe iff it is memory-safe for EVERY input the driver can pass.

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// ===== safe: memory-safe for every input. CSolver should ideally PASS. ========

// A guarded index into a fixed local array — safe for every `i`.
int64_t f_checked_get(int64_t i) {
    int64_t a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
    if (i >= 0 && i < 8) {
        return a[i];
    }
    return -1;
}

// A constant index — statically in bounds.
int64_t f_const_index(void) {
    int64_t a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
    return a[3];
}

// A guarded fill loop over a fixed buffer — every write is in bounds.
int64_t f_fill_loop(int64_t n) {
    int64_t a[16];
    int64_t m = n;
    if (m < 0) m = 0;
    if (m > 16) m = 16;
    for (int64_t i = 0; i < m; i++) {
        a[i] = i;
    }
    return m > 0 ? a[0] : -1;
}

// A heap buffer, guarded index, then freed — safe (no overflow, no use-after-free).
int64_t f_heap_guarded(int64_t i) {
    int64_t *p = malloc(8 * sizeof(int64_t));
    if (!p) return 0;
    for (int64_t k = 0; k < 8; k++) p[k] = k;
    int64_t v = (i >= 0 && i < 8) ? p[i] : -1;
    free(p);
    return v;
}

// memcpy within a fixed destination — the guarded length keeps it in bounds.
int64_t f_memcpy_bounded(int64_t n) {
    uint8_t dst[32] = {0};
    uint8_t src[32];
    for (int i = 0; i < 32; i++) src[i] = (uint8_t) i;
    int64_t m = n;
    if (m < 0) m = 0;
    if (m > 32) m = 32;
    memcpy(dst, src, (size_t) m);
    return dst[0];
}

// The last-element idiom over a fixed array — `len - 1` is in bounds when non-empty.
int64_t f_last(int64_t len) {
    int64_t a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
    int64_t l = len;
    if (l < 0) l = 0;
    if (l > 8) l = 8;
    if (l == 0) return -1;
    return a[l - 1];
}

// A harness-scoping control: signed-integer overflow is UB, but it is *arithmetic*
// UB, not a memory-safety violation — CSolver proves memory safety, not overflow-
// freedom, so it PASSes (no memory obligation). The sanitizer oracle is deliberately
// scoped to memory UB (ASan + UBSan bounds/alignment/null/pointer), which does NOT
// flag this — so it is classified "precise", never a false violation. If the oracle
// were mis-scoped to include `signed-integer-overflow`, this row would expose it.
int64_t f_signed_ovf(int64_t i) {
    int64_t x = INT64_MAX - (i & 1);
    return x + 2; // overflows for i even — arithmetic UB, memory-safe
}

// ===== unsafe: UB on a reachable input. CSolver must NOT say PASS. ============

// An unchecked index into a fixed array — OOB when `i < 0` or `i >= 8`.
int64_t f_unchecked_get(int64_t i) {
    int64_t a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
    return a[i];
}

// An inclusive-bound loop — writes `a[16]`, one past the end, on the last iteration.
int64_t f_off_by_one(void) {
    int64_t a[16];
    int64_t last = 0;
    for (int64_t i = 0; i <= 16; i++) {
        a[i] = i;
        last = a[i];
    }
    return last;
}

// A heap read past the allocation — OOB when `i >= 8`.
int64_t f_heap_oob(int64_t i) {
    int64_t *p = malloc(8 * sizeof(int64_t));
    if (!p) return 0;
    for (int64_t k = 0; k < 8; k++) p[k] = k;
    int64_t v = p[i];
    free(p);
    return v;
}

// A read after free — temporal violation for every input.
int64_t f_use_after_free(int64_t i) {
    int64_t *p = malloc(8 * sizeof(int64_t));
    if (!p) return 0;
    for (int64_t k = 0; k < 8; k++) p[k] = k;
    free(p);
    return p[i & 7];
}

// A double free — temporal violation for every input.
int64_t f_double_free(int64_t i) {
    int64_t *p = malloc(8 * sizeof(int64_t));
    if (!p) return 0;
    p[0] = i;
    free(p);
    free(p);
    return 0;
}

// An unchecked index with an intervening inline asm (a memory barrier). The asm
// must not drop the function from analysis — the OOB past it is still a bug.
int64_t f_asm_then_oob(int64_t i) {
    int64_t a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
    __asm__ volatile("" ::: "memory");
    return a[i];
}

// A negative offset off a buffer interior — OOB below the allocation.
int64_t f_negative_index(int64_t i) {
    int64_t a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
    int64_t *mid = &a[4];
    // `i` in [-8, 8): reads `mid[i]`, which underflows the array when `i < -4`.
    return mid[i];
}
