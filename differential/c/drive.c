// Fuzzing driver for the C differential corpus.
//
// `./drive <fn> [cases]` runs the named corpus function over `cases` (default 64)
// deterministically-fuzzed inputs. Built under `-fsanitize=address,undefined
// -fno-sanitize-recover=all`, so the FIRST input that reaches UB aborts the
// process non-zero — the harness reads that as the soundness-oracle verdict.
//
// Each `drive_*` fuzzes across a range that includes the UB-triggering values, so
// a function that is UB "on a reachable input" is actually reached. A safe function
// stays clean across the whole sweep.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// A tiny dependency-free PRNG (SplitMix64), so a seed reproduces an input exactly.
static uint64_t rng_state;
static uint64_t next_u64(void) {
    rng_state += 0x9E3779B97F4A7C15ULL;
    uint64_t z = rng_state;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
// A signed integer in [lo, hi).
static int64_t next_range(int64_t lo, int64_t hi) {
    uint64_t span = (uint64_t) (hi - lo);
    return lo + (int64_t) (next_u64() % span);
}

// The corpus under test.
int64_t f_checked_get(int64_t);
int64_t f_const_index(void);
int64_t f_fill_loop(int64_t);
int64_t f_heap_guarded(int64_t);
int64_t f_memcpy_bounded(int64_t);
int64_t f_last(int64_t);
int64_t f_signed_ovf(int64_t);
int64_t f_unchecked_get(int64_t);
int64_t f_off_by_one(void);
int64_t f_heap_oob(int64_t);
int64_t f_use_after_free(int64_t);
int64_t f_double_free(int64_t);
int64_t f_asm_then_oob(int64_t);
int64_t f_negative_index(int64_t);

// `sink` keeps the compiler from optimizing calls away.
static volatile int64_t sink;

#define DRIVE(name, call)                             \
    static void drive_##name(int cases) {             \
        for (int c = 0; c < cases; c++) {             \
            sink = (call);                            \
        }                                             \
    }

// Safe functions: swept across the same wide ranges the unsafe ones use, to show
// they stay clean where a missing guard would not.
DRIVE(f_checked_get, f_checked_get(next_range(-8, 24)))
DRIVE(f_const_index, f_const_index())
DRIVE(f_fill_loop, f_fill_loop(next_range(-4, 24)))
DRIVE(f_heap_guarded, f_heap_guarded(next_range(-8, 24)))
DRIVE(f_memcpy_bounded, f_memcpy_bounded(next_range(-4, 40)))
DRIVE(f_last, f_last(next_range(-4, 12)))
// Harness-scoping control: arithmetic UB only — memory-clean under the memory oracle.
DRIVE(f_signed_ovf, f_signed_ovf(next_range(0, 4)))
// Unsafe functions: the range straddles the in-bounds/OOB boundary.
DRIVE(f_unchecked_get, f_unchecked_get(next_range(-8, 24)))
DRIVE(f_off_by_one, f_off_by_one())
DRIVE(f_heap_oob, f_heap_oob(next_range(-8, 24)))
DRIVE(f_use_after_free, f_use_after_free(next_range(0, 8)))
DRIVE(f_double_free, f_double_free(next_range(0, 8)))
DRIVE(f_asm_then_oob, f_asm_then_oob(next_range(-8, 24)))
DRIVE(f_negative_index, f_negative_index(next_range(-8, 8)))

struct entry {
    const char *name;
    void (*run)(int);
};
static const struct entry table[] = {
    {"f_checked_get", drive_f_checked_get},
    {"f_const_index", drive_f_const_index},
    {"f_fill_loop", drive_f_fill_loop},
    {"f_heap_guarded", drive_f_heap_guarded},
    {"f_memcpy_bounded", drive_f_memcpy_bounded},
    {"f_last", drive_f_last},
    {"f_signed_ovf", drive_f_signed_ovf},
    {"f_unchecked_get", drive_f_unchecked_get},
    {"f_off_by_one", drive_f_off_by_one},
    {"f_heap_oob", drive_f_heap_oob},
    {"f_use_after_free", drive_f_use_after_free},
    {"f_double_free", drive_f_double_free},
    {"f_asm_then_oob", drive_f_asm_then_oob},
    {"f_negative_index", drive_f_negative_index},
};

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s <fn> [cases]\n", argv[0]);
        return 2;
    }
    int cases = argc >= 3 ? atoi(argv[2]) : 64;
    // A fixed base seed keeps the sweep reproducible; each case draws the next value.
    rng_state = 0xC0FFEE123456789ULL;
    for (size_t i = 0; i < sizeof(table) / sizeof(table[0]); i++) {
        if (strcmp(table[i].name, argv[1]) == 0) {
            table[i].run(cases);
            return 0;
        }
    }
    fprintf(stderr, "unknown function: %s\n", argv[1]);
    return 2;
}
