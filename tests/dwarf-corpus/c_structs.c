// C test inputs for DWARF-based pointee recovery. Each function reads through a
// pointer whose validity/size the opaque LLVM `ptr` erases but DWARF records.
#include <stdint.h>

typedef struct { int64_t a; int64_t b; } Pair;

// A pointer *parameter* to a sized struct: `p` points to 16 bytes.
int64_t sum_pair(Pair *p) {
    return p->a + p->b;
}

typedef struct { int64_t tag; int32_t *data; } Wrap;

// A pointer *member*: `w->data` is a loaded `int32_t*` field.
int32_t read_member(Wrap *w) {
    return *(w->data);
}

// A field read at a non-zero offset through the parameter.
int64_t second(Pair *p) {
    return p->b;
}
