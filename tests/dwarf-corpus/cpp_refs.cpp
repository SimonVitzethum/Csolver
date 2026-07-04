// C++ test inputs: references (T&) and reference/pointer class members.
#include <cstdint>

struct Point { int64_t x; int64_t y; };

// A C++ reference parameter (`DW_TAG_reference_type`): valid by the type system.
int64_t sum_ref(Point &p) {
    return p.x + p.y;
}

struct Holder { int64_t n; Point *inner; };

// A pointer member loaded then dereferenced.
int64_t via_member(Holder &h) {
    return h.inner->x;
}
