#include <cstdint>
struct Cell { int64_t v; };
struct RefHolder { int64_t tag; Cell &cell; };   // a C++ reference member
int64_t through_ref_member(RefHolder &h) {
    return h.cell.v;                              // load the Cell& field, deref it
}
