const Pair = struct { a: i64, b: i64 };
// Zig `*Pair` single-item pointer — a valid pointer to a Pair by the type system
// (Zig pointers are non-null and valid unless `?*` optional).
export fn sum_pair(p: *const Pair) i64 {
    return p.a + p.b;
}
const Wrap = struct { tag: i64, inner: *const i64 };
export fn read_inner(w: *const Wrap) i64 {
    return w.inner.*;
}
