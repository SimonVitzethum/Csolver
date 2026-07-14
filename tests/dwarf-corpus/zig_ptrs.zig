// Zig pointer non-nullability is carried in the LLVM `nonnull` PARAMETER ATTRIBUTE
// (not DWARF, which Zig emits as DW_LANG_C99). A `*T` is non-null (emits `ptr nonnull`);
// a `?*T` optional is nullable (no `nonnull`). CSolver's language-independent `nonnull`
// recovery proves NoNullDeref for `*T` — while bounds/liveness stay UNKNOWN (a Zig `*T`
// may still dangle: manual memory management, no borrow checker).
export fn deref(p: *i32) i32 {
    return p.*;
}
export fn deref_opt(p: ?*i32) i32 {
    return if (p) |q| q.* else 0;
}
