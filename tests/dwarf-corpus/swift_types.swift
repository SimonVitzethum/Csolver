// Swift: a class instance is a non-null reference (unless Optional); a struct is
// a value. `inout` gives a mutable reference to a value.
final class Counter { var n: Int64 = 0 }
@_silgen_name("read_class") func readClass(_ c: Counter) -> Int64 {
    return c.n
}
struct Pair { var a: Int64; var b: Int64 }
@_silgen_name("sum_inout") func sumInout(_ p: inout Pair) -> Int64 {
    return p.a + p.b
}
