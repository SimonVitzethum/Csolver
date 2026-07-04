struct Pair { long a; long b; }
extern(C) long sum_pair(Pair* p) {   // D pointer
    return p.a + p.b;
}
class Node { long v; }               // D class = reference type
extern(C) long node_val(Node n) {
    return n.v;
}
