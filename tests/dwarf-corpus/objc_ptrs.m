// Objective-C: object pointers (id / Class*) are nullable, like C pointers —
// must be soundly declined. A C struct pointer behaves as in C.
struct Pair { long a; long b; };
long sum_pair(struct Pair *p) { return p->a + p->b; }
