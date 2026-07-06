#include <stddef.h>
#include <stdint.h>
extern unsigned long copy_from_user(void*, const void*, unsigned long);
extern void *kmalloc(unsigned long, unsigned);
extern void kfree(const void*);

struct req { unsigned int len; unsigned int cmd; };

// Realistischer Treiber-ioctl: user-kontrollierte Länge in Stack-Buffer (CVE-Muster).
long dev_ioctl_vuln(void *user_arg) {
    struct req r;
    char buf[128];
    if (copy_from_user(&r, user_arg, sizeof(r))) return -14;
    __asm__ volatile("lfence" ::: "memory");        // typische Kernel-Barrier
    if (copy_from_user(buf, user_arg, r.len)) return -14;   // BUG: r.len ungeprüft
    return buf[0];
}

// Gefixte Variante mit Längenprüfung.
long dev_ioctl_safe(void *user_arg) {
    struct req r;
    char buf[128];
    if (copy_from_user(&r, user_arg, sizeof(r))) return -14;
    if (r.len > sizeof(buf)) return -22;
    if (copy_from_user(buf, user_arg, r.len)) return -14;
    return buf[0];
}

// Heap-UAF: kmalloc, free, dann noch benutzt.
long dev_uaf(unsigned n) {
    char *p = kmalloc(64, 0);
    if (!p) return -12;
    p[0] = 1;
    kfree(p);
    return p[n & 63];   // BUG: use-after-free
}
