#include <stdint.h>
#include <string.h>
void vadd(float* a, float* b, float* c, int n){ for(int i=0;i<n;i++) c[i]=a[i]+b[i]; }
uint64_t bits(uint64_t x){ return __builtin_popcountll(x) + __builtin_clzll(x) + (x>>7); }
void cpy(void* d, void* s, unsigned long n){ memcpy(d,s,n); }
int cmpsel(int a,int b,int c){ return a>b? c: (a<b? a: b); }
long shifts(long x, int s){ return (x<<s) | (x>>s) | (x*17) % 13; }
