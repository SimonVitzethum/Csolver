#include <stdint.h>
int64_t alu(int64_t a, int64_t b){ return (a+b)*(a-b) ^ (a&b) | (a<<3); }
double fp(double x, double y){ return x*y + x/y - 0.5; }
int64_t mem(int64_t *p, int i){ return p[i] + p[i+1]; }
int64_t branchy(int64_t n){ int64_t s=0; for(int64_t i=0;i<n;i++){ if(i&1) s+=i; else s-=i; } return s; }
extern int ext(int);
int calls(int a){ return ext(a)+ext(a+1); }
