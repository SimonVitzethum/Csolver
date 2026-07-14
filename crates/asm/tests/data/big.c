#include <stdint.h>
#include <string.h>
typedef struct { int64_t a,b,c,d; } S;
int64_t f1(int64_t*p,int64_t n){int64_t s=0;for(int64_t i=0;i<n;i++)s+=p[i]*p[n-i-1];return s;}
double f2(double*x,int n){double s=0;for(int i=0;i<n;i++)s+=x[i]*x[i];return s/n;}
float f3(float*a,float*b,int n){float s=0;for(int i=0;i<n;i++)s+=a[i]*b[i];return s;}
uint32_t f4(uint8_t*d,int n){uint32_t h=2166136261u;for(int i=0;i<n;i++){h^=d[i];h*=16777619u;}return h;}
int64_t f5(S*s){return s->a+s->b*s->c-s->d;}
void f6(int*a,int n){for(int i=0;i<n;i++)a[i]=(a[i]<<2)|(a[i]>>30);}
int64_t f7(int64_t x){return x<0?-x:(x==0?1:x*x);}
void f8(char*d,const char*s){while((*d++=*s++));}
uint64_t f9(uint64_t a,uint64_t b){return a>b?a%b:b%a;}
