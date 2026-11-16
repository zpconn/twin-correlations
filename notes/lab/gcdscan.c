// Experiment 5: mean of |G_q(n)|^2 / P by the value of g = gcd(n, q).
// G_q(n) = sum_{r~L, d~L^2, gcd(d,rq)=1} e(2 n inv(d)/(r q)), 1<=n<=4*floor(sqrt(L))*L.  usage: ./gcdscan L q
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ if(m==1) return 0; ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]), q=atoll(argv[2]); ll H=(ll)floor(sqrt((double)L)); ll Nmax=4*H*L;
  ll maxP=L*L*L; double *wr=malloc(maxP*8),*wi=malloc(maxP*8),*zr=malloc(maxP*8),*zi=malloc(maxP*8);
  ll P=0;
  for(ll r=L;r<2*L;r++){ ll M=r*q;
    for(ll d=L*L;d<2*L*L;d++){ if(gcdll(d,M)!=1) continue;
      double th=2.0*M_PI*(double)((2*inv(d,M))%M)/(double)M; wr[P]=cos(th); wi[P]=sin(th); zr[P]=1; zi[P]=0; P++; } }
  double *sum=calloc(q+1,8); ll *cnt=calloc(q+1,sizeof(ll)); double tot=0;
  for(ll n=1;n<=Nmax;n++){ double ar=0,ai=0;
    #pragma omp simd reduction(+:ar,ai)
    for(ll k=0;k<P;k++){ double x=zr[k]*wr[k]-zi[k]*wi[k], y=zr[k]*wi[k]+zi[k]*wr[k]; zr[k]=x; zi[k]=y; ar+=x; ai+=y; }
    double v=ar*ar+ai*ai; ll g=gcdll(n,q); sum[g]+=v; cnt[g]++; tot+=v; }
  printf("L=%lld q=%lld P=%lld  overall mean|G|^2/P = %.3f\n   g=gcd(n,q)   #n    mean|G|^2/P   share of total\n",L,q,P,tot/Nmax/P);
  for(ll g=1;g<=q;g++) if(cnt[g]) printf("   %8lld %6lld %12.3f %12.3f\n",g,cnt[g],sum[g]/cnt[g]/P,sum[g]/tot);
  return 0; }
