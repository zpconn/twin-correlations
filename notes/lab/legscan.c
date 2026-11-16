// For q = p^2: mean of |G_q(n)|^2/P and of Re G, Im G, split by the Legendre symbol (2n/p).  usage: ./legscan L p
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
static ll pw(ll a, ll e, ll m){ ll r=1; a%=m; while(e){ if(e&1) r=r*a%m; a=a*a%m; e>>=1;} return r; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]), p=atoll(argv[2]), q=p*p; ll H=(ll)floor(sqrt((double)L)); ll Nmax=4*H*L;
  ll maxP=L*L*L; double *wr=malloc(maxP*8),*wi=malloc(maxP*8),*zr=malloc(maxP*8),*zi=malloc(maxP*8); ll P=0;
  for(ll r=L;r<2*L;r++){ ll M=r*q;
    for(ll d=L*L;d<2*L*L;d++){ if(gcdll(d,M)!=1) continue;
      double th=2.0*M_PI*(double)((2*inv(d,M))%M)/(double)M; wr[P]=cos(th); wi[P]=sin(th); zr[P]=1; zi[P]=0; P++; } }
  double s2[3]={0,0,0},sr[3]={0,0,0},si[3]={0,0,0}; ll c[3]={0,0,0};
  for(ll n=1;n<=Nmax;n++){ double ar=0,ai=0;
    #pragma omp simd reduction(+:ar,ai)
    for(ll k=0;k<P;k++){ double x=zr[k]*wr[k]-zi[k]*wi[k], y=zr[k]*wi[k]+zi[k]*wr[k]; zr[k]=x; zi[k]=y; ar+=x; ai+=y; }
    ll t=(2*n)%p; int cls = t==0 ? 2 : (pw(t,(p-1)/2,p)==1 ? 0 : 1);
    s2[cls]+=ar*ar+ai*ai; sr[cls]+=ar; si[cls]+=ai; c[cls]++; }
  const char*nm[3]={"(2n/p)=+1","(2n/p)=-1","p | n    "};
  printf("L=%lld p=%lld q=%lld P=%lld sqrt(P)=%.1f\n",L,p,q,P,sqrt((double)P));
  for(int k=0;k<3;k++) if(c[k]) printf("  %s  #n=%lld  mean|G|^2/P=%.3f  mean Re G=%.1f  mean Im G=%.1f\n",nm[k],c[k],s2[k]/c[k]/P,sr[k]/c[k],si[k]/c[k]);
  return 0; }
