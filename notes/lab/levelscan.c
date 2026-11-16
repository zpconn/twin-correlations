// Experiment 3: dependence on the level q of
//   G_q(n) = sum_{r~L, d~L^2, gcd(d,rq)=1} e(2 n inv(d)/(r q)),  1 <= n <= 4*floor(sqrt(L))*L.
// Reports mean |G|^2 / P (P = number of terms) and its split into the terms with
// r = r' ("diag") and r != r' ("cross").  usage: ./levelscan L q1 q2 ...
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ if(m==1) return 0; ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]); ll H=(ll)floor(sqrt((double)L)); ll Nmax=4*H*L;
  ll maxP=L*L*L; double *wr=malloc(maxP*8),*wi=malloc(maxP*8),*zr=malloc(maxP*8),*zi=malloc(maxP*8);
  ll *start=malloc((L+1)*sizeof(ll));
  printf("L=%lld Nmax=%lld\n     q        P   mean|G|^2/P    diag(r=r')   cross(r!=r')\n",L,Nmax);
  for(int a=2;a<argc;a++){ ll q=atoll(argv[a]); ll P=0;
    for(ll r=L;r<2*L;r++){ start[r-L]=P; ll M=r*q;
      for(ll d=L*L;d<2*L*L;d++){ if(gcdll(d,M)!=1) continue;
        double th=2.0*M_PI*(double)((2*inv(d,M))%M)/(double)M;
        wr[P]=cos(th); wi[P]=sin(th); zr[P]=1; zi[P]=0; P++; } }
    start[L]=P; double tot=0,diag=0;
    for(ll n=1;n<=Nmax;n++){ double Ar=0,Ai=0;
      for(ll rr=0;rr<L;rr++){ double ar=0,ai=0;
        #pragma omp simd reduction(+:ar,ai)
        for(ll k=start[rr];k<start[rr+1];k++){ double x=zr[k]*wr[k]-zi[k]*wi[k], y=zr[k]*wi[k]+zi[k]*wr[k]; zr[k]=x; zi[k]=y; ar+=x; ai+=y; }
        diag+=ar*ar+ai*ai; Ar+=ar; Ai+=ai; }
      tot+=Ar*Ar+Ai*Ai; }
    double c=(double)Nmax*(double)P;
    printf("%6lld %8lld %12.3f %12.3f %12.3f\n",q,P,tot/c,diag/c,(tot-diag)/c); }
  return 0; }
