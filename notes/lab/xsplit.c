// Experiment 7: split S(q) by pairs of the inner variable d (the "modulus picture").
// G_q(n) = sum_d K_d(n), K_d(n) = sum_{r~L, gcd(d,rq)=1} e(2 n inv(d)/(r q)).
// Reports total, sum_d |K_d|^2 (diag) and the rest (cross), divided by N*P.  usage: ./xsplit L q1 q2 ...
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ if(m==1) return 0; ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]); ll H=(ll)floor(sqrt((double)L)); ll Nmax=4*H*L; ll D=L*L;
  ll maxP=L*L*L; double *wr=malloc(maxP*8),*wi=malloc(maxP*8),*zr=malloc(maxP*8),*zi=malloc(maxP*8);
  ll *start=malloc((D+1)*sizeof(ll));
  printf("L=%lld Nmax=%lld\n     q        P        total   diag(d=d')  cross(d!=d')\n",L,Nmax);
  for(int a=2;a<argc;a++){ ll q=atoll(argv[a]); ll P=0;
    for(ll d=D;d<2*D;d++){ start[d-D]=P;
      for(ll r=L;r<2*L;r++){ ll M=r*q; if(gcdll(d,M)!=1) continue;
        double th=2.0*M_PI*(double)((2*inv(d,M))%M)/(double)M; wr[P]=cos(th); wi[P]=sin(th); zr[P]=1; zi[P]=0; P++; } }
    start[D]=P; double tot=0,diag=0;
    for(ll n=1;n<=Nmax;n++){ double Ar=0,Ai=0;
      for(ll dd=0;dd<D;dd++){ double ar=0,ai=0;
        for(ll k=start[dd];k<start[dd+1];k++){ double x=zr[k]*wr[k]-zi[k]*wi[k], y=zr[k]*wi[k]+zi[k]*wr[k]; zr[k]=x; zi[k]=y; ar+=x; ai+=y; }
        diag+=ar*ar+ai*ai; Ar+=ar; Ai+=ai; }
      tot+=Ar*Ar+Ai*Ai; }
    double c=(double)Nmax*(double)P;
    printf("%6lld %8lld %12.3f %12.3f %12.3f\n",q,P,tot/c,diag/c,(tot-diag)/c); }
  return 0; }
