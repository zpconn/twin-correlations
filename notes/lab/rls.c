// Experiment (RLS): for a pair (s,s') ~ L, the point set
//   Theta = { 2*inv(d)/(r s s') mod 1 : r ~ L, d ~ L^2, gcd(d, r s s') = 1 }
// has Fourier transform G(n) = sum_points e(n*theta).  Compare the mean of
// |G(n)|^2 over the Bohr set N = { h s' - h' s : h,h' ~ H }, H = sqrt(L),
// with its mean over all n in the same range, in units of P = #points
// (P is the square-root-cancellation value of |G|^2).
// usage: ./rls L npairs
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]); int np=atoi(argv[2]); srand(2026);
  ll H=(ll)floor(sqrt((double)L)); ll Nmax=4*H*L;
  ll maxP=L*L*L; double *wr=malloc(maxP*8),*wi=malloc(maxP*8),*zr=malloc(maxP*8),*zi=malloc(maxP*8);
  double *g2=malloc((Nmax+1)*8),*gr=malloc((Nmax+1)*8);
  double tA=0,tAc=0,tN=0,tNc=0,tS=0,tNs=0,tLo=0; double cA=0,cAc=0,cN=0,cNc=0,cLo=0,cpairs=0,tP=0;
  for(int t=0;t<np;t++){
    ll s,sp; do{ s=L+rand()%L; sp=L+rand()%L; }while(s==sp||gcdll(s,sp)!=1);
    ll P=0;
    for(ll r=L;r<2*L;r++){ ll M=r*s*sp;
      for(ll d=L*L;d<2*L*L;d++){ if(gcdll(d,M)!=1) continue;
        double th=2.0*M_PI*(double)((2*inv(d,M))%M)/(double)M;
        wr[P]=cos(th); wi[P]=sin(th); zr[P]=1; zi[P]=0; P++; } }
    for(ll n=1;n<=Nmax;n++){ double ar=0,ai=0;
      #pragma omp simd reduction(+:ar,ai)
      for(ll k=0;k<P;k++){ double a=zr[k]*wr[k]-zi[k]*wi[k], b=zr[k]*wi[k]+zi[k]*wr[k]; zr[k]=a; zi[k]=b; ar+=a; ai+=b; }
      g2[n]=ar*ar+ai*ai; gr[n]=ar; }
    ll q=s*sp;
    for(ll n=1;n<=Nmax;n++){ tA+=g2[n]; cA++; if(gcdll(n,q)==1){ tAc+=g2[n]; cAc++; }
      if(n<=Nmax/4 && gcdll(n,q)==1){ tLo+=g2[n]; cLo++; } }
    double sgn=0; ll cnt=0;
    for(ll h=H;h<2*H;h++) for(ll hp=H;hp<2*H;hp++){ ll n=h*sp-hp*s; if(n==0) continue; ll m=n<0?-n:n; if(m>Nmax) continue;
      tN+=g2[m]; cN++; sgn+=gr[m]; cnt++; if(gcdll(m,q)==1){ tNc+=g2[m]; cNc++; } }
    tS+=sgn*sgn; tNs+=(double)cnt*P; tP+=P; cpairs++; }
  double Pm=tP/cpairs;
  printf("L=%lld H=%lld pairs=%d P=%.0f | mean|G|^2/P: all=%.3f all_coprime=%.3f low_coprime=%.3f Bohr=%.3f Bohr_coprime=%.3f | (sum_Bohr Re G)^2/(|N| P)=%.3f\n",
    L,H,np,Pm,(tA/cA)/Pm,(tAc/cAc)/Pm,(tLo/cLo)/Pm,(tN/cN)/Pm,(tNc/cNc)/Pm,tS/tNs);
  return 0; }
