// Experiment 6: correlation between the layers G_r and G_r' of G_q.
// corr(r,r') = Re <G_r,G_r'> / (|G_r| |G_r'|), norms over 1<=n<=Nmax.
// Prints the pairs with |corr| > thr and the summed cross term by class of (r, r').  usage: ./paircorr L q s thr
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ if(m==1) return 0; ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]), q=atoll(argv[2]), s=atoll(argv[3]); double thr=atof(argv[4]);
  ll H=(ll)floor(sqrt((double)L)); ll Nmax=4*H*L;
  ll maxP=L*L*L; double *wr=malloc(maxP*8),*wi=malloc(maxP*8),*zr=malloc(maxP*8),*zi=malloc(maxP*8);
  ll *start=malloc((L+1)*sizeof(ll)); ll P=0;
  for(ll r=L;r<2*L;r++){ start[r-L]=P; ll M=r*q;
    for(ll d=L*L;d<2*L*L;d++){ if(gcdll(d,M)!=1) continue;
      double th=2.0*M_PI*(double)((2*inv(d,M))%M)/(double)M; wr[P]=cos(th); wi[P]=sin(th); zr[P]=1; zi[P]=0; P++; } }
  start[L]=P;
  double *gr=malloc(L*8),*gi=malloc(L*8),*C=calloc(L*L,8);
  for(ll n=1;n<=Nmax;n++){
    for(ll rr=0;rr<L;rr++){ double ar=0,ai=0;
      #pragma omp simd reduction(+:ar,ai)
      for(ll k=start[rr];k<start[rr+1];k++){ double x=zr[k]*wr[k]-zi[k]*wi[k], y=zr[k]*wi[k]+zi[k]*wr[k]; zr[k]=x; zi[k]=y; ar+=x; ai+=y; }
      gr[rr]=ar; gi[rr]=ai; }
    for(ll a=0;a<L;a++) for(ll b=0;b<L;b++) C[a*L+b]+=gr[a]*gr[b]+gi[a]*gi[b]; }
  double diag=0,cp=0,cm=0,co=0; ll np=0,nm=0,no=0;
  for(ll a=0;a<L;a++){ diag+=C[a*L+a];
    for(ll b=0;b<L;b++){ if(a==b) continue; ll r=a+L, rp=b+L; double c=C[a*L+b];
      if((r-rp)%s==0){ cp+=c; np++; } else if((r+rp)%s==0){ cm+=c; nm++; } else { co+=c; no++; }
      double cor=c/sqrt(C[a*L+a]*C[b*L+b]); if(a<b && fabs(cor)>thr) printf("  r=%lld r'=%lld corr=%.3f  (r-r')%%s=%lld (r+r')%%s=%lld\n",r,rp,cor,((r-rp)%s+s)%s,(r+rp)%s); } }
  printf("L=%lld q=%lld s=%lld: diag=1, cross from r=r' mod s: %.3f (%lld pairs), r=-r' mod s: %.3f (%lld pairs), other: %.3f (%lld pairs)\n",
    L,q,s,cp/diag,np,cm/diag,nm,co/diag,no);
  return 0; }
