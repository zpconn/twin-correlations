// Experiment 14: for a pair (s,s') ~ L, q = s s', with G(n) = sum_{r~L, d~L^2} e(2 n inv(d)/(r q)):
//  (a) the H x H block M[h][h'] = G(h s' - h' s), h,h' in [H,2H): ratio ||M||_op^2 / ||M||_HS^2
//      (1 = rank one; about 4/H for a random matrix), and mean |G|^2 / P on the block;
//  (b) the fourth moment over ALL 0<n<=N=2HL: mean|G|^4 / (mean|G|^2)^2  (2 for complex Gaussian);
//  (c) Fourier coefficients of |G(n)|^2 in n mod s at the frequencies w*inv(s') mod s, 0<|w|<=H,
//      relative to the total mass (this is what non-concentration on the Bohr set needs small).
// usage: ./blockrank L npairs
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
static double rnd(){ return (rand()+0.5)/(RAND_MAX+1.0); }
static double gauss(){ return sqrt(-2*log(rnd()))*cos(2*M_PI*rnd()); }
static double opnorm2(int H,double*mr,double*mi){ // largest eigenvalue of M M^*
  double *vr=calloc(H,8),*vi=calloc(H,8),*wr=calloc(H,8),*wi=calloc(H,8),*ur=calloc(H,8),*ui=calloc(H,8); double lam=0;
  for(int i=0;i<H;i++){ vr[i]=gauss(); vi[i]=gauss(); }
  for(int it=0;it<400;it++){
    for(int j=0;j<H;j++){ double a=0,b=0; for(int i=0;i<H;i++){ double xr=mr[i*H+j],xi=-mi[i*H+j]; a+=xr*vr[i]-xi*vi[i]; b+=xr*vi[i]+xi*vr[i]; } wr[j]=a; wi[j]=b; }
    for(int i=0;i<H;i++){ double a=0,b=0; for(int j=0;j<H;j++){ double xr=mr[i*H+j],xi=mi[i*H+j]; a+=xr*wr[j]-xi*wi[j]; b+=xr*wi[j]+xi*wr[j]; } ur[i]=a; ui[i]=b; }
    double nn=0; for(int i=0;i<H;i++) nn+=ur[i]*ur[i]+ui[i]*ui[i]; nn=sqrt(nn); lam=nn;
    for(int i=0;i<H;i++){ vr[i]=ur[i]/nn; vi[i]=ui[i]/nn; } }
  free(vr);free(vi);free(wr);free(wi);free(ur);free(ui); return lam; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]); int np=atoi(argv[2]); srand(2026);
  int H=(int)floor(sqrt((double)L)); ll Nmax=2*H*2*L+1;
  ll maxP=L*L*L; double *wr=malloc(maxP*8),*wi=malloc(maxP*8),*zr=malloc(maxP*8),*zi=malloc(maxP*8);
  double *gr=malloc((Nmax+1)*8),*gi=malloc((Nmax+1)*8);
  double *mr=malloc(H*H*8),*mi=malloc(H*H*8);
  double sRat=0,sBohr=0,sKurt=0,sSm=0,sTw=0,sTwMax=0,sRand=0;
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
      gr[n]=ar; gi[n]=ai; }
    // (a) block
    double hs=0;
    for(int i=0;i<H;i++) for(int j=0;j<H;j++){ ll n=(ll)(H+i)*sp-(ll)(H+j)*s; ll m=n<0?-n:n; double a=gr[m], b=(n<0?-gi[m]:gi[m]); if(n==0){a=0;b=0;}
      mr[i*H+j]=a; mi[i*H+j]=b; hs+=a*a+b*b; }
    double op=opnorm2(H,mr,mi); sRat+=op/hs; sBohr+=hs/((double)H*H*P);
    double smr=0,smi=0; for(int i=0;i<H*H;i++){ smr+=mr[i]; smi+=mi[i]; } sSm+=(smr*smr+smi*smi)/((double)H*H*hs);
    // random baseline
    double hs2=0; for(int i=0;i<H*H;i++){ mr[i]=gauss(); mi[i]=gauss(); hs2+=mr[i]*mr[i]+mi[i]*mi[i]; } sRand+=opnorm2(H,mr,mi)/hs2;
    // (b) kurtosis over all n <= N
    ll N=2*H*L; double m2=0,m4=0; for(ll n=1;n<=N;n++){ double g2=gr[n]*gr[n]+gi[n]*gi[n]; m2+=g2; m4+=g2*g2; }
    sKurt+=(m4/N)/((m2/N)*(m2/N));
    // (c) twisted masses at k = w*inv(s') mod s
    ll isp=inv(sp,s); double av=0,mx=0;
    for(int w=1;w<=H;w++){ ll k=(w*isp)%s; double cr=0,ci=0;
      for(ll n=1;n<=N;n++){ double g2=gr[n]*gr[n]+gi[n]*gi[n]; double ph=2.0*M_PI*(double)((k*(n%s))%s)/(double)s; cr+=g2*cos(ph); ci+=g2*sin(ph); }
      double rel=sqrt(cr*cr+ci*ci)/m2; av+=rel; if(rel>mx) mx=rel; }
    sTw+=av/H; sTwMax+=mx; }
  printf("L=%lld H=%d pairs=%d | block: op^2/HS^2=%.3f (random %.3f, rank-one 1) mean|G|^2/P=%.3f smooth-vector share=%.3f (flat 1/H=%.3f) | all n: kurtosis=%.2f | twisted mass: avg=%.3f max=%.3f (N^-1/2=%.3f)\n",
    L,H,np,sRat/np,sRand/np,sBohr/np,sSm/np,1.0/H,sKurt/np,sTw/np,sTwMax/np,1.0/sqrt(2.0*H*L));
  return 0; }
