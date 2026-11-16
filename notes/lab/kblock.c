// Experiment 8: is the block of the Kloosterman kernel "flat"?
// K(m,n) = sum_{c in [C,2C)} S(m,n;c q)/(c q),  m in [M,2M), 1 <= n <= N,  C = M = floor(sqrt(q)), N = floor(q^{3/4}).
// Reports the largest eigenvalue of K K^T against the mean eigenvalue (trace/M), and the Rayleigh quotient of
// the vector w_m = m^{-1/2}.  A flat (generic) block has ratio about (1+sqrt(M/N))^2.   usage: ./kblock q
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a; }
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
int main(int argc,char**argv){
  ll q=atoll(argv[1]); ll M=(ll)floor(sqrt((double)q)), C=M, N=(ll)floor(pow((double)q,0.75));
  double *K=calloc(M*N,8);
  for(ll c=C;c<2*C;c++){ ll mod=c*q; double *cs=malloc(mod*8); for(ll j=0;j<mod;j++) cs[j]=cos(2*M_PI*j/(double)mod);
    ll *xs=malloc(mod*sizeof(ll)),*xi=malloc(mod*sizeof(ll)); ll cnt=0;
    for(ll x=1;x<mod;x++) if(gcdll(x,mod)==1){ xs[cnt]=x; xi[cnt]=inv(x,mod); cnt++; }
    for(ll mi=0;mi<M;mi++){ ll m=M+mi; for(ll n=1;n<=N;n++){ double s=0;
        for(ll k=0;k<cnt;k++) s+=cs[(m*xs[k]+n*xi[k])%mod];
        K[mi*N+n-1]+=s/(double)mod; } }
    free(cs); free(xs); free(xi); }
  double *G=calloc(M*M,8); double tr=0;
  for(ll a=0;a<M;a++) for(ll b=0;b<M;b++){ double s=0; for(ll n=0;n<N;n++) s+=K[a*N+n]*K[b*N+n]; G[a*M+b]=s; if(a==b) tr+=s; }
  double *v=malloc(M*8),*u=malloc(M*8); for(ll a=0;a<M;a++) v[a]=1.0+0.01*a; double lam=0;
  for(int it=0;it<2000;it++){ double nr=0; for(ll a=0;a<M;a++){ double s=0; for(ll b=0;b<M;b++) s+=G[a*M+b]*v[b]; u[a]=s; nr+=s*s; }
    nr=sqrt(nr); lam=nr; for(ll a=0;a<M;a++) v[a]=u[a]/nr; }
  double num=0,den=0; for(ll a=0;a<M;a++) for(ll b=0;b<M;b++) num+=G[a*M+b]/sqrt((double)(M+a)*(M+b)); for(ll a=0;a<M;a++) den+=1.0/(M+a);
  double mean=tr/M;
  printf("q=%lld M=C=%lld N=%lld | mean eig=%.4g  top eig=%.4g  top/mean=%.2f  (flat block ~ %.2f) | w=m^{-1/2}: quotient/mean=%.2f | Weil-size mean eig would be %.4g\n",
    q,M,N,mean,lam,lam/mean,pow(1+sqrt((double)M/N),2),(num/den)/mean,(double)N*C*C/(C*(double)q));
  return 0; }
