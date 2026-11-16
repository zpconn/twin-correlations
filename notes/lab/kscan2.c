// Experiment 8c: spectrum of the Kloosterman block for an arbitrary level q (composite allowed).
// K(m,n) = sum_{c in [C,2C)} S(m,n;cq)/(cq), m in [M,2M), 1<=n<=N, C=M=floor(sqrt q), N=floor(q^{3/4}).
// usage: ./kscan2 q [q ...]
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a; }
static void jacobi(double *A,int n){
  for(int sw=0;sw<60;sw++){ double off=0; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) off+=A[i*n+j]*A[i*n+j]; if(off<1e-22) break;
    for(int p=0;p<n;p++) for(int q=p+1;q<n;q++){ double apq=A[p*n+q]; if(fabs(apq)<1e-300) continue;
      double th=(A[q*n+q]-A[p*n+p])/(2*apq), t=(th>=0?1:-1)/(fabs(th)+sqrt(th*th+1)), c=1/sqrt(t*t+1), s=t*c;
      for(int k=0;k<n;k++){ double akp=A[k*n+p],akq=A[k*n+q]; A[k*n+p]=c*akp-s*akq; A[k*n+q]=s*akp+c*akq; }
      for(int k=0;k<n;k++){ double apk=A[p*n+k],aqk=A[q*n+k]; A[p*n+k]=c*apk-s*aqk; A[q*n+k]=s*apk+c*aqk; } } } }
static double *ktab(ll c){ double *cs=malloc(c*8); for(ll j=0;j<c;j++) cs[j]=cos(2*M_PI*j/(double)c);
  double *S=calloc(c*c,8); for(ll x=1;x<=c;x++){ if(gcdll(x,c)!=1) continue; ll xi=inv(x,c);
    for(ll a=0;a<c;a++){ ll ax=a*x%c; double *row=S+a*c; ll idx=ax; for(ll b=0;b<c;b++){ row[b]+=cs[idx]; idx+=xi; if(idx>=c) idx-=c; } } }
  free(cs); return S; }
int main(int argc,char**argv){
  for(int ai=1;ai<argc;ai++){ ll q=atoll(argv[ai]);
    ll M=(ll)floor(sqrt((double)q)),C=M,N=(ll)floor(pow((double)q,0.75));
    double *Sq=ktab(q); double *K=calloc(M*N,8); int nslow=0;
    for(ll c=C;c<2*C;c++){
      if(gcdll(c,q)==1){ double *Sc=ktab(c); ll qb=inv(q,c), cb=inv(c,q);
        for(ll mi=0;mi<M;mi++){ ll m=M+mi; ll a=(m%c)*qb%c; ll aq=(m%q)*cb%q;
          for(ll n=1;n<=N;n++){ ll b=(n%c)*qb%c; ll bq=(n%q)*cb%q; K[mi*N+n-1]+=Sc[a*c+b]*Sq[aq*q+bq]/((double)c*q); } }
        free(Sc); }
      else { nslow++; ll mod=c*q; double *cs=malloc(mod*8); for(ll j=0;j<mod;j++) cs[j]=cos(2*M_PI*j/(double)mod);
        for(ll x=1;x<mod;x++){ if(gcdll(x,mod)!=1) continue; ll xi=inv(x,mod);
          for(ll mi=0;mi<M;mi++){ ll mx=(M+mi)*x%mod; ll idx=mx; double *row=K+mi*N; for(ll n=1;n<=N;n++){ idx+=xi; if(idx>=mod) idx-=mod; row[n-1]+=cs[idx]/(double)mod; } } }
        free(cs); } }
    double *G=calloc(M*M,8); double tr=0;
    for(ll a=0;a<M;a++) for(ll b=a;b<M;b++){ double s=0; for(ll n=0;n<N;n++) s+=K[a*N+n]*K[b*N+n]; G[a*M+b]=G[b*M+a]=s; if(a==b) tr+=s; }
    double num=0,den=0; for(ll a=0;a<M;a++) for(ll b=0;b<M;b++) num+=G[a*M+b]/sqrt((double)(M+a)*(M+b)); for(ll a=0;a<M;a++) den+=1.0/(M+a);
    jacobi(G,M); double e1=0,e2=0,e3=0;
    for(int i=0;i<M;i++){ double e=G[i*M+i]; if(e>e1){ e3=e2; e2=e1; e1=e; } else if(e>e2){ e3=e2; e2=e; } else if(e>e3) e3=e; }
    double mean=tr/M, edge=pow(1+sqrt((double)M/N),2);
    printf("q=%lld M=%lld N=%lld (non-coprime c: %d) mean=%.4g  top3/mean= %.2f %.2f %.2f  flat edge=%.2f  smooth vector/mean=%.2f  1+q^{1/4}=%.2f\n",q,M,N,nslow,mean,e1/mean,e2/mean,e3/mean,edge,(num/den)/mean,1+pow((double)q,0.25));
    free(Sq); free(K); free(G); fflush(stdout); }
  return 0; }
