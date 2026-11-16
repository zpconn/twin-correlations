// Experiment 8b: spectrum of the Kloosterman block, fast version (twisted multiplicativity).
// K(m,n) = sum_{c in [C,2C), (c,q)=1} S(m,n;cq)/(cq), m in [M,2M), 1<=n<=N, C=M=floor(sqrt q), N=floor(q^{3/4}), q prime.
// Prints the three largest eigenvalues of K K^T over the mean eigenvalue, and the Marchenko-Pastur edge.
// usage: ./kscan qlo qhi [v]     (v: also print the top eigenvector)
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a; }
static int isprime(ll n){ if(n<2) return 0; for(ll p=2;p*p<=n;p++) if(n%p==0) return 0; return 1; }
static void jacobi(double *A,double *V,int n){ for(int i=0;i<n;i++) for(int j=0;j<n;j++) V[i*n+j]=(i==j);
  for(int sw=0;sw<60;sw++){ double off=0; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) off+=A[i*n+j]*A[i*n+j]; if(off<1e-22) break;
    for(int p=0;p<n;p++) for(int q=p+1;q<n;q++){ double apq=A[p*n+q]; if(fabs(apq)<1e-300) continue;
      double th=(A[q*n+q]-A[p*n+p])/(2*apq), t=(th>=0?1:-1)/(fabs(th)+sqrt(th*th+1)), c=1/sqrt(t*t+1), s=t*c;
      for(int k=0;k<n;k++){ double akp=A[k*n+p],akq=A[k*n+q]; A[k*n+p]=c*akp-s*akq; A[k*n+q]=s*akp+c*akq; }
      for(int k=0;k<n;k++){ double apk=A[p*n+k],aqk=A[q*n+k]; A[p*n+k]=c*apk-s*aqk; A[q*n+k]=s*apk+c*aqk; }
      for(int k=0;k<n;k++){ double vkp=V[k*n+p],vkq=V[k*n+q]; V[k*n+p]=c*vkp-s*vkq; V[k*n+q]=s*vkp+c*vkq; } } } }
int main(int argc,char**argv){ ll qlo=atoll(argv[1]),qhi=atoll(argv[2]); int pv=argc>3; ll step=1; if(argc>3&&argv[3][0]=='s'){ pv=0; step=atoll(argv[3]+1); } ll seen=0;
  for(ll q=qlo;q<=qhi;q++){ if(!isprime(q)) continue; if((seen++)%step) continue;
    ll M=(ll)floor(sqrt((double)q)),C=M,N=(ll)floor(pow((double)q,0.75));
    double *Kl=malloc(q*8); { double *cs=malloc(q*8); for(ll j=0;j<q;j++) cs[j]=cos(2*M_PI*j/(double)q);
      ll *iv=malloc(q*sizeof(ll)); for(ll x=1;x<q;x++) iv[x]=inv(x,q);
      for(ll t=0;t<q;t++){ double s=0; for(ll x=1;x<q;x++) s+=cs[(x+t*iv[x])%q]; Kl[t]=s; } free(cs); free(iv); }
    double *K=calloc(M*N,8);
    for(ll c=C;c<2*C;c++){ if(c%q==0) continue; double *cs=malloc(c*8); for(ll j=0;j<c;j++) cs[j]=cos(2*M_PI*j/(double)c);
      double *Sc=calloc(c*c,8); for(ll x=1;x<=c;x++){ if(gcdll(x,c)!=1) continue; ll xi=inv(x,c);
        for(ll a=0;a<c;a++){ ll ax=a*x%c; for(ll b=0;b<c;b++) Sc[a*c+b]+=cs[(ax+b*xi)%c]; } }
      ll qb=inv(q,c), cb=inv(c,q), cb2=cb*cb%q;
      for(ll mi=0;mi<M;mi++){ ll m=M+mi; ll a=(m%c)*qb%c; ll mc=m%q*cb2%q;
        for(ll n=1;n<=N;n++){ ll b=(n%c)*qb%c; K[mi*N+n-1]+=Sc[a*c+b]*Kl[mc*(n%q)%q]/((double)c*q); } }
      free(cs); free(Sc); }
    double *G=calloc(M*M,8),*V=malloc(M*M*8); double tr=0;
    for(ll a=0;a<M;a++) for(ll b=a;b<M;b++){ double s=0; for(ll n=0;n<N;n++) s+=K[a*N+n]*K[b*N+n]; G[a*M+b]=G[b*M+a]=s; if(a==b) tr+=s; }
    jacobi(G,V,M); double e1=0,e2=0,e3=0; int i1=0;
    for(int i=0;i<M;i++){ double e=G[i*M+i]; if(e>e1){ e3=e2; e2=e1; e1=e; i1=i; } else if(e>e2){ e3=e2; e2=e; } else if(e>e3) e3=e; }
    double mean=tr/M, edge=pow(1+sqrt((double)M/N),2); int nout=0; for(int i=0;i<M;i++) if(G[i*M+i]>1.25*edge*mean) nout++;
    printf("q=%lld M=%lld N=%lld mean=%.4g  top3/mean= %.2f %.2f %.2f  MP edge=%.2f  outliers(>1.25 edge)=%d  1+q^{1/4}=%.2f\n",q,M,N,mean,e1/mean,e2/mean,e3/mean,edge,nout,1+pow((double)q,0.25));
    if(pv){ printf("  top eigenvector (m: v_m): "); for(int a=0;a<M;a++) printf("%lld:%.2f ",M+a,V[a*M+i1]); printf("\n"); }
    free(Kl); free(K); free(G); free(V); fflush(stdout); }
  return 0; }
