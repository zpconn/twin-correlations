// Experiment 8d: single rows of the Kloosterman block.
// For m = 1..8 prints sum_{n<=N} K(m,n)^2 over the generic value N*sum_c phi(cq)/(cq)^2, where
// K(m,n) = sum_{c in [C,2C)} S(m,n;cq)/(cq), C = floor(sqrt q), N = floor(q^{3/4}), q prime.
// usage: ./krow qlo qhi
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
    ll C=(ll)floor(sqrt((double)q)),M=8,N=(ll)floor(pow((double)q,0.75));
    double *Kl=malloc(q*8); { double *cs=malloc(q*8); for(ll j=0;j<q;j++) cs[j]=cos(2*M_PI*j/(double)q);
      ll *iv=malloc(q*sizeof(ll)); for(ll x=1;x<q;x++) iv[x]=inv(x,q);
      for(ll t=0;t<q;t++){ double s=0; for(ll x=1;x<q;x++) s+=cs[(x+t*iv[x])%q]; Kl[t]=s; } free(cs); free(iv); }
    double *K=calloc(M*N,8);
    for(ll c=C;c<2*C;c++){ if(c%q==0) continue; double *cs=malloc(c*8); for(ll j=0;j<c;j++) cs[j]=cos(2*M_PI*j/(double)c);
      double *Sc=calloc(c*c,8); for(ll x=1;x<=c;x++){ if(gcdll(x,c)!=1) continue; ll xi=inv(x,c);
        for(ll a=0;a<c;a++){ ll ax=a*x%c; for(ll b=0;b<c;b++) Sc[a*c+b]+=cs[(ax+b*xi)%c]; } }
      ll qb=inv(q,c), cb=inv(c,q), cb2=cb*cb%q;
      for(ll mi=0;mi<M;mi++){ ll m=1+mi; ll a=(m%c)*qb%c; ll mc=m%q*cb2%q;
        for(ll n=1;n<=N;n++){ ll b=(n%c)*qb%c; K[mi*N+n-1]+=Sc[a*c+b]*Kl[mc*(n%q)%q]/((double)c*q); } }
      free(cs); free(Sc); }
    double *G=calloc(M*M,8),*V=malloc(M*M*8); double tr=0;
    for(ll a=0;a<M;a++) for(ll b=a;b<M;b++){ double s=0; for(ll n=0;n<N;n++) s+=K[a*N+n]*K[b*N+n]; G[a*M+b]=G[b*M+a]=s; if(a==b) tr+=s; }
    double gen=0; for(ll c=C;c<2*C;c++){ ll ph=0; for(ll x=1;x<=c;x++) if(gcdll(x,c)==1) ph++; gen+=(double)ph*(q-1)/((double)c*c*q*q); } gen*=N;
    printf("q=%lld C=%lld N=%lld generic=%.4g | sum_n K(m,n)^2/generic for m=1..8:",q,C,N,gen); for(int a=0;a<M;a++) printf(" %.2f",G[a*M+a]/gen);
    printf(" | Bessel/generic ~ q/N = %.1f\n",(double)q/N);
    free(Kl); free(K); free(G); free(V); fflush(stdout); }
  return 0; }
