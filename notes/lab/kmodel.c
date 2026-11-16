// Experiment 10: the finite-field model.  K0(m,n) = q^{-1/2} sum_{c in [C,2C)} S(1, m n cbar^2; q),
// m in [M,2M), 1<=n<=N, C=M=floor(sqrt q), N=floor(q^{3/4}), q prime.  No sum over an archimedean ball.
// Prints top eigenvalues of K0 K0^T over the mean, and the same after removing the quadratic character
// (the vector eta(m) = (m/q)).   usage: ./kmodel qlo qhi
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
static int isprime(ll n){ if(n<2) return 0; for(ll p=2;p*p<=n;p++) if(n%p==0) return 0; return 1; }
static ll powmod(ll a, ll e, ll m){ ll r=1; a%=m; while(e){ if(e&1) r=r*a%m; a=a*a%m; e>>=1; } return r; }
static void jacobi(double *A,int n){
  for(int sw=0;sw<60;sw++){ double off=0; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) off+=A[i*n+j]*A[i*n+j]; if(off<1e-22) break;
    for(int p=0;p<n;p++) for(int q=p+1;q<n;q++){ double apq=A[p*n+q]; if(fabs(apq)<1e-300) continue;
      double th=(A[q*n+q]-A[p*n+p])/(2*apq), t=(th>=0?1:-1)/(fabs(th)+sqrt(th*th+1)), c=1/sqrt(t*t+1), s=t*c;
      for(int k=0;k<n;k++){ double akp=A[k*n+p],akq=A[k*n+q]; A[k*n+p]=c*akp-s*akq; A[k*n+q]=s*akp+c*akq; }
      for(int k=0;k<n;k++){ double apk=A[p*n+k],aqk=A[q*n+k]; A[p*n+k]=c*apk-s*aqk; A[q*n+k]=s*apk+c*aqk; } } } }
static void top3(double *K,ll M,ll N,double *out){ double *G=calloc(M*M,8); double tr=0;
  for(ll a=0;a<M;a++) for(ll b=a;b<M;b++){ double s=0; for(ll n=0;n<N;n++) s+=K[a*N+n]*K[b*N+n]; G[a*M+b]=G[b*M+a]=s; if(a==b) tr+=s; }
  jacobi(G,M); double e1=0,e2=0,e3=0; for(int i=0;i<M;i++){ double e=G[i*M+i]; if(e>e1){ e3=e2; e2=e1; e1=e; } else if(e>e2){ e3=e2; e2=e; } else if(e>e3) e3=e; }
  out[0]=tr/M; out[1]=e1; out[2]=e2; out[3]=e3; free(G); }
int main(int argc,char**argv){ ll qlo=atoll(argv[1]),qhi=atoll(argv[2]);
  for(ll q=qlo;q<=qhi;q++){ if(!isprime(q)) continue;
    ll M=(ll)floor(sqrt((double)q)),C=M,N=(ll)floor(pow((double)q,0.75));
    double *Kl=malloc(q*8); { double *cs=malloc(q*8); for(ll j=0;j<q;j++) cs[j]=cos(2*M_PI*j/(double)q);
      ll *iv=malloc(q*sizeof(ll)); for(ll x=1;x<q;x++) iv[x]=inv(x,q);
      for(ll t=0;t<q;t++){ double s=0; for(ll x=1;x<q;x++) s+=cs[(x+t*iv[x])%q]; Kl[t]=s/sqrt((double)q); } free(cs); free(iv); }
    double *K=calloc(M*N,8);
    for(ll c=C;c<2*C;c++){ ll cb=inv(c,q), cb2=cb*cb%q;
      for(ll mi=0;mi<M;mi++){ ll mc=(M+mi)%q*cb2%q; for(ll n=1;n<=N;n++) K[mi*N+n-1]+=Kl[mc*(n%q)%q]; } }
    double o[4]; top3(K,M,N,o);
    // remove the quadratic character component eta(m) eta(n)
    double *em=malloc(M*8),*en=malloc(N*8); for(ll mi=0;mi<M;mi++) em[mi]=(powmod(M+mi,(q-1)/2,q)==1)?1:-1; for(ll n=1;n<=N;n++) en[n-1]=(powmod(n,(q-1)/2,q)==1)?1:-1;
    double co=0; for(ll mi=0;mi<M;mi++) for(ll n=0;n<N;n++) co+=K[mi*N+n]*em[mi]*en[n]; co/=(double)(M*N);
    for(ll mi=0;mi<M;mi++) for(ll n=0;n<N;n++) K[mi*N+n]-=co*em[mi]*en[n];
    double p[4]; top3(K,M,N,p);
    printf("q=%lld M=C=%lld N=%lld | mean eig %.1f (generic N*C=%.1f) | top3/mean= %.2f %.2f %.2f | quadratic character coefficient %.3f, after removing it: %.2f %.2f %.2f | edge %.2f, Bessel q/N=%.1f\n",
      q,M,N,o[0],(double)N*C,o[1]/o[0],o[2]/o[0],o[3]/o[0],co,p[1]/p[0],p[2]/p[0],p[3]/p[0],pow(1+sqrt((double)M/N),2),(double)q/N);
    free(Kl); free(K); free(em); free(en); fflush(stdout); }
  return 0; }
