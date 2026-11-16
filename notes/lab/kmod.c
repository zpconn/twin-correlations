// Experiment 9: the block modulus by modulus.  K = sum_c K_c, K_c(m,n) = S(m,n;cq)/(cq).
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
    double *K=calloc(M*N,8),*Kc=malloc(M*N*8),*Gd=calloc(M*M,8),*Gc=malloc(M*M*8),*Vc=malloc(M*M*8); double sumtop=0,maxrel=0;
    for(ll c=C;c<2*C;c++){ if(c%q==0) continue; double *cs=malloc(c*8); for(ll j=0;j<c;j++) cs[j]=cos(2*M_PI*j/(double)c);
      double *Sc=calloc(c*c,8); for(ll x=1;x<=c;x++){ if(gcdll(x,c)!=1) continue; ll xi=inv(x,c);
        for(ll a=0;a<c;a++){ ll ax=a*x%c; for(ll b=0;b<c;b++) Sc[a*c+b]+=cs[(ax+b*xi)%c]; } }
      ll qb=inv(q,c), cb=inv(c,q), cb2=cb*cb%q;
      for(ll mi=0;mi<M;mi++){ ll m=M+mi; ll a=(m%c)*qb%c; ll mc=m%q*cb2%q;
        for(ll n=1;n<=N;n++){ ll b=(n%c)*qb%c; Kc[mi*N+n-1]=Sc[a*c+b]*Kl[mc*(n%q)%q]/((double)c*q); } }
      { double trc=0,top=0; for(ll x=0;x<M*N;x++) K[x]+=Kc[x]; for(ll u=0;u<M;u++) for(ll v=u;v<M;v++){ double t=0; for(ll n=0;n<N;n++) t+=Kc[u*N+n]*Kc[v*N+n]; Gc[u*M+v]=Gc[v*M+u]=t; Gd[u*M+v]+=t; if(u!=v) Gd[v*M+u]+=t; else trc+=t; }
        jacobi(Gc,Vc,M); for(int i=0;i<M;i++) if(Gc[i*M+i]>top) top=Gc[i*M+i]; sumtop+=top; if(top/(trc/M)>maxrel) maxrel=top/(trc/M); }
      free(cs); free(Sc); }
    double *G=calloc(M*M,8),*V=malloc(M*M*8); double tr=0;
    for(ll u=0;u<M;u++) for(ll v=u;v<M;v++){ double t=0; for(ll n=0;n<N;n++) t+=K[u*N+n]*K[v*N+n]; G[u*M+v]=G[v*M+u]=t; if(u==v) tr+=t; }
    double trd=0; for(ll u=0;u<M;u++) trd+=Gd[u*M+u];
    jacobi(G,V,M); double e1=0; for(int i=0;i<M;i++) if(G[i*M+i]>e1) e1=G[i*M+i];
    jacobi(Gd,V,M); double d1=0; for(int i=0;i<M;i++) if(Gd[i*M+i]>d1) d1=Gd[i*M+i];
    double mean=tr/M;
    printf("q=%lld M=%lld N=%lld | mean eig %.4g (diagonal-in-c part %.4g) | top(KK^T)/mean=%.2f  top(sum_c K_cK_c^T)/mean=%.2f  sum_c||K_c||^2/mean=%.2f  max_c top_c/mean_c=%.2f | q^{1/4}=%.1f\n",q,M,N,mean,trd/M,e1/mean,d1/mean,sumtop/mean,maxrel,pow((double)q,0.25));
    free(Kl); free(K); free(G); free(V); fflush(stdout); }
  return 0; }
