// Experiment 13: W(chi) = sum_{lambda != 0} N_lambda chi(lambda) for all characters chi mod q (q prime),
// where N_lambda is the pair-correlation count of the model point set (A: 1/(x c^2), B: 1/(x y)).
// (E4) is the statement that the mean square of |W(chi)| over chi != chi_0 is << q^{9/8 - delta} squared;
// the elementary bound is q^{3/2}, square-root size is q.   usage: ./wchi q
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <complex.h>
typedef long long ll;
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
static ll powmod(ll a, ll e, ll m){ ll r=1; a%=m; while(e){ if(e&1) r=r*a%m; a=a*a%m; e>>=1; } return r; }
static void run(ll q,int model,ll g){ ll R=(ll)floor(sqrt((double)q)); ll P=R*R; int *z=malloc(P*sizeof(int)); ll k=0;
  for(ll x=R;x<2*R;x++) for(ll c=R;c<2*R;c++){ ll v=model==0? (x%q)*(c*c%q)%q : (x*c)%q; z[k++]=(int)inv(v,q); }
  unsigned *N=calloc(q,sizeof(unsigned));
  for(ll i=0;i<P;i++){ int zi=z[i]; for(ll j=0;j<P;j++){ int d=zi-z[j]; if(d<0) d+=q; N[d]++; } }
  double mean=(double)P*P/q; double *a=malloc((q-1)*8); ll pw=1; for(ll e=0;e<q-1;e++){ a[e]=N[pw]-mean; pw=pw*g%q; }   // a[e] = N_{g^e} - mean
  // W(chi_j) = sum_e a[e] exp(2 pi i j e/(q-1)), j = 1..q-2  (naive DFT)
  double mx=0, ms=0; ll n=q-1; double complex *w=malloc(n*sizeof(double complex)); for(ll e=0;e<n;e++) w[e]=cexp(2*M_PI*I*e/(double)n);
  for(ll j=1;j<n;j++){ double complex s=0; ll idx=0; for(ll e=0;e<n;e++){ s+=a[e]*w[idx]; idx+=j; if(idx>=n) idx-=n; } double m=cabs(s); ms+=m*m; if(m>mx) mx=m; }
  printf("model %c q=%lld  rms |W(chi)|/q = %.3f   max |W(chi)|/q = %.3f   (elementary bound q^{1/2}=%.1f, needed q^{1/8}=%.2f)\n",model?'B':'A',q,sqrt(ms/(n-1))/q,mx/q,sqrt((double)q),pow((double)q,0.125));
  free(z); free(N); free(a); free(w); }
int main(int argc,char**argv){ ll q=atoll(argv[1]); ll g=2; for(;;g++){ int ok=1; ll m=q-1; for(ll p=2;p*p<=m;p++) if(m%p==0){ if(powmod(g,(q-1)/p,q)==1){ok=0;break;} while(m%p==0) m/=p; } if(ok&&m>1&&powmod(g,(q-1)/m,q)==1) ok=0; if(ok) break; }
  run(q,0,g); run(q,1,g); return 0; }
