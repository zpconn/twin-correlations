// Experiment 12: the complete fourth moment (additive energy) of the model point sets.
//   model A: z = inverse of x*c^2;  model B: z = inverse of x*y;  x,c,y in [R,2R), R = floor(sqrt q), q prime.
// N_lambda = #{(z,z') : z - z' = lambda}.  Prints F = sum_{lambda != 0} (N_lambda - P^2/q)^2 / (P^2),
// where P = number of points.  Independent points give F close to 1 (model A) -- the sufficient
// condition (E4) for the short-shift statement is F << q^{1/4 - delta}; the trivial bound is F <= q.
// usage: ./e4 q
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
static void run(ll q,int model){ ll R=(ll)floor(sqrt((double)q)); ll P=R*R; int *z=malloc(P*sizeof(int)); ll k=0;
  for(ll x=R;x<2*R;x++) for(ll c=R;c<2*R;c++){ ll v=model==0? (x%q)*(c*c%q)%q : (x*c)%q; z[k++]=(int)inv(v,q); }
  unsigned *N=calloc(q,sizeof(unsigned));
  for(ll i=0;i<P;i++){ int zi=z[i]; for(ll j=0;j<P;j++){ int d=zi-z[j]; if(d<0) d+=q; N[d]++; } }
  double mean=(double)P*P/q, F=0, mx=0; for(ll l=1;l<q;l++){ double e=N[l]-mean; F+=e*e; if(fabs(e)>mx) mx=fabs(e); }
  printf("model %c q=%lld P=%lld  N_0=%u (P=%lld)  F=%.3f  max|N_l - mean|/sqrt(mean)=%.2f  | q^{1/4}=%.1f, trivial q=%lld\n",model?'B':'A',q,P,N[0],P,F/((double)P*P),mx/sqrt(mean),pow((double)q,0.25),q);
  free(z); free(N); }
int main(int argc,char**argv){ ll q=atoll(argv[1]); run(q,0); run(q,1); return 0; }
