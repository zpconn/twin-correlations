// Experiment 11: shift correlations of the model point sets on Z/q (q prime, R = floor(sqrt q)).
//   model A: z = inverse of x*c^2,  x,c in [R,2R)      (the model (MP) for the smooth vector)
//   model B: z = inverse of x*y,    x,y in [R,2R)      (variant with a product instead of a square)
// nu(z) = number of representations.  Prints Var(nu)/mean and, for shifts t, Cov(nu(z),nu(z+t))/mean.
// usage: ./mcorr q
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
static void run(ll q,int model){ ll R=(ll)floor(sqrt((double)q)); int *nu=calloc(q,sizeof(int)); double P=0;
  for(ll x=R;x<2*R;x++) for(ll c=R;c<2*R;c++){ ll v=model==0? (x%q)*(c*c%q)%q : (x*c)%q; nu[inv(v,q)]++; P++; }
  double mean=P/q, var=0; for(ll z=0;z<q;z++) var+=(nu[z]-mean)*(nu[z]-mean); var/=q;
  printf("model %c q=%lld points=%.0f mean=%.3f  Var/mean=%.3f | Cov(t)/mean, t=1,2,3,4,6,8,12,16,24,32,48,64:",model?'B':'A',q,P,mean,var/mean);
  int ts[12]={1,2,3,4,6,8,12,16,24,32,48,64};
  for(int i=0;i<12;i++){ int t=ts[i]; double s=0; for(ll z=0;z<q;z++) s+=(nu[z]-mean)*(nu[(z+t)%q]-mean); printf(" %.3f",s/q/mean); }
  // variance of window sums of length U = q^{1/4}
  ll U=(ll)floor(pow((double)q,0.25)); double *w=malloc(q*8); double s=0; for(ll z=0;z<U;z++) s+=nu[z]; double vw=0;
  for(ll z=0;z<q;z++){ w[z]=s; s+=nu[(z+U)%q]-nu[z]; } for(ll z=0;z<q;z++) vw+=(w[z]-U*mean)*(w[z]-U*mean); vw/=q;
  printf(" | windows U=%lld: Var/(U*mean)=%.3f (fully correlated would be %.1f)\n",U,vw/(U*mean),(double)U*var/mean);
  free(nu); free(w); }
int main(int argc,char**argv){ ll q=atoll(argv[1]); run(q,0); run(q,1); return 0; }
