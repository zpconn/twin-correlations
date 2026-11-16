// Experiment (V): nu(d,r) = #{(a,s): a in [A,2A), s in [L,2L) odd, r*s | a*d+2}
// for d ~ L^2 odd, r ~ L odd, gcd(d,r)=1.  Compares Var(nu) with its mean.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]); double alpha=atof(argv[2]); int nd=atoi(argv[3]);
  ll A=(ll)floor(pow((double)L,alpha)); srand(12345);
  double sn=0,sm=0,sv=0,cnt=0;
  for(int t=0;t<nd;t++){
    ll d=L*L + 2*(rand()%(L*L/2)) + 1;
    for(ll r=L|1; r<2*L; r+=2){ if(gcdll(d,r)!=1) continue;
      ll a0=(r - (2*inv(d,r))%r)%r;            // a = -2/d mod r
      ll a=A - (A%r) + a0; if(a<A) a+=r;
      long nu=0;
      for(; a<2*A; a+=r){ ll m=(a*d+2)/r;
        for(ll s=L|1; s<2*L; s+=2) if(m%s==0) nu++; }
      double mu=0; for(ll s=L|1; s<2*L; s+=2) if(gcdll(s,d)==1) mu+=(double)A/((double)r*s);
      sn+=nu; sm+=mu; sv+=(nu-mu)*(nu-mu); cnt++; } }
  double K=(double)A/L;
  printf("L=%lld A=L^%.2f K=%.1f  mean_nu=%.3f mean_mu=%.3f  Var=%.3f  Var/mean=%.3f  Var/K^2=%.4f\n",
         L,alpha,K,sn/cnt,sm/cnt,sv/cnt,sv/sm,(sv/cnt)/(K*K));
  return 0; }
