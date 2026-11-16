// Experiment 4: number variance of the points theta = 2*inv(d)/(r q) (r~L, d~L^2)
// in arcs of length K/q, K = 1,2,4,...  and the correlation of the counts in
// neighbouring arcs of length 1/q.   usage: ./arcs L q
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll inv(ll a, ll m){ ll g=m,x=0,y=1,b=((a%m)+m)%m; while(b){ ll q=g/b,t=g-q*b; g=b; b=t; t=x-q*y; x=y; y=t;} return ((x%m)+m)%m; }
int main(int argc,char**argv){
  ll L=atoll(argv[1]), q=atoll(argv[2]); ll nb=q; double *cnt=calloc(nb,sizeof(double)); ll P=0;
  for(ll r=L;r<2*L;r++){ ll M=r*q;
    for(ll d=L*L;d<2*L*L;d++){ if(gcdll(d,M)!=1) continue;
      ll x=(2*inv(d,M))%M;            // theta = x/M ; bin = floor(theta*q) = floor(x/r)
      cnt[x/r]+=1; P++; } }
  double mean=(double)P/nb;
  printf("L=%lld q=%lld P=%lld  mean per arc of length 1/q = %.2f\n",L,q,P,mean);
  printf("  K (arc = K/q)   mean      variance   var/mean\n");
  for(ll K=1;K<=nb/8;K*=2){ double s=0,s2=0; ll m=0;
    for(ll i=0;i+K<=nb;i+=K){ double c=0; for(ll j=0;j<K;j++) c+=cnt[i+j]; s+=c; s2+=c*c; m++; }
    double mu=s/m, var=s2/m-mu*mu; printf("  %6lld      %9.2f  %10.2f  %8.3f\n",K,mu,var,var/mu); }
  double v0=0; for(ll i=0;i<nb;i++) v0+=(cnt[i]-mean)*(cnt[i]-mean); v0/=nb;
  printf("  correlation of neighbouring arcs, lag k:");
  for(ll k=1;k<=8;k++){ double c=0; for(ll i=0;i<nb;i++) c+=(cnt[i]-mean)*(cnt[(i+k)%nb]-mean); printf(" %.3f",c/nb/v0); }
  printf("\n"); return 0; }
