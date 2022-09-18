#include "pari.h"
#include "paripriv.h"

long
TotalDegree(GEN F)
{
  GEN Fi;
  long D,d,di,i;
  if(gequal0(F)) return -1;
  if(typ(F)!=t_POL) return 0;
  d = degree(F);
  D = -1;
  for(i=0;i<=d;i++)
  {
    Fi = gel(F,i+2);
    if(gequal0(Fi)) continue;
    di = i+TotalDegree(Fi);
    if(di>D) D = di;
  }
  return D;
}

GEN
PolHomogenise(GEN f, GEN z, long D)
{
  pari_sp av = avma;
  GEN F;
  long d,i;
  if(gequal0(f)) return gcopy(gen_0);
  if(typ(f)!=t_POL)
  {
    if(D==-1) return gcopy(f);
    F = gmul(f,gpowgs(z,D));
    return gerepileupto(av,F);
  }
  F = gcopy(f);
  d = degree(f);
  if(D==-1) D = TotalDegree(F);
  for(i=0;i<=d;i++)
  {
    gel(F,i+2) = PolHomogenise(gel(f,i+2),z,D-i);
  }
  return gerepilecopy(av,F);
}

GEN
RgXY_RgX_div(GEN N, GEN D, ulong dy)
{
  pari_sp av = avma;
  GEN V,N1,D1,G,R;
  ulong vx,vy,dx,i,dG;
  V = variables_vecsmall(N);
  if(lg(V)<3 || lg(variables_vecsmall(D))==1)
    return gdiv(N,D);
  vx = V[1];
  vy = V[2];
  dx = degpol(N);
  N1 = RgXY_swap(N,dy,vy);
  dy = degpol(N1);
  D1 = gcopy(D);
  setvarn(D1,vy);
  V = cgetg(dy+3,t_VEC);
  for(i=0;i<=dy;i++)
  {
    gel(V,i+1) = gel(N1,i+2);
  }
  gel(V,dy+2) = D1;
  G = content0(V,NULL);
  for(i=0;i<=dy;i++)
  {
    gel(N1,i+2) = RgX_div(gel(N1,i+2),G);
  }
  dG = degpol(G);
  if(degpol(D1)==dG)
  {
    N1 = RgXY_swap(N1,dx-dG,vy);
    return gerepilecopy(av,N1);
  }
  D1 = RgX_div(D1,G);
  setvarn(D1,vx);
  R = cgetg(3,t_RFRAC);
  gel(R,1) = RgXY_swap(N1,dx-dG,vy);
  gel(R,2) = D1;
  return gerepilecopy(av,R);
}

// Zeta functions

GEN
ZetaFromPointCount(GEN N, ulong p, ulong g)
{
  pari_sp av = avma;
  GEN Z,L,Pi;
  ulong i;
  if(g==0)
    return pol_1(0);
  Z = cgetg(g+2,t_SER);
  Z[1] = 0;
  setsigne(Z,1);
  setvarn(Z,0);
  setvalp(Z,1);
  for(i=1;i<=g;i++) gel(Z,i+1) = gdiv(utoi(N[i]),utoi(i));
  Z = gexp(Z,0);
  Z = gmul(Z,deg1pol_shallow(gen_1,gen_m1,0));
  Z = gmul(Z,deg1pol_shallow(utoi(p),gen_m1,0));
  L = cgetg(2*g+3,t_POL);
  L[1] = 0;
  setvarn(L,0);
  setsigne(L,1);
  gel(L,2*g+2) = gen_1;
  for(i=1;i<=g;i++) gel(L,2*g+2-i) = gel(Z,i+2);
  Pi = gen_1;
  for(i=1;i<=g;i++)
  {
    Pi = muliu(Pi,p);
    gel(L,g+2-i) = mulii(gel(L,g+2+i),Pi);
  }
  return gerepilecopy(av,L);
}

ulong
CrvZeta_loc(GEN f, GEN BadU, GEN T, ulong p, GEN u1, GEN s, ulong r, ulong l)
{ /* q-1 = (p-1)*r
     Fq* = Z/(q-1) ->> Z/(p-1), work in fibre u1*<s>, s=g^(p-1), u1 = g^l */
  // TODO f FlxX, BadU Flx
  pari_sp av = avma, av1;
  GEN u,fu,done;
  ulong n,m,i,i1;
  n = 0;
  u = u1;
  done = cgetg(r+1,t_VECSMALL);
  for(i=1;i<=r;i++)
    done[i] = 0;
  av1 = avma;
  for(i=1;i<=r;i++)
  {
    u = Flxq_mul(u,s,T,p);
    if(gc_needed(av1,3)) u = gerepileupto(av1,u);
    if(done[i])
      continue;
    m = 0;
    if(lgpol(Flx_Flxq_eval(BadU,u,T,p))==0)
    {
      //pari_printf("u=%Ps is a root of BadU=%Ps\n",Flx_to_ZX(u),Flx_to_ZX(BadU));
      continue;
    }
    fu = FlxY_Flxq_evalx(f,u,T,p);
    m = FlxqX_nbroots(fu,T,p);
    //pari_printf("At x=%Ps, fu=%Ps -> %lu\n",Flx_to_ZX(u),FlxX_to_ZXX(fu),m);
    i1 = i;
    while(done[i1]==0)
    {
      done[i1]=1;
      n += m;
      i1 = (i1*p+l)%r;
      if(i1==0) i1=r;
    }
  }
  //pari_printf("Done: %Ps\n",done);
  avma = av;
  return n;
}

