#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_pic

/* Modular curves */

/* Z/NZ */

ulong
ZNnorm(long x, ulong N)
{ /* Z/NZ <-> {1,..,N} */
  x = umodsu(x,N);
  return x?x:N;
}

ulong
ZNneg(long x, ulong N)
{
  ulong y;
  y = umodsu(x,N);
  return y?N-y:N;
}

long
zM_coef_mod(GEN A, GEN v)
{
  ulong N,i,j;
  N = lg(A)-1;
  i = umodsu(v[1],N);
  j = umodsu(v[2],N);
  return gel(A,j?j:N)[i?i:N];
}

GEN
RgM_Coef_mod(GEN A, GEN v)
{
  ulong N,i,j;
  N = lg(A)-1;
  i = umodsu(v[1],N);
  j = umodsu(v[2],N);
  return gcoeff(A,i?i:N,j?j:N);
}


GEN
znx_span(GEN S, ulong N)
{ /* Span of vecsmall S in (Z/NZ)* */
  pari_sp av = avma;
  GEN S1,H1,charf,H;
  ulong nS,s,n1,n,i,j,h;
  /* Trivial case */
  if(lg(S)==1)
    return mkvecsmall(1);
  nS = lg(S)-1;
  s = umodsu(S[nS],N);
  S1 = gcopy(S);
  setlg(S1,nS); /* Drop last */
  H1 = znx_span(S1,N); /* Recurse */
  n1 = lg(H1);
  charf = cgetg(N+1,t_VECSMALL);
  for(i=1;i<=N;i++) charf[i]=0;
  n = 0;
  for(i=1;i<n1;i++)
  {
    h = H1[i];
    while(charf[h]==0)
    {
      charf[h] = 1;
      n++;
      h = Fl_mul(h,s,N);
    }
  }
  H = cgetg(n+1,t_VECSMALL);
  j = 1;
  for(i=1;i<=N;i++)
  {
    if(charf[i])
      H[j++] = i;
  }
  return gerepileupto(av,H);
}

ulong
VecSmallFind(GEN V, long x)
{
  /* Index between a and A */
  ulong a,A,c;
  long y;
  a=1;
  A = lg(V)-1;
  while(A-a>1)
  {
    c = (a+A)/2;
    y = V[c];
    if(y==x) return c;
    if(y<x) a = c;
    if(y>x) A = c;
  }
  for(c=a;c<=A;c++)
  {
    if(V[c]==x) return c;
  }
  return 0;
}

ulong
VecSmallFind_unsorted(GEN V, long x)
{
  ulong n,c;
  n = lg(V);
  for(c=1;c<n;c++)
  {
    if(V[c]==x) return c;
  }
  return 0;
}

GEN
znx_Hlist(GEN S, ulong N)
{ /* H = <S,-1> and H/+-1 */
  /* S=0: (Z/NZ)*. S=1: +-1. */
  pari_sp av = avma;
  GEN H,H1,S1;
  ulong i,j,nS,nH;
  if(N<=2)
  {
    H = cgetg(3,t_VEC);
    gel(H,1) = mkvecsmall(1);
    gel(H,2) = mkvecsmall(1);
    return H;
  }
  if(gequal1(S))
  {
    H = cgetg(3,t_VEC);
    gel(H,1) = mkvecsmall2(1,N-1);
    gel(H,2) = mkvecsmall(1);
    return H;
  }
  if(gequal0(S))
  {
    j = 1;
    H = cgetg(N+1,t_VECSMALL);
    for(i=1;i<=N;i++)
    {
      if(ugcd(i,N)==1)
        H[j++] = i;
    }
    setlg(H,j);
    nH = j;
  }
  else
  {
    nS = lg(S);
    S1 = cgetg(nS+1,t_VECSMALL); /* S and -1 */
    for(i=1;i<nS;i++)
      S1[i] = S[i];
    S1[nS] = -1;
    H = znx_span(S1,N);
    nH = lg(H);
  }
  H1 = cgetg(nH,t_VECSMALL);
  for(i=1;2*H[i]<=N;i++)
    H1[i] = H[i];
  setlg(H1,i);
  return gerepilecopy(av,mkvec2(H,H1));
}

/* GammaH(N) */

GEN
Flm2_Flm2_mul(GEN A, GEN B, ulong N)
{
  GEN A1,A2,B1,B2,C,C1,C2;
  A1 = gel(A,1);
  A2 = gel(A,2);
  B1 = gel(B,1);
  B2 = gel(B,2);
  C = cgetg(3,t_MAT);
  gel(C,1) = C1 = cgetg(3,t_VECSMALL);
  gel(C,2) = C2 = cgetg(3,t_VECSMALL);
  C1[1] = (A1[1]*B1[1]+A2[1]*B1[2])%N;
  C1[2] = (A1[2]*B1[1]+A2[2]*B1[2])%N;
  C2[1] = (A1[1]*B2[1]+A2[1]*B2[2])%N;
  C2[2] = (A1[2]*B2[1]+A2[2]*B2[2])%N;
  return C;
}

GEN
Flv2_Flm2_mul(GEN v, GEN A, ulong N)
{
  GEN A1,A2,w;
  A1 = gel(A,1);
  A2 = gel(A,2);
  w = cgetg(3,t_VECSMALL);
  w[1] = (v[1]*A1[1]+v[2]*A1[2])%N;
  w[2] = (v[1]*A2[1]+v[2]*A2[2])%N;
  return w;
}

GEN
Bot2SL2(GEN Bot, ulong N)
{ /* Finds Flm [*,*;c';d'] in SL2(Z/NZ) where Bot=[c,d] */
  GEN M,M1,M2;
  long c,d,g,u,v;
  M = cgetg(3,t_MAT);
  M1 = gel(M,1) = cgetg(3,t_VECSMALL);
  M2 = gel(M,2) = cgetg(3,t_VECSMALL);
  c = Bot[1];
  d = Bot[2];
  g = cbezout(c,d,&u,&v);
  g = Fl_inv(g,N);
  M1[1] = umodsu(v*g,N);
  M1[2] = umodsu(c,N);
  M2[1] = umodsu(-u*g,N);
  M2[2] = umodsu(d,N);
  return M;
}

GEN
ZNZ2primH(ulong N, GEN H)
{ /* Find all (u,v) s.t. gcd(u,v,N)=1 / H. Also returns maps for representatives */
  pari_sp av = avma;
  GEN A,tag;
  ulong nH,n,u,v,i,h;
  A = cgetg(N*N+1,t_VEC);
  n = 0;
  tag = cgetg(N+1,t_VEC);
  for(v=1;v<=N;v++)
  {
    gel(tag,v) = cgetg(N+1,t_VECSMALL);
    for(u=1;u<=N;u++)
      gel(tag,v)[u] = 0;
  }
  nH = lg(H);
  for(u=1;u<=N;u++)
  {
    for(v=1;v<=N;v++)
    {
      if(gel(tag,v)[u]) continue;
      if(ugcd(ugcd(u,v),N)>1) continue;
      n++;
      gel(A,n) = mkvecsmall2(u,v);
      for(i=1;i<nH;i++)
      {
        h = H[i];
        gel(tag,ZNnorm(h*v,N))[ZNnorm(h*u,N)] = n;
      }
    }
  }
  setlg(A,n+1);
  return gerepilecopy(av,mkvec2(A,tag));
}

static int
sort_lg_rev(void* data, GEN x, GEN y)
{
  (void)data;
  ulong lx,ly;
  lx = lg(x);
  ly = lg(y);
  if(lx==ly) return 0;
  if(lx<ly) return 1;
  return -1;
}

GEN
GammaHCusps(ulong N, GEN H)
{
  /* * Reps (c,d) of all cusps of GammaH
     * Galois orbits
     * Vector of bits: whether such that there is M = [*,*;c,d] in SL(2,Z/NZ) such that f|M has rat coefs for all f def/Q
     * Vector of Flm [*,*;c,d] in SL(2,Z/NZ), satifying above condition whenever bit=1
     * Galois orbits
     * Widths
     * Tags: (c',d') -> index of equivalent representative
  */
  pari_sp av = avma;
  ulong a,b,c,d,i,x,h,g,g2,w,nCusp,nH,nGalOrb,nOrb,N2,acg2;
  GEN Cusps,cd,CuspsGal,GalOrb,Qqexp,Mats,M,Widths,tag;
  N2 = N*N;
  Cusps = cgetg(N2+1,t_VEC);
  CuspsGal = cgetg(N2+1,t_VEC);
  Qqexp = cgetg(N2+1,t_VECSMALL);
  Mats = cgetg(N2+1,t_VEC);
  Widths = cgetg(N2+1,t_VECSMALL);
  tag = cgetg(N+1,t_VEC);
  for(d=1;d<=N;d++)
  {
    gel(tag,d) = cgetg(N+1,t_VECSMALL);
    for(c=1;c<=N;c++)
      gel(tag,d)[c] = 0;
  }
  nH = lg(H);
  nCusp = 0;
  nOrb = 1;
  for(c=0;c<N;c++) /* c in Z/NZ */
  {
    g = ugcd(c,N);
    g2 = N/ugcd(c*c,N);
    GalOrb = cgetg(N+1,t_VEC); /* Two cusps are Galois-conj iff. they have the same c mod H */
    nGalOrb = 1;
    for(d=0;d<g;d++)
    { /*d in (Z/gZ)* */
      if(ugcd(d,g)>1) continue;
      if(gel(tag,d?d:N)[c?c:N]) continue;
      /* Record cusp */
      gel(Cusps,++nCusp) = cd = mkvecsmall2(c,d);
      gel(GalOrb,nGalOrb++) = gcopy(cd);
      /* Mark equivalent cusps */
      for(x=0;x<N/g;x++)
      {
        for(i=1;i<nH;i++)
        {
          h = H[i];
          gel(tag,ZNnorm(h*d+x*g,N))[ZNnorm(h*c,N)] = nCusp;
        }
      }
      M = Bot2SL2(cd,N); /* [a,b;c,d] in SL2(Z/NZ), the other choices are M*[1,i;0,1]=[a,b+i*a;c,d+i*c] */
      /* Qqexp iff can choose i so that for all invertible x, cd(x-1)=0 & ad(x-1)+1 in H */
      gel(Mats,nCusp) = M;
      a = gel(M,1)[1];
      b = gel(M,2)[1];
      for(i=0;i<N;i++)
      {
        Qqexp[nCusp] = 1;
        for(x=2;x<N;x++)
        {
          if(ugcd(x,N)>1) continue;
          if( (c*d*(x-1))%N || VecSmallFind(H,(a*d*(x-1)+1)%N)==0 )
          {
            Qqexp[nCusp] = 0;
            break;
          }
        }
        if(Qqexp[nCusp])
        {
          break;
        }
        b += a;
        if(b>=N) b-=N;
        gel(M,2)[1] = b;
        d += c;
        if(d>=N) d-=N;
        gel(M,2)[2] = d;
      }
      /* Compute width: g2 * min w such that 1+acg2w in H */
      acg2 = (a*c*g2)%N;
      for(w=1;VecSmallFind(H,(1+acg2*w)%N)==0;w++) {}
      Widths[nCusp] = g2*w;
    }
    if(nGalOrb>1)
    { /* Record GalOrb if non-empty */
      setlg(GalOrb,nGalOrb);
      gel(CuspsGal,nOrb++) = GalOrb;
    }
  }
  nCusp++;
  setlg(Cusps,nCusp);
  setlg(Qqexp,nCusp);
  setlg(Mats,nCusp);
  setlg(Widths,nCusp);
  setlg(CuspsGal,nOrb);
  CuspsGal = gen_sort_shallow(CuspsGal,NULL,&sort_lg_rev);
  return gerepilecopy(av,mkvecn(6,Cusps,CuspsGal,Qqexp,Mats,Widths,tag));
}

GEN
GammaHCusps_GalDiam_orbits(long y, GEN Cusps, GEN CuspsGal, GEN tags)
{ /* Orbits of cusps under GalQ and <y> */
  pari_sp av = avma;
  GEN Diam,c,C;
  ulong m,n,i,j,k;
  n = lg(CuspsGal);
  Diam = cgetg(n,t_VECSMALL);
  for(i=1;i<n;i++)
  {
    Diam[i] = 0;
    c = gmael(CuspsGal,i,1); /* Take a cusp in orbit i */
    c = zv_z_mul(c,y); /* Apply <y> */
    c = gel(Cusps,zM_coef_mod(tags,c)); /* Normalised rep */
    /* Find its orbit */
    for(j=1;Diam[i]==0;j++)
    {
      C = gel(CuspsGal,j);
      m = lg(C);
      for(k=1;k<m;k++)
      {
        if(gequal(gel(C,k),c))
        {
          Diam[i] = j;
          break;
        }
      }
    }
  }
  /* Now Diam is the perm induced by <y> on CuspsGal */
  Diam = permcycles(Diam); /* Decomp into cycles */
  n = lg(Diam);
  for(i=1;i<n;i++)
  {
    m = lg(gel(Diam,i));
    C = cgetg(m,t_VEC);
    for(j=1;j<m;j++)
      gel(C,j) = gel(CuspsGal,gel(Diam,i)[j]);
    gel(Diam,i) = gconcat1(C);
  }
  return gerepilecopy(av,Diam);
}

GEN
GammaHmodN(ulong N, GEN H)
{ /* FlM reps of GammaH(N) / +-Gamma(N) */
  pari_sp av = avma;
  ulong nH,h,x,j;
  GEN G,Mh;
  nH = lg(H)-1;
  G = cgetg(nH*N+1,t_VEC);
  j = 1;
  Mh = cgetg(3,t_MAT);
  gel(Mh,1) = cgetg(3,t_VECSMALL);
  gel(Mh,2) = cgetg(3,t_VECSMALL);
  gel(Mh,1)[2] = 0;
  for(h=1;h<=nH;h++)
  {
    gel(Mh,1)[1] = H[h];
    gel(Mh,2)[2] = Fl_inv(H[h],N);
    for(x=0;x<N;x++)
    {
      gel(Mh,2)[1] = x;
      gel(G,j++) = gcopy(Mh);
    }
  }
  return gerepilecopy(av,G);
}

GEN
XH_decomp(ulong N, GEN H)
{ /* Returns list of [eps,S2(eps)], where H c Ker eps and dim S2(eps)>0 */
  pari_sp av = avma;
  GEN iN,N2chi,res,G,AllChi,chi,Gchi,VecChi,VecS,S;
  ulong d,i,j,n,nH,nChi;
  iN = utoi(N);
  N2chi = cgetg(4,t_VEC);
  gel(N2chi,1) = iN = utoi(N);
  gel(N2chi,2) = gen_2;
  res = cgetg(3,t_VEC);
  G = znstar0(iN,1);
  if(gequal0(H))
  { /* Gamma0 : only care about trivial character */
    setlg(N2chi,3);
    S = cgetg(2,t_VEC);
    gel(S,1) = mfinit(N2chi,1);
    d = MF_get_dim(gel(S,1));
    if(DEBUGLEVEL>=3) printf("XH_decomp: S2(Gamma0) has dim %lu\n",d);
    if(d)
    {
      gel(res,1) = cgetg(2,t_VEC);
      gmael(res,1,1) = mkvec2(G,gen_1);
      gel(res,2) = S;
    }
    else gel(res,1) = gel(res,2) = cgetg(1,t_VEC);
    return gerepileupto(av,res);
  }
  if(gequal1(H))
  { /* Gamma1 : consider all characters */
    H = NULL; /* Nothing needed in Ker */
    nH = 0;
  }
  else
    nH = lg(H);
  AllChi = chargalois(G,NULL);
  nChi = lg(AllChi);
  VecChi = cgetg(nChi,t_VEC);
  VecS = cgetg(nChi,t_VEC);
  n = 1;
  for(i=1;i<nChi;i++)
  { /* Loop over chi */
    chi = gel(AllChi,i);
    if(zncharisodd(G,chi)) continue;
    for(j=1;j<nH;j++)
    {
      if(!gequal0(chareval(G,chi,stoi(H[j]),NULL)))
      {
        if(DEBUGLEVEL>=2) pari_printf("XH_decomp: Dropping chi=%Ps because %lu not in Ker\n",chi,H[j]);
        chi = NULL;
        break;
      }
    }
    if(chi==NULL) continue;
    gel(N2chi,3) = Gchi = mkvec2(G,chi);
    /*d = mfcuspdim(N,2,Gchi); */
    S = mfinit(N2chi,1);
    d = MF_get_dim(S);
    if(DEBUGLEVEL>=3) pari_printf("XH_decomp: For chi=%Ps, dim S2(chi)=%lu\n",chi,d);
    if(d==0)
    {
      if(DEBUGLEVEL>=2) pari_printf("XH_decomp: Dropping chi=%Ps because dim S2(chi)=0\n",chi);
      continue;
    }
    gel(VecChi,n) = Gchi;
    gel(VecS,n++) = S;
  }
  setlg(VecChi,n);
  setlg(VecS,n);
  gel(res,1) = VecChi;
  gel(res,2) = VecS;
  return gerepilecopy(av,res);
}

/* LMod */

GEN
LMod_worker(GEN p, GEN Gchi, GEN S, long t, GEN Z, GEN zo, GEN MZ)
{
  pari_sp av = avma;
  GEN epsp,L1,Tp,Xp,res;
  epsp = chareval(gel(Gchi,1),gel(Gchi,2),p,zo);
  L1 = deg2pol_shallow(gen_1,gneg(pol_x(1)),gmul(p,epsp),0); /* x^2-y*x+p*eps(p)(t) */
  Tp = mfheckemat(S,p); /* coeffs in Q(t mod Z) */
  Xp = charpoly(Tp,1); /* in Q(t mod Z)[y] */
  Tp = matconcat(gsubst(liftpol(Tp),t,MZ));
  L1 = polresultant0(Xp,L1,1,0); /* Res_y(Xp(y),L1(x,y)) in Q(t mod Z)[x] */
  L1 = liftpol(L1); /* In Q[x,t] */
  res = cgetg(3,t_VEC);
  gel(res,1) = ZX_ZXY_resultant(Z,L1);
  gel(res,2) = RgM_Frobenius(Tp,0,NULL,NULL); /* Canonical form ensures integer coeffs, TODO slow in large dim */
  return gerepileupto(av,res);
}

GEN
ModCrv_charpoly_multi(ulong N, GEN H, GEN Vecp)
{
  pari_sp av = avma;
  GEN L,XH,VecChi,VecS,chi,S,o,Z,z,worker,Params,done,Psort;
  ulong np,nChi,i;
  long t,j,pending,workid;
  struct pari_mt pt;
  XH = XH_decomp(N,H);
  VecChi = gel(XH,1);
  VecS = gel(XH,2);
  nChi = lg(VecChi);
  np = lg(Vecp);
  L = cgetg(np,t_VEC);
  for(i=1;i<np;i++) gel(L,i) = mkvec2(pol_1(0),cgetg(nChi,t_VEC));
  if(nChi==1) /* Genus 0 */
    return gerepileupto(av,L);
  Psort = indexsort(Vecp);
  Params = cgetg(8,t_VEC);
  for(i=1;i<nChi;i++)
  {
    gel(Params,2) = chi = gel(VecChi,i);
    gel(Params,3) = S = gel(VecS,i);
    t = variables_vecsmall(S)[2];
    gel(Params,4) = stoi(t);
    o = charorder0(gel(chi,1),gel(chi,2));
    gel(Params,5) = Z = polcyclo(itou(o),t);
    z = pol_x(t);
    gel(Params,6) = mkvec2(gmodulo(z,Z),o);
    gel(Params,7) = matcompanion(Z);
    worker = strtofunction("_LMod_worker");
    mt_queue_start_lim(&pt,worker,np-1);
    for(j=np-1;j>0||pending;j--)
    {
      if(j>0)
      {
        gel(Params,1) = gel(Vecp,Psort[j]);
        mt_queue_submit(&pt,Psort[j],Params);
      }
      else
        mt_queue_submit(&pt,j,NULL);
      done = mt_queue_get(&pt,&workid,&pending);
      if(done)
      {
        gmael(L,workid,1) = ZX_mul(gmael(L,workid,1),gel(done,1));
        gmael3(L,workid,2,i) = gel(done,2);
      }
    }
    mt_queue_end(&pt);
  }
  return gerepilecopy(av,L);
}

/* Etors */

GEN
elladd_padic(GEN a4, GEN P, GEN Q, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma, av0;
  GEN P0,xP,yP,xQ,yQ,dx,dy,l,m,xR,yR,R;

  P0 = mkvec(gen_0); /* [0] */
  av0 = avma;
  if(gequal(P,P0))
  {
    set_avma(av);
    return Q;
  }
  if(gequal(Q,P0))
  {
    set_avma(av);
    return P;
  }
  xP = gel(P,1);
  yP = gel(P,2);
  xQ = gel(Q,1);
  yQ = gel(Q,2);
  if(gequal(FpX_red(xP,p),FpX_red(xQ,p)))
  {
    /* Dangerous case */
    if(gequal(FpX_red(xP,pe),FpX_red(xQ,pe))==0)
      pari_err(e_IMPL,"case P!=Q but P=Q mod p");
    if(gequal0(FpX_red(ZX_add(yP,yQ),pe)))
    {
      set_avma(av0);
      return P0;
    }
    dx = ZX_Z_mul(yP,gen_2);
    dy = Fq_sqr(xP,T,pe);
    dy = ZX_Z_mul(dy,utoi(3));
    dy = gadd(dy,a4);
  }
  else
  {
    dx = ZX_sub(xQ,xP);
    dy = ZX_sub(yQ,yP);
  }
  l = ZpXQ_div(dy,dx,T,pe,p,e);
  m = Fq_mul(l,xP,T,pe);
  m = ZX_sub(yP,m);
  xR = ZX_add(xP,xQ);
  xR = FpX_sub(Fq_sqr(l,T,pe),xR,pe);
  yR = Fq_mul(l,xR,T,pe);
  yR = ZX_add(yR,m);
  yR = FpX_neg(yR,pe);
  R = mkvec2(xR,yR);
  return gerepilecopy(av,R);
}

GEN
FpEll_y2_from_Fqx(GEN a4, GEN a6, GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN y;
  y = Fq_sqr(x,T,p); // x^2
  y = ZX_Z_add(y,a4); // x^2+a4
  y = Fq_mul(y,x,T,p); // x^3+a4*x
  y = ZX_Z_add(y,a6); // x^3+a4*x+a6
  return gerepileupto(av,y);
}

ulong
FpX_split_deg(GEN F, GEN p)
{ /* Smallest d s.t. all roots in GF(p^d), i.e. x^p^d = x mod F */
  pari_sp av = avma;
  GEN x,y;
  ulong i;
  x = pol_x(varn(F));
  y = FpX_Frobenius(F,p);
  for(i=1;!gequal(y,x);i++)
    y = Fq_pow(y,p,F,p);
  return gc_ulong(av,i);
}

GEN
Fp_elldivpol_lv(GEN a4, GEN a6, ulong l, ulong v, GEN p)
{ /* pol whose roots are the x of the pts in E[l^v]-E[l^v-1] */
  pari_sp av = avma;
  GEN D,D1;
  if(l==2 && v==1)
  {
    D = mkpoln(4,gen_1,gen_0,a4,a6);
    return gerepilecopy(av,D);
  }
  D = Fp_elldivpol(a4,a6,upowuu(l,v),p);
  if(v==1) return D;
  D1 = Fp_elldivpol(a4,a6,upowuu(l,v-1),p);
  D = FpX_div(D,D1,p);
  return gerepileupto(av,D);
}

ulong
EllTorsIsSplit_lv(GEN a4, GEN a6, ulong l, ulong v, GEN p, ulong d, GEN T, GEN q2)
{ /* returns [Fp(E[l^v]/+-1):Fp] if E[l^v] defined over Fp^d, else returns 0 */
  pari_sp av = avma;
  GEN D,X,y;
  ulong r,nX,i;
  if(DEBUGLEVEL)
    printf("EllSplitTors: Using divpol to check whether E[%lu^%lu] defined in degree %lu.\n",l,v,d);
  D = Fp_elldivpol_lv(a4,a6,l,v,p);
  r = FpX_split_deg(D,p);
  if(d%r)
  {
    if(DEBUGLEVEL)
      printf("EllSplitTors: E[%lu^%lu] not defined in degree %lu.\n",l,v,d);
    return gc_ulong(av,0);
  }
  if(l!=2 || v>1)
  {
    X = FpXQX_roots(D,T,p);
    nX = lg(X);
    for(i=1;i<nX;i++)
    {
      y = FpEll_y2_from_Fqx(a4,a6,gel(X,i),T,p);
      y = Fq_pow(y,q2,T,p);
      if(!gequal1(y))
      {
        if(DEBUGLEVEL)
          printf("EllSplitTors: E[%lu^%lu] not split.\n",l,v);
        return gc_ulong(av,0);
      }
    }
  }
  return gc_ulong(av,r);
}

ulong
EllTorsIsSplit(GEN a4, GEN a6, ulong N, GEN p, ulong d, GEN T, GEN q, GEN q2)
{ /* returns [Fp(E[N]/+-1):Fp] if E[N] defined over Fp^d, else returns 0 */
  pari_sp av = avma;
  GEN ap,chiE,nu,nud,NE,g,fa;
  ulong M,l,v,pl,i,r,c,nfa;
  ap = subii(addiu(p,1),Fp_ellcard(a4,a6,p));
  chiE = deg2pol_shallow(gen_1,negi(ap),p,0); /* x^2-ap*x+p */
  nu = polsym(chiE,d);
  nud = gel(nu,d+1); /* alpha^d+beta^d */
  NE = subii(addiu(q,1),nud); /* #E(Fq) */
  if(umodiu(NE,N*N)) /* Must have N^2 | #E(Fq) */
    return gc_ulong(av,0);
  g = subii(sqri(ap),muliu(p,4)); /* ap^2-4p */
  fa = factoru(ugcdiu(g,N)); /* Primes l|N such that Frobp not ss on E[l] */
  nfa = lg(gel(fa,1));
  M = N;
  for(i=1;i<nfa;i++)
  {
    l = gel(fa,1)[i];
    gel(fa,2)[i] = v = u_lval(N,l); /* Set multiplicities of N */
    M /= upowuu(l,v);
    if(l==2) continue;
    if(DEBUGLEVEL) printf("EllSplitTors: Checking whether Frob^%lu unipotent on E[%lu].\n",d,l);
    if(Fl_powu(umodiu(ap,l),d,l) != Fl_powu(2,d,l))
    {
      if(DEBUGLEVEL) printf("EllSplitTors: Frob^%lu unipotent on E[%lu].\n",d,l);
      return gc_ulong(av,0);
    }
  }
  /* M = Cofactor supported by primes l such that Frobp ss on E[l] */
  if(M>1)
  {
    if(DEBUGLEVEL) printf("EllSplitTors: Checking whether Frob^%lu trivial on E[%lu].\n",d,M);
    if(umodiu(nud,M)!=(2%M))
    {
      if(DEBUGLEVEL) printf("EllSplitTors: Frob^%lu nontrivial on E[%lu].\n",d,M);
      return gc_ulong(av,0);
    }
  }
  /* So now Frob^d trivial on E[l] but maybe not E[l^v] for l good,
     and unipotent on E[l] but maybe not E[l^v] for l bad.
     We now check for each l if Frob^d trivial on E[l^v],
     and also determine the order of Frob on E[l^v]/-1. */
  /* TODO check l=2 */
  c = 1;
  for(i=1;i<nfa;i++)
  {
    l = gel(fa,1)[i];
    v = gel(fa,2)[i];
    r = EllTorsIsSplit_lv(a4,a6,l,v,p,d,T,q2);
    if(r==0)
      return gc_ulong(av,0);
    c = ulcm(c,r);
  }
  fa = factoru(M);
  nfa = lg(gel(fa,1));
  for(i=1;i<nfa;i++)
  {
    l = gel(fa,1)[i];
    v = gel(fa,2)[i];
    if(v==1)
    { /* We already know E[l^v] defined over Fp^d, but still need deg of E[l]/-1 */
      pl = umodiu(p,l);
      for(r=1;r<=d;r++)
      {
        if(Fl_sqr(umodiu(gel(nu,r+1),l),l)==(4%l) && Fl_powu(pl,r,l)==1)
        {
          c = ulcm(c,r);
          break;
        }
      }
    }
    else
    {
      r = EllTorsIsSplit_lv(a4,a6,l,v,p,d,T,q2);
      if(r==0)
       return gc_ulong(av,0);
      c = ulcm(c,r);
    }
  }
  return gc_ulong(av,c);
}

GEN
EllSplitTors(ulong N, GEN p, GEN T, GEN Badj)
{ /* Look for E/Fp such that E[N] def / Fp^d and j not in Badj */
  pari_sp av = avma, av1;
  ulong d,nBad,i,r,nwatch;
  GEN q,q2,a4,a6,D,j;
  d = degpol(T);
  if(Fl_powu(umodiu(p,N),d,N)!=1)
    pari_err(e_MISC,"Impossible by Weil pairing");
  nBad = lg(Badj);
  q = powiu(p,d);
  q2 = subiu(q,1);
  q2 = shifti(q2,-1);
  av1 = avma;
  for(nwatch=1;nwatch<1000;nwatch++) /* TODO adjust */
  {
    set_avma(av1);
    if(DEBUGLEVEL>=2) printf("EllSplitTors: Trying new curve.\n");
    a4 = genrand(p);
    if(gequal0(a4)) continue; /* Avoid j=0 */
    a6 = genrand(p);
    if(gequal0(a6)) continue; /* Avoid j=1728 */
    D = Fp_powu(a4,3,p);
    D = muliu(D,4);
    D = Fp_add(D,muliu(Fp_sqr(a6,p),27),p);
    if(gequal0(D)) continue; /* Singular curve */
    j = Fp_ellj(a4,a6,p);
    for(i=1;i<nBad;i++)
    {
      if(gequal(gel(Badj,i),j))
      {
        if(DEBUGLEVEL>=2) printf("EllSplitTors: Got one of the forbidden j.\n");
        a4 = a6 = NULL;
        break;
      }
    }
    if(a4==NULL) continue;
    r = EllTorsIsSplit(a4,a6,N,p,d,T,q,q2);
    if(r==d)
      return gerepilecopy(av,mkvec3(a4,a6,j));
    if(DEBUGLEVEL>=2)
    {
      if(r==0) printf("EllSplitTors: Unsuitable curve.\n");
      else printf("EllSplitTors: E[%lu]/-1 defined in degree %lu<%lu.\n",N,r,d);
    }
  }
  if(DEBUGLEVEL)
    printf("EllSplitTors: Unable to find suitable elliptic curve after %lu attempts, giving up.\n",nwatch);
  return NULL;
}

GEN
EllTorsBasis_lv(GEN a4, GEN a6, GEN A4, ulong l, ulong v, GEN T, GEN p, GEN D)
{ /* l,v -> Basis [P,Q] of E[l^v] over Fq, plus its Weil pairing, and mat of Frob */
  pari_sp av = avma;
  GEN lv1,lv,X,P,Q,x,z,z1,FP,FQ,M;
  ulong nX,iP,iQ;
  if(DEBUGLEVEL) printf("EllTorsBasis_lv: Getting basis of E[%lu^%lu]\n",l,v);
  lv1 = powuu(l,v-1);
  lv = muliu(lv1,l);
  X = FpXQX_roots(D,T,p);
  nX = lg(X)-1;
  P = cgetg(3,t_VEC);
  Q = cgetg(3,t_VEC);
  FP = cgetg(3,t_VEC);
  FQ = cgetg(3,t_VEC);
  for(;;)
  {
    iP = random_Fl(nX);
    do {iQ = random_Fl(nX);} while(iQ==iP);
    gel(P,1) = x = gel(X,iP+1);
    gel(P,2) = Fq_sqrt(FpEll_y2_from_Fqx(a4,a6,x,T,p),T,p);
    gel(Q,1) = x = gel(X,iQ+1);
    gel(Q,2) = Fq_sqrt(FpEll_y2_from_Fqx(a4,a6,x,T,p),T,p);
    z = FpXQE_weilpairing(P,Q,lv,A4,T,p);
    if(!gequal1(Fq_pow(z,lv1,T,p))) break;
  }
  z1 = Fq_inv(z,T,p);
  gel(FP,1) = Fq_pow(gel(P,1),p,T,p);
  gel(FP,2) = Fq_pow(gel(P,2),p,T,p);
  gel(FQ,1) = Fq_pow(gel(Q,1),p,T,p);
  gel(FQ,2) = Fq_pow(gel(Q,2),p,T,p);
  M = cgetg(3,t_MAT);
  gel(M,1) = cgetg(3,t_COL);
  gel(M,2) = cgetg(3,t_COL);
  gcoeff(M,1,1) = Fq_log(FpXQE_weilpairing(FP,Q,lv,A4,T,p),z,lv,T,p);
  gcoeff(M,2,1) = Fq_log(FpXQE_weilpairing(FP,P,lv,A4,T,p),z1,lv,T,p);
  gcoeff(M,1,2) = Fq_log(FpXQE_weilpairing(FQ,Q,lv,A4,T,p),z,lv,T,p);
  gcoeff(M,2,2) = Fq_log(FpXQE_weilpairing(FQ,P,lv,A4,T,p),z1,lv,T,p);
  return gerepilecopy(av,mkvecn(4,P,Q,z1,gmodulo(M,lv)));
}

GEN
ZqE_LiftTorsPt(GEN a4, GEN a6, GEN P, GEN D, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma;
  GEN x,y,y2;
  x = gel(P,1);
  y = gel(P,2);
  x = ZpX_ZpXQ_liftroot(D,x,T,p,e);
  y2 = FpEll_y2_from_Fqx(a4,a6,x,T,pe);
  y = gequal0(FpX_red(y2,pe)) ? gen_0 : ZpXQ_sqrtnlift(y2,gen_2,y,T,p,e);
  return gerepilecopy(av,mkvec2(x,y));
}

GEN
EllWithTorsBasis(ulong N, GEN T, GEN pe, GEN p, long e, GEN Badj)
{ /* Find a4,a6 s.t. E[N] def/Fq and Fp(E[N]/-)=Fq. Returns a4,a6,P,Q,eN(P,Q),MFrob mod p^e. */
  pari_sp av = avma;
  GEN Fq1,E,a4,a6,A4,P,Q,z,faN,M,D,B,Pi,Qi,zi;
  ulong nfaN,i,l,v,lv1,lv;
  E = EllSplitTors(N,p,T,Badj);
  if(E==NULL) /* Couldn't find E, and giving up? */
    return gc_NULL(av);
  a4 = gel(E,1);
  a6 = gel(E,2);
  A4 = scalarpol(a4,varn(T));
  P = Q = mkvec(gen_0);
  z = Fq1 = pol_1(varn(T));
  faN = factoru(N);
  nfaN = lg(gel(faN,1));
  M = cgetg(nfaN,t_VEC);
  for(i=1;i<nfaN;i++)
  {
    l = gel(faN,1)[i];
    v = gel(faN,2)[i];
    lv1 = upowuu(l,v-1);
    lv = lv1*l;
    D = Fp_elldivpol_lv(a4,a6,l,v,pe);
    B = EllTorsBasis_lv(a4,a6,A4,l,v,T,p,D);
    Pi = ZqE_LiftTorsPt(a4,a6,gel(B,1),D,T,pe,p,e);
    P = elladd_padic(a4,P,Pi,T,pe,p,e);
    Qi = ZqE_LiftTorsPt(a4,a6,gel(B,2),D,T,pe,p,e);
    Q = elladd_padic(a4,Q,Qi,T,pe,p,e);
    zi = gel(B,3);
    zi = Fq_powu(zi,N/lv,T,p);
    zi = ZpXQ_sqrtnlift(Fq1,utoi(lv),zi,T,p,e);
    z = Fq_mul(z,zi,T,pe);
    gel(M,i) = gel(B,4);
  }
  M = liftint(chinese1(M));
  return gerepilecopy(av,mkvecn(5,E,P,Q,z,M));
}

GEN
Ell_l2(GEN EN, GEN a4, GEN P, GEN Q, GEN T, GEN pe, GEN p, long e)
{ /* Not mem clean */
  ulong N;
  if(P==Q) /* Tangent? */
  {
    N = lg(EN)-1;
    if(umodsu(3*P[1],N)==0 && umodsu(3*P[2],N)==0) /* Flex? */
    {
      P = RgM_Coef_mod(EN,P);
      return ZpXQ_div(ZX_Z_add(ZX_Z_mul(ZX_sqr(gel(P,1)),utoi(3)),a4),ZX_Z_mul(gel(P,2),gen_2),T,pe,p,e);
    }
    Q = mkvecsmall2(-P[1]-Q[1],-P[2]-Q[2]);
  }
  P = RgM_Coef_mod(EN,P);
  Q = RgM_Coef_mod(EN,Q);
  return ZpXQ_div(ZX_sub(gel(Q,2),gel(P,2)),ZX_sub(gel(Q,1),gel(P,1)),T,pe,p,e);
}

GEN
Ell_l1_c(GEN EN, GEN a4, GEN P, ulong m, GEN T, GEN pe, GEN p, long e)
{
  /* Not mem clean */
  GEN c,mP;
  if(m==1) return gen_0;
  if(m&1)
  {
    m--;
    c = Ell_l1_c(EN,a4,P,m,T,pe,p,e);
    mP = zv_z_mul(P,m);
    c = ZX_add(c,Ell_l2(EN,a4,mP,P,T,pe,p,e));
  }
  else
  {
    m>>=1;
    c = Ell_l1_c(EN,a4,P,m,T,pe,p,e);
    mP = zv_z_mul(P,m);
    c = ZX_add(ZX_Z_mul(c,gen_2),Ell_l2(EN,a4,mP,mP,T,pe,p,e));
  }
  return c;
}

GEN
Ell_l1(GEN EN, GEN a4, GEN P, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma;
  ulong N,g,o;
  GEN c;
  N = lg(EN)-1;
  g = ugcd(ugcd(N,P[1]),P[2]);
  o = N/g;
  c = Ell_l1_c(EN,a4,P,o-1,T,pe,p,e);
  c = ZX_Z_mul(c,utoi(g));
  c = FpX_red(c,pe);
  return gerepileupto(av,c);
}

GEN
Ell_FillTors_worker(GEN Axes, GEN a4, ulong y, GEN T, GEN pe, GEN p, long e)
{
  GEN ENy;
  ulong N,x;
  N = lg(gel(Axes,1))-1;
  ENy =cgetg(N+1,t_COL);
  for(x=1;x<N;x++)
  {
    gel(ENy,x) = elladd_padic(a4,gmael(Axes,1,x),gmael(Axes,2,y),T,pe,p,e);
  }
  gel(ENy,N) = gcopy(gen_0);
  return ENy;
}

GEN
Ell_l1_worker(GEN EN, GEN a4, ulong y, GEN T, GEN pe, GEN p, long e)
{ /* t_COL l1(x,y) for x in Z/NZ */
  pari_sp av = avma;
  GEN P,L1y;
  ulong N,xmax,x;
  N = lg(EN)-1;
  P = mkvecsmall2(0,y);
  L1y = cgetg(N+1,t_COL);
  if(y==N)
  {
    xmax = N-1;
    gel(L1y,N) = gcopy(gen_0);
  }
  else
    xmax = N;
  for(x=1;x<=xmax;x++)
  {
    P[1] = x;
    gel(L1y,x) = Ell_l1(EN,a4,P,T,pe,p,e);
  }
  return gerepileupto(av,L1y);
}

GEN
EllMl1(GEN a4, ulong N, GEN P, GEN Q, ulong m, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma;
  GEN worker,done,E,Axes,ENx0,EN0y,EN,Ml1,params,INTs;
  ulong x,y;
  long pending,workid;
  struct pari_mt pt;
  E = stoi(e);
  /* Write down all N-torsion: this is a naive level structure alpha : (Z/NZ)^2 ~ E[N] */
  EN = cgetg(N+1,t_MAT); /* [ m*i*P + j*Q ] */
  Axes = cgetg(3,t_VEC);
  gel(Axes,1) = ENx0 = cgetg(N+1,t_COL);
  gel(Axes,2) = EN0y = cgetg(N+1,t_VEC);
  gel(ENx0,N) = gel(EN0y,N) = gen_0;
  gel(ENx0,m) = P;
  gel(EN0y,1) = Q;
  /* Axes */
  for(x=2;x<N;x++)
  {
    gel(ENx0,ZNnorm(m*x,N)) = elladd_padic(a4,gel(ENx0,ZNnorm(m*(x-1),N)),P,T,pe,p,e);
    gel(EN0y,x) = elladd_padic(a4,gel(EN0y,x-1),Q,T,pe,p,e);
  }
  /* The rest */
  params = cgetg(8,t_VEC);
  gel(params,1) = Axes;
  gel(params,2) = a4;
  gel(params,4) = T;
  gel(params,5) = pe;
  gel(params,6) = p;
  gel(params,7) = E;
  INTs = cgetg(N+1,t_VEC);
  worker = strtofunction("_Ell_FillTors_worker");
  mt_queue_start_lim(&pt,worker,N-1);
  pending = 0;
  for(y=1;y<N||pending;y++)
  {
    if(y<N)
    {
      gel(params,3) = gel(INTs,y) = utoi(y);
      mt_queue_submit(&pt,y,params);
    }
    else mt_queue_submit(&pt,0,NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done)
    {
      gel(EN,workid) = done;
      gcoeff(EN,N,workid) = gel(EN0y,workid);
    }
  }
  mt_queue_end(&pt);
  gel(EN,N) = ENx0;
  gel(INTs,N) = utoi(N);
  /* Ml1 */
  gel(params,1) = EN;
  worker = strtofunction("_Ell_l1_worker");
  mt_queue_start_lim(&pt,worker,N);
  Ml1 = cgetg(N+1,t_MAT);
  for(y=1;y<=N||pending;y++)
  {
    if(y<=N)
    {
        gel(params,3) = gel(INTs,y);
        mt_queue_submit(&pt,y,params);
    }
    else mt_queue_submit(&pt,0,NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done)
      gel(Ml1,workid) = done;
  }
  mt_queue_end(&pt);
  return gerepileupto(av,Ml1);
}

GEN
GetMl1(ulong N, GEN Pts, GEN PtTags, GEN T, GEN p, long e, GEN zNpref_pows, GEN Badj)
{
  pari_sp av = avma;
  GEN pe,E,a4,P,Q,zN,M,Ml1,FP,PtsFrob;
  ulong m,nPts,i,a,b,c,d,x,y;
  pe = powis(p,e);
  E = EllWithTorsBasis(N,T,pe,p,e,Badj);
  if(E==NULL) /* Couldn't find E, and giving up? */
    return gc_NULL(av);
  a4 = gmael(E,1,1);
  P = gel(E,2);
  Q = gel(E,3);
  zN = gel(E,4);
  M = gel(E,5);
  /* Frob acts on E[N] by [a,c;b,d]
   * => on pts, Frob([x,y]) = [x,y]*[a,b;c,d] = [a*x + c*y, b*x + d*y] */
  a = itou(gcoeff(M,1,1));
  b = itou(gcoeff(M,2,1));
  c = itou(gcoeff(M,1,2));
  d = itou(gcoeff(M,2,2));
  if(zNpref_pows)
  {
    for(m=1;;m++)
      if(gequal(zN,gel(zNpref_pows,m))) break;
    c = Fl_mul(c,m,N);
    b = Fl_div(b,m,N);
    zN = gen_0;
  }
  else m=1;
  Ml1 = EllMl1(a4,N,P,Q,m,T,pe,p,e);
  nPts = lg(Pts);
  PtsFrob = cgetg(nPts,t_VECSMALL);
  for(i=1;i<nPts;i++)
  {
    P = gel(Pts,i);
    x = P[1];
    y = P[2];
    FP = mkvecsmall2(a*x + c*y, b*x + d*y);
    PtsFrob[i] = zM_coef_mod(PtTags,FP);
  }
  return gerepilecopy(av,mkvecn(4,gel(E,1),Ml1,PtsFrob,zN));
}

/* Divisors */

GEN
BalancedDiv(ulong d, GEN degs)
{ /* Let degs = [a1,..,an]. Find balanced b1,..,bn such that sum ai*bi = d. Loops forever if no solution! */
  GEN D;
  ulong n,i;
  long s,q,r;
  n = lg(degs);
  D = cgetg(n,t_VECSMALL);
  s = zv_sum(degs);
  q = sdivss_rem(d,s,&r);
  for(i=1;i<n;i++) D[i] = q;
  while(r)
  {
    for(i=1;i<n && r;i++)
    {
      if(degs[i]<=r)
      {
        r -= degs[i];
        D[i]++;
      }
    }
  }
  return D;
}

GEN
BalancedDivInf(ulong d, GEN degs)
{ /* TODO sort/improve Let degs = [a1,..,an]. Find balanced b1,..,bn such that sum ai*bi <= d, not too far. */
  GEN D;
  ulong n,i;
  long s,q,r;
  n = lg(degs);
  D = cgetg(n,t_VECSMALL);
  s = zv_sum(degs);
  q = sdivss_rem(d,s,&r);
  for(i=1;i<n;i++)
  {
    D[i] = q;
    if(degs[i]<=r)
    {
      r -= degs[i];
      D[i]++;
    }
  }
  return D;
}

GEN
DivPerturb(GEN D, GEN degs)
{ /* TODO improve */
  GEN D2;
  ulong n,i,d;
  n = lg(D);
  d = 0;
  for(i=1;i<n;i++)
    d += D[i]*degs[i];
  D2 = BalancedDiv(d-1,degs);
  for(i=n-1;i&&degs[i]==1;i--)
  {
    if(D2[i]+1 != D[i])
    {
      D2[i]++;
      return D2;
    }
  }
  pari_err(e_MISC,"I do not know how to pertub this divisor (code needs to be improved)");
  return NULL;
}

GEN
Divo2Div(GEN Do, GEN Orbs, GEN tags, ulong n)
{
  GEN D,o;
  ulong nO,no,i,j;
  nO = lg(Orbs);
  D = cgetg(n+1,t_VECSMALL);
  for(i=1;i<nO;i++)
  {
    o = gel(Orbs,i);
    no = lg(o);
    for(j=1;j<no;j++)
    {
      D[zM_coef_mod(tags,gel(o,j))] = Do[i];
    }
  }
  return D;
}

GEN
MRRsubspace(GEN Mqexps, GEN D, GEN B, GEN T, GEN pe, GEN p, long e)
{ /* Subspace of mf defined by vanishing orders at cusps */
  pari_sp av=avma;
  GEN K,Ms;
  ulong nD,nCusps,nM,i,j,n,s;
  nD = zv_sum(D)+1;
  nCusps = lg(D);
  nM = lg(gel(Mqexps,1));
  K =  cgetg(nM,t_MAT);
  for(j=1;j<nM;j++)
    gel(K,j) = cgetg(nD,t_COL);
  for(i=s=1;s<nCusps;s++)
  {
    Ms = gel(Mqexps,s);
    for(n=1;n<=D[s];n++,i++)
    {
      for(j=1;j<nM;j++)
        gcoeff(K,i,j) = gcoeff(Ms,B?n+B[s]:n,j);
    }
  }
  K = matkerpadic(K,T,pe,p,e);
  return gerepileupto(av,K);
}

/* permutations */
/* TODO some functions probably have terrible complexity, better algos certainly possible */

GEN
PermConcat(GEN s, GEN t)
{
  GEN st;
  ulong n,m,i;
  n = lg(s)-1;
  m = lg(t);
  st = cgetg(n+m,t_VECSMALL);
  for(i=1;i<n+m;i++)
    st[i] = i<=n?s[i]:t[i-n]+n;
  return st;
}

GEN
Perms_orbits_ind(GEN S)
{ /* Perms S=[s[i]] acting on 1..N -> orbits, perms induced on these orbits, and size of thse orbits */
  pari_sp av = avma;
  GEN Orbs,SOrbs,lOrbs,Orb,SOrb,SOrbi,seen;
  ulong nS,N,nOrbs,nOrb,i,j,m,n,iseen,P,find;
  nS = lg(S);
  N = lg(gel(S,1))-1;
  seen = cgetg(N+1,t_VECSMALL); /* Bits: visited points */
  for(n=1;n<=N;n++)
    seen[n] = 0;
  Orbs = cgetg(N+1,t_VEC); /* Orbits */
  SOrbs = cgetg(N+1,t_VEC); /* Perms induced on orbits */
  lOrbs = cgetg(N+1,t_VECSMALL); /* Length of orbits */
  nOrbs = 0; /* #Orbits */
  for(iseen=0;iseen<=N;iseen++) /* Visit all points */
  {
    if(seen[iseen]) continue; /* Already visited? */
    P = iseen; /* No. Begin new orbit. */
    Orb = cgetg(N+1,t_VECSMALL);
    Orb[1] = P; /* For now, */
    nOrb = 1; /* It only contains this point. */
    setlg(Orb,nOrb+1);
    SOrb = cgetg(nS,t_VEC); /* Perms induced on this orbit */
    for(i=1;i<nS;i++)
    {
      gel(SOrb,i) = SOrbi = cgetg(N+1,t_VECSMALL);
      for(j=1;j<=N;j++) SOrbi[j] = 0; /* 0 marks unknown */
    }
    for(n=nOrb=1;n<=nOrb;n++) /* Move forward in orbit until we know what each perm does to each point */
    {
      for(i=1;i<nS;i++) /* for each perm */
      {
        SOrbi = gel(SOrb,i);
        if(SOrbi[n]==0) /* Do we know what this perm does to this point? */
        {
          m = n; /* No, let us see */
          P = Orb[n]; /* This point */
          for(;;)
          {
            P = gel(S,i)[P]; /* Image by this perm */
            seen[P] = 1; /* Mark this point as visited */
            find = VecSmallFind_unsorted(Orb,P); /* Is it already in Orb? */
            if(find)
            { /* Yes, in this position */
              SOrbi[m] = find; /* Record this info in perm */
              break;
            }
            /* It is not in Orb yet */
            Orb[++nOrb] = P; /* Add it */
            setlg(Orb,nOrb+1); /* Orb size increases */
            SOrbi[m] = nOrb; /* Record info in perm */
            m = nOrb; /* Now explore what happens to this new point */
          }
        }
      }
    }
    /* We have found a complete orbit */
    for(i=1;i<nS;i++) /* Adjust lengths of induced perms */
      setlg(gel(SOrb,i),nOrb+1);
    /* Record this orbit */
    gel(Orbs,++nOrbs) = Orb;
    gel(SOrbs,nOrbs) = SOrb;
    lOrbs[nOrbs] = nOrb;
  }
  /* Now we have found the orbits. */
  setlg(Orbs,nOrbs+1);
  setlg(SOrbs,nOrbs+1);
  setlg(lOrbs,nOrbs+1);
  return gerepilecopy(av,mkvec3(Orbs,SOrbs,lOrbs));
}

GEN
SubPerms_from_orbits_sup(ulong N, GEN Orbs, GEN SOrbs, GEN lOrbs, GEN I, ulong M)
{
  /* Perms of 1..N split into orbits -> -> [T,ST]
   T subset (possibly reordered) of 1..N stable under S and with #T<=M but close,
  ST perms induced by S on T */
  pari_sp av = avma;
  GEN Sub,SubS,Orb,SOrb;
  ulong nOrbs,nS,In,i,j,l,m,n;
  nOrbs = lg(Orbs)-1;
  nS = lg(gel(SOrbs,1));
  m = 0; /* Total size so far */
  Sub = cgetg(N+1,t_VECSMALL); /* Subset */
  SubS = cgetg(nS,t_VEC); /* Induced perms */
  for(i=1;i<nS;i++)
    gel(SubS,i) = cgetg(N+1,t_VECSMALL);
  /* From largest to smallest */
  for(n=nOrbs;n;n--)
  {
    In = I[n];
    Orb = gel(Orbs,In);
    SOrb = gel(SOrbs,In);
    l = lOrbs[In];
    if(m+l>M) continue; /* Does it fit? */
    for(j=1;j<=l;j++)
    {
      Sub[m+j] = Orb[j];
      for(i=1;i<nS;i++)
      {
        gel(SubS,i)[m+j] = gel(SOrb,i)[j]+m;
      }
    }
    m += l;
  }
  /* Adjust sizes */
  setlg(Sub,m+1);
  for(i=1;i<nS;i++)
    setlg(gel(SubS,i),m+1);
  return gerepilecopy(av,mkvec2(Sub,SubS));
}

GEN
SubPerms_inf(GEN S, ulong M)
{ /* Perms S=[s[i]] acting on 1..N, M<=N -> [T,ST]
   T subset (possibly reordered) of 1..N stable under S and with #T>=M but close,
  ST perms induced by S on T */
  pari_sp av = avma;
  GEN Orbs,SOrbs,lOrbs,Orb,SOrb,Sub,I;
  ulong N,nOrbs,i,j,l,m,n;
  N = lg(gel(S,1))-1;
  /* Get orbits */
  Orbs = Perms_orbits_ind(S);
  SOrbs = gel(Orbs,2);
  lOrbs = gel(Orbs,3);
  Orbs = gel(Orbs,1);
  nOrbs = lg(Orbs)-1;
  /* Shuffle them randomly */
  for(n=1;n<=nOrbs;n++)
  {
    i = 1 + random_Fl(nOrbs);
    j = 1 + random_Fl(nOrbs);
    if(i==j) continue;
    Orb = gel(Orbs,i);
    gel(Orbs,i) = gel(Orbs,j);
    gel(Orbs,j) = Orb;
    SOrb = gel(SOrbs,i);
    gel(SOrbs,i) = gel(SOrbs,j);
    gel(SOrbs,j) = SOrb;
    l = lOrbs[i];
    lOrbs[i] = lOrbs[j];
    lOrbs[j] = l;
  }
  I = vecsmall_indexsort(lOrbs);
  /* Attempt extracts */
  for(m=M;;m++)
  {
    Sub = SubPerms_from_orbits_sup(N,Orbs,SOrbs,lOrbs,I,m);
    if(lg(gel(Sub,1))>M) break;
  }
  return gerepileupto(av,Sub);
}

/* qexp */

GEN
E1qexp(GEN v, ulong N, GEN zpows, ulong B, GEN T, GEN pe, GEN p, long e)
{ /* v=[c,d] reduced mod N, zpows = powers of primitive Nth root of 1: q-exp of E_1^[c,d] up to O(qN^B) */
  /* TODO use t_SER ? */
  pari_sp av = avma;
  GEN E,Fq0,a0,zd;
  ulong a,b,c,d,m,n;

  if(B==0) return cgetg(1,t_VEC);
  c = v[1];
  d = v[2];
  Fq0 = pol_0(varn(T));
  E = cgetg(B+1,t_VEC);
  for(m=1;m<=B;m++) gel(E,m) = Fq0;

  if(c)
  { /* a0 = 1/2 - c/N */
    a0 = subii(Fp_inv(gen_2,pe),Fp_div(utoi(c),utoi(N),pe));
    a0 = scalarpol(a0,varn(T));
  }
  else
  { /* a0 = 1/2 * (1+z^d)/(1-z^d) */
    m = ZNnorm(d,N);
    zd = gel(zpows,m);
    a0 = ZpXQ_div(ZX_Z_add(zd,gen_1),ZX_Z_mul(Z_ZX_sub(gen_1,zd),gen_2),T,pe,p,e);
  }
  gel(E,1) = a0;

  /* sum_{a>0,b>0} if(a==c mod N, z^(b*d) * q^(a*b)) - if(a==-c mod N, z^(-b*d) * q^(a*b)) */
  for(a=(c==0?N:c);a<B;a+=N) /* Case a==c mod N */
  {
    for(b=1;(n=a*b+1)<=B;b++)
    {
      m = ZNnorm(b*d,N);
      gel(E,n) = ZX_add(gel(E,n),gel(zpows,m));
    }
  }
  for(a=N-c;a<B;a+=N) /* Case a==-c mod N */
  {
    for(b=1;(n=a*b+1)<=B;b++)
    {
      m = ZNneg(b*d,N);
      gel(E,n) = ZX_sub(gel(E,n),gel(zpows,m));
    }
  }

  return gerepilecopy(av,E);
}

GEN
TrE2qexp(GEN vw, ulong N, GEN TH, GEN M, ulong w, GEN zpows, ulong B, GEN T, GEN pe, GEN p, long e)
{ /* vw=[v,w] -> qexp of Tr_H(E_1^v * E_1^w) | M in terms of qw up to O(qw^B) */
  pari_sp av = avma;
  ulong Nw,Nwi,BN,nTH,h,i,j;
  GEN Fq0,E,hM,fv,fw;

  if(B==0) return cgetg(1,t_VEC);
  Nw = N/w;
  BN = (B-1)*N/w+1;

  Fq0 = pol_0(varn(T));
  E = cgetg(B+1,t_VEC);
  for(i=1;i<=B;i++) gel(E,i) = Fq0;

  nTH = lg(TH);
  for(h=1;h<nTH;h++)
  {
    hM = Flm2_Flm2_mul(gel(TH,h),M,N);
    fv = E1qexp(Flv2_Flm2_mul(gel(vw,1),hM,N),N,zpows,BN,T,pe,p,e);
    fw = E1qexp(Flv2_Flm2_mul(gel(vw,2),hM,N),N,zpows,BN,T,pe,p,e);
    /* TODO use fast series multiplication */
    /* f[i] = sum_j fv[j]*fw[Nw*i-j] */
    for(i=0;i<B;i++)
    {
      Nwi = Nw*i;
      for(j=0;j<=Nwi;j++)
        gel(E,i+1) = ZX_add(gel(E,i+1),Fq_mul(gel(fv,j+1),gel(fw,Nwi+1-j),T,pe));
    }
  }

  return gerepilecopy(av,E);
}

/* ModJac */

GEN
M2_worker(GEN vw, GEN Ml1, GEN TH, GEN Mpts, GEN T, GEN pe)
{
  pari_sp avs;
  ulong N, nZ, nTH;
  GEN v,w,C,Cs,M,vM,wM;
  ulong s,h;

  N = lg(Ml1)-1;
  nZ = lg(Mpts);
  nTH = lg(TH);
  v = gel(vw,1);
  w = gel(vw,2);

  C = cgetg(nZ,t_COL);
  for(s=1;s<nZ;s++)
  {
    avs = avma;
    Cs = pol_0(varn(T));
    for(h=1;h<nTH;h++)
    {
      M = Flm2_Flm2_mul(gel(TH,h),gel(Mpts,s),N);
      vM = Flv2_Flm2_mul(v,M,N);
      wM = Flv2_Flm2_mul(w,M,N);
      Cs = ZX_add(Cs,ZX_mul(RgM_Coef_mod(Ml1,vM),RgM_Coef_mod(Ml1,wM)));
    }
    Cs = Fq_red(Cs,T,pe);
    gel(C,s) = gerepileupto(avs,Cs);
  }
  return C;
}

GEN
M2mat(GEN M2gens, GEN Ml1, GEN TH, GEN MPts, GEN T, GEN pe)
{
  pari_sp av = avma;
  GEN M2;
  ulong d,j;
  struct pari_mt pt;
  GEN vFixedParams,worker,done;
  long pending,workid;

  d = lg(M2gens);
  vFixedParams = mkvecn(5,Ml1,TH,MPts,T,pe);
  worker = snm_closure(is_entry("_M2_worker"),vFixedParams);
  pending = 0;
  M2 = cgetg(d,t_MAT);
  mt_queue_start_lim(&pt,worker,d-1);
  for(j=1;j<d||pending;j++)
  {
    mt_queue_submit(&pt,j,j<d?mkvec(gel(M2gens,j)):NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done) gel(M2,workid) = done;
  }
  mt_queue_end(&pt);
  return gerepilecopy(av,M2);
}

GEN
FqCSer_mul(GEN A, GEN B, ulong n, GEN T, GEN p)
{ /* Multiplies t_COLS A,B of same length n+1 viewed as series A[1]*1+A[2]*x+..+A[n]*x^{n-1}+O(x^n) */
  /* TODO for now quadratic */
  pari_sp av;
  GEN C,Ck;
  ulong k,i;
  C = cgetg(n+1,t_COL);
  for(k=0;k<n;k++)
  {
    av = avma;
    Ck = ZX_mul(gel(A,k+1),gel(B,1));
    for(i=0;i<k;i++)
      Ck = ZX_add(Ck,ZX_mul(gel(A,i+1),gel(B,k+1-i)));
    Ck = Fq_red(Ck,T,p);
    gel(C,k+1) = gerepileupto(av,Ck);
  }
  return C;
}

GEN
M4qexp_worker(GEN pageV1, GEN V2gens, GEN U0, GEN T, GEN pe)
{
  pari_sp av = avma;
  GEN pageV2;
  ulong sprec,j,d;
  d = lg(V2gens);
  pageV1 = FqM_mul(pageV1,U0,T,pe);
  sprec = lg(gel(pageV1,1))-1;
  pageV2  = cgetg(d,t_MAT);
  for(j=1;j<d;j++)
    gel(pageV2,j) = FqCSer_mul(gel(pageV1,gel(V2gens,j)[1]),gel(pageV1,gel(V2gens,j)[2]),sprec,T,pe);
  return gerepileupto(av,pageV2);
}

GEN
ModPicInit(ulong N, GEN H, GEN p, ulong a, long e, GEN Lp, long UseTp, ulong nbE, ulong qprec)
{ /* J_H(N) over Zq/p^e, q=p^a */
  /* TODO sort cusps? */
  pari_sp av = avma, av1;
  long t;
  GEN J,T,pe,H1;
  GEN Cusps,CuspsGal,CuspsQexp,CuspsMats,CuspsWidths,CuspsTags,CuspsGalDegs,CuspsGalDiamp,CuspsGalDiampDegs;
  GEN Pts,PtsTags,MPts,PtsFrob,PtsDiamp,PtsDiamp0,PtsFrob0;
  GEN list_j,E,Ml1,zN,zNpows,TH,M2gens,geni,M2,B,M2qexps;
  GEN C0o,C0,C02,E1o,E1,E2o,E2,M,U0,M20,V1,V2,V3,V5,V,KV,EvalData,I,M4Q,V2qexps,V2gens,pageV2;
  ulong up,g,d0,nCusps,nCuspsGal,nCuspsGalDiamp,mQ,nZ,nPts,d,d1,nB,i,j,k,s,sprec;
  struct pari_mt pt;
  GEN worker,params,ie,done;
  long pending,workid;

  up = itou(p);
  J = cgetg(18,t_VEC);
  gel(J,1) = gen_0; /* No plane equation for curve */
  gel(J,4) = gel(J,15) = cgetg(1,t_VEC); /* No formula for RR spaces */
  gel(J,6) = p;
  /* Create unramified extension */
  t = fetch_var();
  name_var(t,"t");
  gel(J,5) = T = liftint(ffinit(p,a,t));
  gel(J,8) = pe = powis(p,e);
  gel(J,9) = ZpXQ_FrobMat(T,p,e,pe);
  gel(J,11) = V = cgetg(6,t_VEC);
  /* Get <H> */
  if(typ(H)==t_VEC) H = ZV_to_zv(H);
  H = znx_Hlist(H,N);
  H1 = gel(H,2); /* <H,-1>/-1 */
  H = gel(H,1); /* <H,-1> */
  if(dvdui(6*N*(lg(H1)-1),p))
    pari_err(e_MISC,"Use a prime p that does not divide 6*N*<H>");
  if(Lp==NULL || gequal0(Lp))
    Lp = gmael(ModCrv_charpoly_multi(N,H,mkvec(p)),1,1);
  gel(J,10) = Lp;
  g = degpol(Lp)/2;
  if(DEBUGLEVEL) printf("modpicinit: genus %lu\n",g);
  gel(J,2) = utoi(g);
  /* Get data about cusps */
  Cusps = GammaHCusps(N,H);
  CuspsGal = gel(Cusps,2);
  CuspsQexp = gel(Cusps,3);
  CuspsMats = gel(Cusps,4);
  CuspsWidths = gel(Cusps,5);
  CuspsTags = gel(Cusps,6);
  Cusps = gel(Cusps,1);
  nCusps = lg(Cusps)-1;
  if(nCusps<3)
    pari_err(e_IMPL,"the case where the number of cusps is < 3");
  nCuspsGal = lg(CuspsGal);
  CuspsGalDegs = cgetg(nCuspsGal,t_VECSMALL);
  for(i=1;i<nCuspsGal;i++)
    CuspsGalDegs[i] = lg(gel(CuspsGal,i))-1;
  if(DEBUGLEVEL) printf("modpicinit: %lu cusps\n",nCusps);
  if(UseTp)
  {
    CuspsGalDiamp = GammaHCusps_GalDiam_orbits(up,Cusps,CuspsGal,CuspsTags);
    nCuspsGalDiamp = lg(CuspsGalDiamp);
    CuspsGalDiampDegs = cgetg(nCuspsGalDiamp,t_VECSMALL);
    for(i=1;i<nCuspsGalDiamp;i++)
      CuspsGalDiampDegs[i] = lg(gel(CuspsGalDiamp,i))-1;
  }
  else CuspsGalDiamp = CuspsGalDiampDegs = NULL;
  /* Get data about fibre */
  Pts = ZNZ2primH(N,H);
  PtsTags = gel(Pts,2);
  Pts = gel(Pts,1);
  nPts = lg(Pts)-1;
  if(DEBUGLEVEL) printf("modpicinit: %lu points on fibre of X_H(%lu) -> X(1)\n",nPts,N);
  if(UseTp)
  {
    PtsDiamp = PtsDiamp0 = cgetg(nPts+1,t_VECSMALL); /* Perm induced by <p> */
    for(i=1;i<=nPts;i++)
      PtsDiamp[i] = zM_coef_mod(PtsTags,zv_z_mul(gel(Pts,i),up));
  }
  else PtsDiamp = PtsDiamp0 = NULL;
  MPts = cgetg(nPts+1,t_VEC); /* Matrices having these bottom rows */
  for(i=1;i<=nPts;i++) /* P_g = P_g' on X_H(N) <=> g,g' same bottom row mod H */
    gel(MPts,i) = Bot2SL2(gel(Pts,i),N);
  /* Get first elliptic curve */
  if(DEBUGLEVEL) pari_printf("modpicinit: Looking for an elliptic curve whose %lu-torsion is defined over F_%Ps^%lu\n",N,p,a);
  list_j = cgetg(nbE+1,t_VEC);
  setlg(list_j,1);
  E = GetMl1(N,Pts,PtsTags,T,p,e,NULL,list_j); /* NULL: no preferred zeta_N for now */
  if(E==NULL) /* Could not find E, and giving up? */
    return gc_NULL(av);
  if(DEBUGLEVEL) pari_printf("modpicinit: Working on y^2=x^3+%Psx+%Ps (j=%Ps)\n",gmael(E,1,1),gmael(E,1,2),gmael(E,1,3));
  Ml1 = gel(E,2);
  PtsFrob = gel(E,3);
  zN = gel(E,4);
  setlg(list_j,2);
  gel(list_j,1) = gmael(E,1,3);
  zNpows = cgetg(N+1,t_VEC);
  gel(zNpows,1) = zN;
  for(i=1;i<N;i++)
    gel(zNpows,i+1) = Fq_mul(gel(zNpows,i),zN,T,pe);
  /* Find basis for M2(GammaH(N)) */
  d = g+nCusps-1;
  if(DEBUGLEVEL) printf("modpicinit: M2(GammaH) (dim %lu)\n",d);
  d1 = (4*d)/3; /* # gens */
  if(d1>nPts)
    d1 = nPts;
  d1++;
  TH = GammaHmodN(N,H1); /* reps in SL2(Z) of GammaH mod N,-1 */
  for(;;)
  {
    M2gens = cgetg(d1,t_VEC);
    for(i=1;i<d1;i++)
    {
      gel(M2gens,i) = geni = cgetg(3,t_VEC);
      gel(geni,1) = gel(Pts,1+random_Fl(nPts));
      gel(geni,2) = gel(Pts,1+random_Fl(nPts));
    }
    M2 = M2mat(M2gens,Ml1,TH,MPts,T,pe); /* d1 forms E_1^v*E_1^v' in M2(GammaH) */
    /* Do we span? */
    B = gel(FqM_indexrank(M2,T,p),2);
    nB = lg(B)-1;
    if(DEBUGLEVEL>=2) printf("modpicinit: span %lu out of %lu\n",nB,d);
    if(nB>d)
      pari_err(e_BUG,"Excessive dimension in M2(GammaH)");
    if(nB==d)
      break;
    d1 += 2*(d-nB);
  }
  /* Extract basis */
  for(i=1;i<=d;i++)
  {
    gel(M2,i) = gel(M2,B[i]);
    gel(M2gens,i) = gel(M2gens,B[i]);
  }
  setlg(M2,d+1);
  setlg(M2gens,d+1);
  /* Get extra ellitpic curves */
  for(i=2;i<=nbE;i++)
  {
    if(DEBUGLEVEL) printf("modpicinit: Getting extra elliptic curve %lu/%lu\n",i,nbE);
    E = GetMl1(N,Pts,PtsTags,T,p,e,zNpows,list_j);
    if(E==NULL) /* Could not find E, and giving up? */
      return gc_NULL(av);
    if(DEBUGLEVEL) pari_printf("modpicinit: working on y^2=x^3+%Psx+%Ps (j=%Ps)\n",gmael(E,1,1),gmael(E,1,2),gmael(E,1,3));
    setlg(list_j,i+1);
    gel(list_j,i) = gmael(E,1,3);
    M2 = vconcat(M2,M2mat(M2gens,gel(E,2),TH,MPts,T,pe));
    PtsFrob = PermConcat(PtsFrob,gel(E,3));
    if(UseTp) PtsDiamp = PermConcat(PtsDiamp,PtsDiamp0);
  }
  /* Prepare divisors to know min qprec
   * then prune: M2 -> S2(>=3cusps) = M2(-C0) */
  if(UseTp)
  {
    C0o = BalancedDivInf(nCusps-3,CuspsGalDiampDegs);
    C0 = Divo2Div(C0o,CuspsGalDiamp,CuspsTags,nCusps);
    if(DEBUGLEVEL) printf("modpicinit: Wanted C0 of degree %lu, got %lu\n",nCusps-3,zv_sum(C0));
  }
  else
  {
    C0o = BalancedDiv(nCusps-3,CuspsGalDegs);
    C0 = Divo2Div(C0o,CuspsGal,CuspsTags,nCusps);
  }
  d0 = 2*g+nCusps-(2+zv_sum(C0));
  if(DEBUGLEVEL) printf("modpicinit: d0=%lu\n",d0);
  gel(J,3) = utoi(d0);
  /* Evaluation J_H(N) -> A1 */
  E1o = BalancedDiv(d0-g,CuspsGalDegs);
  E2o = DivPerturb(E1o,CuspsGalDegs);
  E1 = Divo2Div(E1o,CuspsGal,CuspsTags,nCusps);
  E2 = Divo2Div(E2o,CuspsGal,CuspsTags,nCusps);
  M2qexps = cgetg(nCusps+1,t_VEC);
  if(DEBUGLEVEL) printf("modpicinit: q-exp of forms of weight 2, cusp");
  params = cgetg(12,t_VEC);
  gel(params,2) = utoi(N);
  gel(params,3) = TH;
  gel(params,6) = zNpows;
  gel(params,8) = T;
  gel(params,9) = pe;
  gel(params,10) = p;
  gel(params,11) = ie = stoi(e);
  worker = strtofunction("_TrE2qexp");
  mt_queue_start_lim(&pt,worker,nCusps*d);
  pending = 0;
  for(s=1;s<=nCusps||pending;s++)
  {
    if(s<=nCusps)
    {
      if(DEBUGLEVEL) printf(" %lu",s);
      gel(M2qexps,s) = cgetg(d+1,t_MAT);
      gel(params,4) = gel(CuspsMats,s);
      gel(params,5) = stoi(CuspsWidths[s]);
      sprec = 2*C0[s]+(E1[s]>E2[s]?E1[s]:E2[s]);
      if(CuspsQexp[s] && sprec<qprec)
        sprec = qprec;
      gel(params,7) = stoi(sprec);
    }
    for(i=1;i<=d;i++)
    {
      if(s<=nCusps)
      {
        gel(params,1) = gel(M2gens,i);
        mt_queue_submit(&pt,s*d+i,params);
      }
      else mt_queue_submit(&pt,0,NULL);
      done = mt_queue_get(&pt,&workid,&pending);
      if(done)
      {
        j = udivuu_rem(workid-1,d,&k);
        gmael(M2qexps,j,k+1) = done;
      }
      if(s>nCusps) break;
    }
  }
  mt_queue_end(&pt);
  if(DEBUGLEVEL) printf("\nmodpicinit: Pruning, dim %lu, eval on >= %lu pts (%lu safe)\n",d-zv_sum(C0),5*d0+1-g,5*d0+1);
  /* M2 -> S2(>=3cusps) = M2(-C0) */
  U0 = MRRsubspace(M2qexps,C0,NULL,T,pe,p,e);
  M20 = FqM_mul(M2,U0,T,pe);
  d = d0+1-g;
  /* Reduce # pts at which we evaluate */
  PtsFrob0 = PtsFrob;
  PtsDiamp0 = PtsDiamp;
  av1 = avma;
  V1 = V2 = V2gens = V3 = NULL; /* Else gcc freaks out */
  for(nZ=5*d0+1-g;nZ<=5*d0+1;nZ++) // TODO nZ=nPts?
  {
    if(UseTp)
    {
      Pts = SubPerms_inf(mkvec2(PtsFrob0,PtsDiamp0),nZ);
      PtsFrob = gmael(Pts,2,1); /* Induced perm */
      PtsDiamp = gmael(Pts,2,2); /* Induced perm */
      Pts = gel(Pts,1); /* Selected indices */
    }
    else
    {
      Pts = SubPerms_inf(mkvec(PtsFrob0),nZ);
      PtsFrob = gmael(Pts,2,1); /* Induced perm */
      Pts = gel(Pts,1); /* Selected indices */
    }
    nPts = lg(Pts);
    if(DEBUGLEVEL) printf("modpicinit: Wanted to reduce nZ to %lu, actually got %lu\n",nZ,nPts-1);
    V1 = cgetg(d+1,t_MAT);
    for(j=1;j<=d;j++)
    {
      gel(V1,j) = cgetg(nPts,t_COL);
      for(i=1;i<nPts;i++)
        gcoeff(V1,i,j) = gcoeff(M20,Pts[i],j);
    }
    // Check enough pts
    V2 = DivAdd1(V1,V1,2*d0+1-g,T,p,p,d0,0,1);// TODO tune excess=d0
    V2gens = gel(V2,2);
    V2 = gel(V2,1);
    V3 = DivAdd(V2,V1,3*d0+1-g,T,p,p,d0,0); // TODO tune excess=d0
    V5 = DivAdd(V2,V3,5*d0+1-g,T,p,p,d0,5); // TODO tune excess=d0
    if(V5) break;
    if(DEBUGLEVEL>=2) printf("V5 FAILED\n");
    set_avma(av1);
  }
  if(DEBUGLEVEL) printf("Out of pruning, nZ=%lu vs %lu\n",nPts-1,5*d0+1);
  gel(V,1) = V1;
  // TODO do not recalc if e==1
  /* Forms of weight 4 */
  if(e>1)
  {
    d = 2*d0+1-g;
    if(DEBUGLEVEL) printf("modpicinit: M4(GammaH)(-2C0), dim %lu\n",d);
    V2 = DivAdd1(V1,V1,d,T,pe,p,d0,0,1); // TODO tune excess=d0
    V2gens = gel(V2,2);
    V2 = gel(V2,1);
  }
  gel(V,2) = V2;
  gel(V,5) = I = gel(FqM_indexrank(V2,T,p),1); /* Rows of V2 forming invertible block */
  M = cgetg(d+1,t_MAT);
  for(j=1;j<=d;j++)
  {
    gel(M,j) = cgetg(d+1,t_COL);
    for(i=1;i<=d;i++)
      gcoeff(M,i,j) = gcoeff(V2,I[i],j);
  }
  gel(V,4) = ZpXQMinv(M,T,pe,p,e); /* Matrix to ID forms of weight 4 from their I coords */
  if(DEBUGLEVEL) printf("modpicinit: q-exp of forms of weight 4\n");
  params = cgetg(6,t_VEC);
  gel(params,2) = V2gens;
  gel(params,3) = U0;
  gel(params,4) = T;
  gel(params,5) = pe;
  worker = strtofunction("_M4qexp_worker");
  mt_queue_start_lim(&pt,worker,nCusps);
  pending = 0;
  V2qexps = cgetg(nCusps+1,t_VEC);
  for(s=1;s<=nCusps||pending;s++)
  {
    if(s<=nCusps)
    {
      gel(params,1) = gel(M2qexps,s);
      mt_queue_submit(&pt,s,params);
    }
    else mt_queue_submit(&pt,0,NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done)
      gel(V2qexps,workid) = done;
  }
  mt_queue_end(&pt);
  if(DEBUGLEVEL) printf("modpicinit: Eval data\n");
  C02 = zv_z_mul(C0,2);
  gel(J,14) = EvalData = cgetg(4,t_VEC);
  // TODO parallel
  gel(EvalData,1) = mkvec(FqM_mul(V2,MRRsubspace(V2qexps,E1,C02,T,pe,p,e),T,pe));
  gel(EvalData,2) = mkvec(FqM_mul(V2,MRRsubspace(V2qexps,E2,C02,T,pe,p,e),T,pe));
  mQ = 1; /* 1 + Total number of coefs at Q cusps */
  for(s=1;s<=nCusps;s++)
  {
    if(CuspsQexp[s])
      mQ += lg(gmael(V2qexps,s,1))-1-C02[s];
  }
  M4Q = cgetg(d+1,t_MAT);
  for(j=1;j<=d;j++)
  {
    gel(M4Q,j) = cgetg(mQ,t_COL);
    i = 1;
    for(s=1;s<=nCusps;s++)
    {
      if(CuspsQexp[s]==0) continue;
      pageV2 = gel(V2qexps,s);
      sprec = lg(gel(pageV2,1));
      for(k=1+C02[s];k<sprec;k++)
        gcoeff(M4Q,i++,j) = gcoeff(pageV2,k,j);
    }
  }
  gel(EvalData,3) = FqM_mul(M4Q,gel(V,4),T,pe);
  /* Forms of weight 6 */
  if(e>1)
  {
    d = 3*d0+1-g;
    if(DEBUGLEVEL) printf("modpicinit: M6(GammaH)(-3C0), dim %lu\n",d);
    V3 = DivAdd(V2,V1,d,T,p,pe,d0,0); // TODO tune excess=d0
  }
  gel(V,3) = V3;
  /* Finish constructing J */
  gel(J,7) = ie;
  if(DEBUGLEVEL) printf("modpicinit: Computing equation matrices\n");
  gel(J,12) = KV = cgetg(4,t_VEC);
  worker = strtofunction("_mateqnpadic");
  params = cgetg(6,t_VEC);
  gel(params,2) = T;
  gel(params,3) = pe;
  gel(params,4) = p;
  gel(params,5) = ie;
  mt_queue_start_lim(&pt,worker,3);
  for(i=1;i<=3||pending;i++)
  {
    if(i<=3)
    {
      gel(params,1) = gel(V,i);
      mt_queue_submit(&pt,i,params);
    }
    else mt_queue_submit(&pt,i,NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done) gel(KV,workid) = done;
  }
  mt_queue_end(&pt);
  gel(J,13) = DivMul(gel(V1,1),V1,T,pe);
  gel(J,16) = PtsFrob;
  gel(J,17) = UseTp ? mkvec(mkvec2(PtsDiamp,gen_0)) : cgetg(1,t_VEC);
  return gerepilecopy(av,J);
}

GEN
ModPicInit_gp(ulong N, GEN H, GEN p, ulong a, long e, GEN Lp, long UseTp, ulong nbE, ulong qprec)
{
  GEN J;
  J = ModPicInit(N,H,p,a,e,Lp,UseTp,nbE,qprec);
  if(J==NULL)
  {
    if(nbE>1)
      pari_err(e_MISC,"Unable to find suitable elliptic curve, try another value of the prime p");
    else
      pari_err(e_MISC,"Unable to find suitable elliptic curve(s), try requesting fewer elliptic curves or with another value of the prime p");
  }
  return J;
}

GEN
PicTp(GEN J, GEN W, GEN l)
{ /* Assumes <p> is given by the 1st aut of J */
  /* TODO check aut 1 is present? */
  /* Use Eichler-Shimura Tp = Frob + p <p> Frob^-1 */
  /* If l is present, assumes l*W = 0 */
  pari_sp av = avma;
  GEN p,W1,W2,W3;
  p = Jgetp(J);
  W1 = PicFrob(J,W);
  W2 = PicAut(J,W,1);
  W2 = PicFrobInv(J,W2);
  if(l && !gequal0(l))
  {
    p = centermodii(p,l,shifti(l,-1));
  }
  W2 = PicMul(J,W2,p,2);
  W3 = PicAdd(J,W1,W2);
  return gerepileupto(av,W3);
}

/* mfgalrep */

GEN
mfyt(GEN pf, GEN qf, GEN l, GEN coefs)
{
  /* pf: mfparams(f)
   * qf: mfcoefs(f), at least up to max coefs
   * l: prime
   * coefs: vector of [n,bn]
   * look for prime L|l such that an(f) mod L = bn for all n in coefs */
  pari_sp av = avma;
  GEN P,Phi,rnf,F,t,k,Z,T,Y,V,bn,an,ani;
  ulong nZ,ncoefs,nV,n,i,j;
  long vt,vy;
  P = liftpol(gel(pf,4)); /* P(y,t): Hecke field */
  vy = varn(P);
  Phi = gel(pf,5); /* Phi(t): nebentypus */
  vt = varn(Phi);
  rnf = rnfequation2(Phi,P);
  F = gel(rnf,1); /* Absolute equation */
  t = liftpol(gel(rnf,2)); /* Root of Phi in absolute model */
  k = gel(rnf,3); /* y+k*t is gen of absolute model */
  Z = FpX_roots(F,l); /* Possible values of y+k*t mod l */
  nZ = lg(Z);
  T = cgetg(nZ,t_VEC); /* Corresponding values of t */
  Y = cgetg(nZ,t_VEC); /* Corresponding values of y */
  V = cgetg(nZ,t_VECSMALL); /* Booleans: acceptable values */
  for(i=1;i<nZ;i++)
  {
    gel(T,i) = Fp_red(poleval(t,gel(Z,i)),l);
    gel(Y,i) = Fp_sub(gel(Z,i),mulii(k,gel(T,i)),l);
    V[i] = 1;
  }
  if(DEBUGLEVEL >= 3) pari_printf("mfyt: %lu choices of reductions mod %Ps; Y=%Ps, T=%Ps\n",nZ-1,l,Y,T);
  ncoefs = coefs ? lg(coefs) : 0;
  for(j=1;j<ncoefs;j++)
  {
    n = itou(gmael(coefs,j,1));
    bn = gmael(coefs,j,2);
    an = liftpol(gel(qf,n+1));
    if(DEBUGLEVEL>=3)
      pari_printf("mfyt: Want a%lu = %Ps to reduce to %Ps\n",n,an,bn);
    for(i=1;i<nZ;i++)
    {
      ani = gsubst(gsubst(an,vy,gel(Y,i)),vt,gel(T,i));
      if(DEBUGLEVEL>=3)
        pari_printf("mfyt: with choice %lu, a%lu reduces to %Ps\n",i,n,Fp_red(ani,l));
      if(!gequal0(Fp_red(gsub(ani,bn),l)))
        V[i] = 0;
    }
  }
  nV = zv_sum(V);
  if(nV==0)
    pari_err(e_MISC,"Inconsistent data about prime above l");
  if(nV>1)
    pari_warn(warner,"Insufficient data to specify prime above l; defaulting to first one");
  for(i=1;i<nZ;i++)
  {
    if(V[i]==0) continue;
    break;
  }
  return gerepilecopy(av,mkvec2(gel(Y,i),gel(T,i)));
}

GEN
mfgalrep_bestp(GEN f, GEN l, GEN coefs, GEN prange, long UseTp)
{
  pari_sp av = avma;
  GEN ilN,pf,H,eps,o,to,pmin,pmax,gen_5,p,qf,listp,Lp,yt,ap,epsp,chi,psi,rem,a1,a2,a,xa1,NJ,M,A,res,res1;
  ulong ul,N,lN,philN,k,h,epsh,nH,np,i,i1,j,qprec,ncoefs,n,S,nM,nA;
  long vt,vy;
  forprime_t piter;
  ul = itou(l);
  pf = mfparams(f);
  if(cmpii(gel(pf,2),l)!=-1)
    pari_err(e_IMPL,"case k >= l");
  N = itou(gel(pf,1));
  k = itos(gel(pf,2));
  eps = znchar(f);
  o = charorder0(gel(eps,1),gel(eps,2));
  vy = varn(gel(pf,4));
  vt = varn(gel(pf,5));
  pmin = pmax = gen_0; /* Range of p */
  gen_5 = utoi(5);
  switch(typ(prange))
  {
    case t_INT:
      pmax = prange;
      break;
    case t_VEC:
      pmin = gel(prange,1);
      pmax = gel(prange,2);
      break;
    case t_VECSMALL:
      pmin = utoi(prange[1]);
      pmax = utoi(prange[2]);
      break;
    default:
      pari_err_TYPE("pmax",prange);
  }
  if(cmpii(pmin,gen_5)==-1) pmin = gen_5;
  qprec = itou(pmax);
  if(coefs)
  {
    ncoefs = lg(coefs);
    for(i=1;i<ncoefs;i++)
    {
      n = itou(gmael(coefs,i,1));
      if(n>qprec) qprec = n;
    }
  }
  qf = liftpol(mfcoefs(f,itou(pmax),1)); /* q-exp */
  yt = mfyt(pf,qf,l,coefs);
  to = mkvec2(gel(yt,2),o);
  lN = k==2 ? N : ul*N; /* Level of mod crv */
  ilN = utoi(lN);
  philN = eulerphiu(lN);
  H = cgetg(lN+1,t_VECSMALL); /* Ker eps(f2), subgroup of (Z/lNZ)* */
  nH = 0;
  if(k==1) k = ul; /* TODO test */
  for(h=0;h<lN;h++)
  {
    if(ugcd(h,lN)>1) continue;
    epsh = umodiu(chareval(gel(eps,1),gel(eps,2),utoi(h),to),ul);
    if(Fl_mul(Fl_powu(h,k-2,ul),epsh,ul)!=1) continue;
    H[++nH] = h;
  }
  setlg(H,nH+1);
  listp = cgetg(itou(pmax)-4,t_VEC);
  np = 1;
  forprime_init(&piter,pmin,pmax);
  while((p = forprime_next(&piter)))
  {
    if(dvdui(N*nH,p)) continue;
    if(dvdii(l,p)) continue;
    gel(listp,np++) = gcopy(p);
  }
  setlg(listp,np); /* List of candidate p */
  Lp = ModCrv_charpoly_multi(lN,H,listp);
  if(degpol(gmael(Lp,1,1))==0)
    pari_err(e_MISC,"This Galois representation is a power of the cyclotomic character");
  for(i=i1=1;i<np;i++)
  {
    p = gel(listp,i);
    ap = gel(qf,itou(p)+1);
    ap = Fp_red(gsubst(gsubst(ap,vy,gel(yt,1)),vt,gel(yt,2)),l);
    epsp = chareval(gel(eps,1),gel(eps,2),p,to);
    chi = deg2pol_shallow(gen_1,negi(ap),Fp_mul(Fp_powu(p,k-1,l),epsp,l),0);
    psi = FpX_divrem(gmael(Lp,i,1),chi,l,&rem);
    if(!gequal0(rem))
      pari_err(e_BUG,"charpoly in mfgalrep_bestp");
    if(degpol(FpX_gcd(chi,psi,l)))
    {
      if(UseTp)
      {
        S = 0;
        M = gmael(Lp,i,2); /* Matrices of Tp of S2(chi) */
        nM = lg(M);
        for(n=1;n<nM;n++)
        {
          A = gel(M,n);
          nA = lg(A);
          for(j=1;j<nA;j++)
            gcoeff(A,j,j) = subii(gcoeff(A,j,j),ap);
          S += (lg(FpM_ker(A,l))-1);
        } /* S >= dim Ker(Tp-ap) */
        if(S<1) pari_err(e_BUG,"mfgalrep_bestp_S");
        if(S>1)
        {
          if(DEBUGLEVEL) pari_printf("mfgalrep_bestp: p=%Ps has multiplicity and cannot be used, even with Tp\n",p);
          continue;
        }
        if(DEBUGLEVEL) pari_printf("mfgalrep_bestp: p=%Ps has multiplicity, but can be used thanks to Tp\n",p);
      }
      else
      {
        if(DEBUGLEVEL) pari_printf("mfgalrep_bestp: p=%Ps has multiplicity\n",p);
        continue;
      }
    }
    a1 = gel(FpX_root_order_bound(chi,l),2);
    a2 = utoi(Fl_order(itou(p),philN,lN));
    a = lcmii(a1,a2);
    if(DEBUGLEVEL)
    {
      xa1 = pol_x(0);
      xa1 = powgi(xa1,a);
      xa1 = ZX_Z_add(xa1,gen_m1);
      NJ = ZX_resultant(gmael(Lp,i,1),xa1);
      pari_printf("mfgalrep_bestp: p=%Ps needs deg %Ps (%Ps to split rep, %Ps for roots of 1) -> lg #J = %ld\n",p,a,a1,a2,logint(NJ,gen_2));
    }
    gel(listp,i1++) = mkvecn(6,a,p,gmael(Lp,i,1),ap,epsp,chi);
  }
  if(i1==1)
    pari_err(e_MISC,"mfgalrep_bestp: No suitable prime, please enlarge prime range");
  setlg(listp,i1);
  res = cgetg(3,t_VEC);
  gel(res,1) = res1 = cgetg(3,t_VEC);
  gel(res1,1) = gcopy(ilN);
  gel(res1,2) = gcopy(H);
  gel(res,2) = i1==2 ? gcopy(listp) : lexsort(listp);
  return gerepileupto(av,res);
}

long
PicTors_TpClosure(GEN J, GEN* pBT, GEN* pmatTp, GEN T, GEN PT, GEN FRparams, GEN LinTests, GEN LinTestsNames, GEN* pR, ulong* pNewTestName)
{ /* Shallow */
  GEN l,X,matTp2,u;
  ulong i,j,d,d2;
  int replace;
  d = lg(*pBT);
  d2 = 0;
  l = gel(FRparams,1);
  for(;;)
  {
    X = PicTors_UpdatePairings(J,FRparams,*pBT,*pR,T,PT,&replace);
    if(X==NULL) return -1;
    if(replace==-1) /* T in span BT */
    {
      /* Update mat Tp */
      if(d2)
      {
        matTp2 = cgetg(d+d2,t_MAT);
        for(j=1;j<d;j++)
        {
          gel(matTp2,j) = cgetg(d+d2,t_COL);
          for(i=1;i<d+d2;i++)
            gcoeff(matTp2,i,j) = i<d?gcoeff(*pmatTp,i,j):gen_0;
        }
        for(j=d;j<d+d2-1;j++)
        {
          gel(matTp2,j) = cgetg(d+d2,t_COL);
          for(i=1;i<d+d2;i++)
            gcoeff(matTp2,i,j) = i==j+1?gen_1:gen_0;
        }
        gel(matTp2,d+d2-1) = cgetg(d+d2,t_COL);
        u = Fp_neg(Fp_inv(gel(X,d+d2),l),l);
        for(i=1;i<d+d2;i++)
          gcoeff(matTp2,i,d+d2-1) = Fp_mul(gel(X,i),u,l);
        *pmatTp = matTp2;
      }
      return d2;
    }
    /* T not in span BT */
    *pR = gel(X,1);
    d2++;
    *pBT = VecExtend1_shallow(*pBT,T);
    if(replace)
    {
      *pR = gel(X,1);
      gel(LinTests,replace) = gel(X,2);
      LinTestsNames[replace] = ++(*pNewTestName);
    }
    else *pR = X;
    T = PicTp(J,T,l);
    PT = PicTorsPairing(J,FRparams,T,LinTests);
  }
}

GEN
PicTors_TpEigen(GEN J, GEN l, GEN ap, GEN epsp, GEN chi)
{ /* TODO try to use l-power tors */
  /* TODO reuse code from pic.c */
  pari_sp av = avma;
  GEN Lp,Diva,Chi,gcdchi,Lp1,Phi,phi,Batch,BT,matTp,LinTests,LinTestsNames,FRparams,R,T,B,PT,UsedTestsNames,K,EBT,FEBT,I,Etests,FrobMat,DiamMat;
  ulong i,j,iBatch,iFrob,iPhi,a,nPhi,nBatch,d2,dB,d,r,NewTestName,nwatch;
  long workid,pending;
  GEN worker,done;
  struct pari_mt pt;
  Lp = JgetLp(J);
  a = degree(JgetT(J)); /* Residual degree */
  if(a%itou(l))
  {
    Diva = divisorsu(a);
    Diva = vecsort0(Diva,NULL,4); /* Divisors of a sorted in reverse */
    nPhi = lg(Diva);
    Phi = cgetg(nPhi,t_VEC);
    j = 0;
    for(i=1;i<lg(Phi);i++)
    {
      phi = polcyclo(Diva[i],0);
      if(degree(FpX_gcd(phi,chi,l)))
        gel(Phi,++j) = phi;
    }
    nPhi = j;
    if(nPhi==0) Phi=NULL;
  }
  else
  {
    Phi = NULL;
    nPhi = 1;
  }
  Chi = pol_1(varn(Lp)); /* gcd(Lp,chi^oo) */
  gcdchi = chi;
  Lp1 = Lp;
  while(degpol(gcdchi))
  {
    Lp1 = FpX_div(Lp1,gcdchi,l);
    Chi = FpX_mul(Chi,gcdchi,l);
    gcdchi = FpX_gcd(Lp1,chi,l);
  }
  Chi = FpX_normalize(Chi,l);

  BT = cgetg(1,t_VEC);
  matTp = cgetg(1,t_MAT);
  FRparams = PicTorsPairingInit(J,l);
  d = degpol(Chi);
  LinTests = cgetg(d+1,t_VEC); /* pts to take pairings with */
  LinTestsNames = cgetg(d+1,t_VECSMALL);
  for(i=1;i<=d;i++)
  {
    gel(LinTests,i) = PicChord(J,PicRand(J,NULL),PicRand(J,NULL),1); /* Random pt, well-mixed so as not throw off Pairings */
    LinTestsNames[i] = i;
  }
  NewTestName = d+1;
  R = cgetg(1,t_MAT);
  nBatch = (mt_nbthreads()+1)/2;//TODO
  worker = strtofunction("_PicTorsBasis_worker");
  Batch = cgetg(nBatch+1,t_VEC);
  for(iPhi=nwatch=1;;)
  {
    if(DEBUGLEVEL) printf("PicTors_TpEigen: Generating new batch of %lu torsion points\n",nBatch);
    mt_queue_start_lim(&pt,worker,nBatch);
    for(iBatch=1;iBatch<=nBatch||pending;iBatch++)
    {
      if(iBatch<=nBatch)
      {
        if(Phi)
        {
          if(iPhi>nPhi) iPhi -= nPhi;
          phi = gel(Phi,iPhi++);
        }
        else phi = gen_0;
        mt_queue_submit(&pt,iBatch,mkvecn(8,J,l,Chi,phi,FRparams,LinTests,LinTestsNames,genrand(NULL)));
      }
      else mt_queue_submit(&pt,iBatch,NULL);
      done = mt_queue_get(&pt,&workid,&pending);
      if(done)
        gel(Batch,workid) = done;
    }
    mt_queue_end(&pt);
    for(iBatch=1;iBatch<=nBatch;iBatch++)
    {
      if(DEBUGLEVEL>=2)
        printf("PicTors_TpEigen: Moving on to point %lu of batch\n",iBatch);
      T = gel(Batch,iBatch);
      if(gequal0(T))
      {
        if(DEBUGLEVEL>=2) printf("PicTors_TpEigen: This point is zero, moving on to the next one\n");
        nwatch++;
        continue;
      }
      B = gel(T,4);
      dB = degpol(B);
      PT = gel(T,5);
      UsedTestsNames = gel(T,6);
      T = gel(T,3);
      /* Make sure pairings are current */
      if(DEBUGLEVEL>=2) printf("PicTors_TpEigen: Refreshing pairings\n");
      PT = PicRefreshPairings(J,FRparams,T,PT,UsedTestsNames,LinTests,LinTestsNames);
      for(iFrob=0;;iFrob++)
      {
        if(DEBUGLEVEL>=2)
          pari_printf("PicTors_TpEigen: Throwing in Frob-iterate %lu of point %lu (B = %Ps)\n",iFrob,iBatch,B);
        d2 = PicTors_TpClosure(J,&BT,&matTp,T,PT,FRparams,LinTests,LinTestsNames,&R,&NewTestName);
        if(d2==-1) /* Got stuck and want to give up? */
          return gc_NULL(av);
        if(DEBUGLEVEL>=2) printf("PicTors_TpEigen: taking Tp closure increases dim by %lu\n",d2);
        if(d2==0)
        {
          nwatch++;
          break;
        }
        else nwatch = 0;
        K = gcopy(matTp); /* Tp - ap */
        for(i=1;i<lg(K);i++)
          gcoeff(K,i,i) = subii(gcoeff(K,i,i),ap);
        K = FpM_ker(K,l); /* Ker(Tp-ap)*/
        r = lg(K)-1;
        if(DEBUGLEVEL>=2)
        {
          printf("PicTors_TpEigen: Now matTp=\n");
          printp(mkvec(matTp));
          pari_printf("and the dim of the Tp=%Ps eigenspace is %lu\n",ap,r);
        }
        if(r==2) /* Finished? */
        {
          K = FpM_center(K,l,shifti(l,-1));
          EBT = cgetg(3,t_VEC);
          gel(EBT,1) = PicLC(J,gel(K,1),BT);
          gel(EBT,2) = PicLC(J,gel(K,2),BT);
          R = FpM_mul(R,K,l);
          I = gel(FpM_indexrank(R,l),1); /* Indices of LinTests which are indep on Eigenspace */
          Etests = cgetg(3,t_VEC);
          gel(Etests,1) = gel(LinTests,I[1]);
          gel(Etests,2) = gel(LinTests,I[2]);
          gcoeff(R,1,1) = gcoeff(R,I[1],1);
          gcoeff(R,2,1) = gcoeff(R,I[2],1);
          setlg(gel(R,1),3);
          gcoeff(R,1,2) = gcoeff(R,I[1],2);
          gcoeff(R,2,2) = gcoeff(R,I[2],2);
          setlg(gel(R,2),3);
          FEBT = cgetg(3,t_VEC);
          gel(FEBT,1) = PicFrob(J,gel(EBT,1));
          gel(FEBT,2) = PicFrob(J,gel(EBT,2));
          FrobMat = FpM_mul(FpM_inv(R,l),PicTorsPairing(J,FRparams,FEBT,Etests),l);
          DiamMat = cgetg(3,t_MAT);
          gel(DiamMat,1) = cgetg(3,t_COL);
          gel(DiamMat,2) = cgetg(3,t_COL);
          gcoeff(DiamMat,1,1) = gcoeff(DiamMat,2,2) = epsp;
          gcoeff(DiamMat,1,2) = gcoeff(DiamMat,2,1) = gen_0;
          B = cgetg(4,t_VEC);
          gel(B,1) = EBT;
          gel(B,2) = FrobMat;
          gel(B,3) = mkvec(DiamMat);
          return gerepilecopy(av,B);
        }
        if(++iFrob==dB) break;
      }
      if(nwatch>2*nPhi)
        return gc_NULL(av);
    }
  }
}

GEN
mfgalrep(GEN f, GEN l, GEN prange, ulong D, long UseTp, ulong nbE, ulong qprec)
{
  pari_sp av = avma, av1;
  pari_timer WT,CPUT;
  GEN coefs,best,besti,H,p,Lp,ap,epsp,chi,log2,log10,logp,J,J1,B,R;
  ulong N,a,ip,nwatch;
  long e;
  if(DEBUGLEVEL)
  {
    walltimer_start(&WT);
    timer_start(&CPUT);
  }
  if(typ(l)==t_VEC)
  {
    coefs = gel(l,2);
    l = gel(l,1);
  }
  else coefs = NULL;
  best = mfgalrep_bestp(f,l,coefs,prange,UseTp);
  if(DEBUGLEVEL) timers_printf("mfgalrep","choice p",&CPUT,&WT);
  H = gel(best,1);
  N = itou(gel(H,1));
  H = gel(H,2);
  best = gel(best,2);
  ip = 1;
  av1 = avma;
  nwatch = 0;
  do
  {
    set_avma(av1);
    if(nwatch>2)
    {
      nwatch = 0;
      ip++;
    }
    if(ip>=lg(best))
      pari_err(e_MISC,"run out of primes p, try increasing pmax");
    if(DEBUGLEVEL)
    {
      walltimer_start(&WT);
      timer_start(&CPUT);
    }
    besti = gel(best,ip);
    a = itou(gel(besti,1));
    p = gel(besti,2);
    Lp = gel(besti,3);
    ap = gel(besti,4);
    epsp = gel(besti,5);
    chi = gel(besti,6);
    /* Smallest e such that sqrt(1/2*p^e)>10^D */
    log2 = logr_abs(utor(2,DEFAULTPREC));
    log10 = logr_abs(utor(10,DEFAULTPREC));
    logp = logr_abs(itor(p,DEFAULTPREC));
    e = itos(gceil(divrr(addrr(log2,mulur(2*D,log10)),logp)));
    if(DEBUGLEVEL) pari_printf("mfgalrep: Constructing J_H(%lu) (H=%Ps, genus %ld) over Q_%Ps^%lu with accuracy O(%Ps^%ld)\n",N,H,degpol(Lp)/2,p,a,p,e);
    J = ModPicInit(N,H,p,a,e,Lp,UseTp,nbE,qprec);
    if(J==NULL)
    {
      nwatch = 0;
      ip++;
      continue;
    }
    if(DEBUGLEVEL) timers_printf("mfgalrep","modpicinit",&CPUT,&WT);
    if(UseTp)
    {
      J1 = PicSetPrec(J,1);
      B = PicTors_TpEigen(J1,l,ap,epsp,chi);
      if(B==NULL)
      {
        nwatch++;
        continue;
      }
      if(DEBUGLEVEL) timers_printf("mfgalrep","Tp eigenspace",&CPUT,&WT);
      R = PicTorsGalRep_from_basis(J,J1,l,B);
    }
    else R = PicTorsGalRep(J,l,chi);
    nwatch++;
  } while(R==NULL);
  return gerepileupto(av,R);
}
