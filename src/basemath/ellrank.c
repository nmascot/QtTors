/* Copyright (C) 2020  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

/* This file is a port by Bill Allombert of the script ellQ.gp by Denis Simon
 * Copyright (C) 2019 Denis Simon
 * Distributed under the terms of the GNU General Public License (GPL) */

static long LIM1 = 10000;
static long LIMTRIV = 10000;

/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */
/*    FUNCTIONS FOR POLYNOMIALS                \\ */
/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */

static GEN
ell2pol(GEN ell)
{
  return mkpoln(4, gen_1, ell_get_a2(ell), ell_get_a4(ell), ell_get_a6(ell));
}

static GEN
sqrtrat(GEN a)
{
  if (typ(a) == t_INT) return sqrti(a);
  retmkfrac(sqrti(gel(a,1)),sqrti(gel(a,2)));
}

static GEN
redqfbsplit(GEN a, GEN b, GEN c, GEN d)
{
  GEN p = subii(d,b), q = shifti(a,1);
  GEN U, Q, u, v, w = bezout(p, q, &u, &v);

  if (!equali1(w)) { p = diviiexact(p, w); q = diviiexact(q, w); }
  U = mkmat22(p, negi(v), q, u);
  Q = qfb_apply_ZM(mkvec3(a,b,c), U);
  a = gel(Q, 1); b = gel(Q, 2); c = gel(Q,3);
  if (signe(b) < 0)
  {
    b = negi(b);
    gcoeff(U,1,2) = negi(gcoeff(U,1,2));
    gcoeff(U,2,2) = negi(gcoeff(U,2,2));
  }
  gel(U,2) = ZC_lincomb(gen_1, truedivii(negi(c), d),
                        gel(U,2), gel(U,1));
  return U;
}

static GEN
polreduce(GEN P, GEN M)
{
  long d = degpol(P), v = varn(P);
  GEN A = deg1pol_shallow(gcoeff(M,1,1),gcoeff(M,1,2),v);
  GEN B = gpowers(deg1pol(gcoeff(M,2,1),gcoeff(M,2,2),v), d);
  return gel(RgX_homogenous_evalpow(P, A, B),1);
}

static GEN
hyperellreduce(GEN Q)
{
  pari_sp av = avma;
  long d = degpol(Q);
  GEN den, P = Q_primitive_part(Q, &den);
  GEN a = gel(P,d+2), b = gel(P,d+1), c = gel(P, d);
  GEN q1, q2, q3, D, M, R, vD;
  q1 = mulis(sqri(a), d);
  q2 = shifti(mulii(a,b), 1);
  q3 = subii(sqri(b),shifti(mulii(a,c), 1));
  D = gcdii(gcdii(q1, q2), q3);
  if (!equali1(D))
  {
    q1 = diviiexact(q1,D);
    q2 = diviiexact(q2,D);
    q3 = diviiexact(q3,D);
  }
  D = qfb_disc3(q1, q2, q3);
  if (!signe(D))
    M = mkmat22(gen_1, truedivii(negi(q2),shifti(q1,1)), gen_0, gen_1);
  else if (issquareall(D,&vD))
    M = redqfbsplit(q1, q2, q3, vD);
  else
    M = gel(qfbredsl2(mkqfb(q1,q2,q3,D), NULL),2);
  R = polreduce(P, M);
  if (den) R = gmul(R, den);
  return gerepilecopy(av, mkvec2(R, M));
}

static GEN
projratpoint(GEN pol, long lim)
{
  pari_timer ti;
  GEN P;
  if (issquare(leading_coeff(pol)))
    return mkvec3( gen_1, sqrtrat(leading_coeff(pol)), gen_0);
  if (DEBUGLEVEL) timer_start(&ti);
  P = hyperellratpoints(pol, stoi(lim), 1);
  if (DEBUGLEVEL) timer_printf(&ti,"hyperellratpoints(%ld)",lim);
  return lg(P)==1 ? NULL: mkvec3(gmael(P,1,1),gmael(P,1,2), gen_1);
}

static GEN
listratpoint(GEN pol)
{
  pari_sp ltop = avma, btop;
  GEN list, list2;
  long i, j, l;
  list = mkvec(mkvec4(pol, matid(2), gen_1, gen_1));
  l = lg(list);
  btop = avma;
  for (i = 1; i < l; i++)
  {
    GEN ff, co, p, M, C, roots;
    long lroots;
    GEN li = gel(list, i), pol = gel(li, 1);
    GEN K = ZX_content(pol);
    if (!equali1(K))
    {
      pol = gel(li, 1) = ZX_Z_divexact(gel(li, 1), K);
      gel(li, 3) = mulii(gel(li, 3), K);
    }
    K = gel(li, 3);
    if (equali1(K)) continue;
    ff = Z_factor(K); co = core2(mkvec2(K,ff));
    if (!equali1(gel(co,2)))
    {
      gel(li, 4) = mulii(gel(li, 4), gel(co,2));
      K = gel(li, 3) = gel(co, 1);
      if (equali1(K)) continue;
      ff = Z_factor(K);
    }
    p = gcoeff(ff, 1, 1);
    M = gel(li, 2); C = gel(li, 4);
    /* root at infinity */
    if (dvdii(leading_coeff(pol), p))
    {
      GEN U = mkmat2(gel(M,1), ZC_Z_mul(gel(M,2), p));
      if (equali1(content(U)))
      {
        GEN newpol = ZX_Z_divexact(ZX_rescale(pol, p), p);
        GEN vec = mkvec4(newpol, U, diviiexact(K, p), mulii(C, p));
        list = vec_append(list, vec); l++;
      }
    }
    roots = FpC_center(FpX_roots(pol, p), p, shifti(p,-1));
    lroots = lg(roots);
    for (j = 1; j < lroots; j++)
    {
      GEN U = ZM2_mul(M, mkmat22(p, gel(roots, j), gen_0, gen_1));
      if (equali1(content(U)))
      {
        GEN newpol = ZX_Z_divexact(ZX_unscale(ZX_translate(pol, gel(roots, j)), p), p);
        GEN vec = mkvec4(newpol, U, diviiexact(K, p), mulii(C, p));
        list = vec_append(list, vec); l++;
      }
    }
    if (gc_needed(btop, 1)) gerepileall(btop, 2, &pol, &list);
  }

  list2 = cgetg(l, t_VEC);
  for (i = 1, j = 1; i < l; i++)
  {
    GEN li = gel(list, i);
    if (equali1(gel(li,1)))
    {
      GEN rr = hyperellreduce(gel(li, 1));
      gel(list2, j++) = mkvec4(gel(rr, 1), gmul(gel(li, 2), gel(rr, 2)),
                               gel(li,3), gel(li,4));
    }
  }
  setlg(list2,j);
  return gerepilecopy(ltop, list2);
}

static GEN
projratpoint2(GEN pol, long lim)
{
  pari_sp ltop = avma;
  GEN list = listratpoint(pol);
  long i, l = lg(list);
  for (i = 1; i < l; ++i)
  {
    GEN li = gel(list, i);
    GEN rat = projratpoint(gel(li, 1), lim), y2, aux;
    if (!rat) continue;
    y2 = gmul(gel(rat, 2), gel(li, 4));
    aux = mkcol2(gel(rat, 1), gel(rat, 3));
    aux = gmul(gel(li, 2), aux);
    if (signe(gel(aux, 2))==0)
      rat = mkvec3(gel(aux, 1), y2, gen_0);
    else
      rat = mkvec3(gdiv(gel(aux, 1), gel(aux, 2)),
            gdiv(y2, gpowgs(gel(aux, 2), degpol(pol)>>1)), gen_1);
    return gerepilecopy(ltop, rat);
  }
  return gc_NULL(ltop);
}

static GEN
polrootsmodpn(GEN pol, GEN p)
{
  pari_sp av = avma, av2;
  long j, l, i = 1, vd = Z_pval(ZX_disc(pol), p);
  GEN v, r, P = gpowers0(p, vd-1, p);

  av2 = avma;
  v = FpX_roots(pol, p); l = lg(v);
  for (j = 1; j < l; j++) gel(v,j) = mkvec2(gel(v,j), gen_1);
  while (i < lg(v))
  {
    GEN pol2, pe, roe = gel(v, i), ro = gel(roe,1);
    long e = itou(gel(roe,2));

    if (e >= vd) { i++; continue; }
    pe = gel(P, e);
    pol2 = ZX_unscale(ZX_translate(pol, ro), pe);
    (void)ZX_pvalrem(pol2, p, &pol2);
    r = FpX_roots(pol2, p); l = lg(r);
    if (l == 1) { i++; continue; }
    for (j = 1; j < l; j++)
      gel(r, j) = mkvec2(addii(ro, mulii(pe, gel(r, j))), utoi(e + 1));
    /* roots with higher precision = ro + r*p^(e+1) */
    if (l > 2) v = shallowconcat(v, vecslice(r, 2, l-1));
    gel(v, i) = gel(r, 1);
    if (gc_needed(av2, 1)) gerepileall(av2, 1, &v);
  }
  return gerepilecopy(av, v);
}

/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */
/*    FUNCTIONS FOR LOCAL COMPUTATIONS         \\ */
/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */

static GEN
kpmodsquares1(GEN nf, GEN z, GEN modpr, GEN pstar)
{
  GEN pr = modpr_get_pr(modpr), p = pr_get_p(pr);
  long v = nfvalrem(nf, z, pr, &z);
  if (equaliu(p, 2))
  {
    GEN c = ZV_to_Flv(ideallog(nf, z, pstar), 2);
    return vecsmall_prepend(c, odd(v));
  }
  else
  {
    GEN T = modpr_get_T(modpr);
    long c = !Fq_issquare(nf_to_Fq(nf, z, modpr), T, p);
    return mkvecsmall2(odd(v), c);
  }
}

static GEN
kpmodsquares(GEN vnf, GEN z, GEN pr, GEN pstar)
{
  pari_sp ltop = avma;
  long i, j, l = lg(vnf);
  GEN vchar = cgetg(l, t_VEC);
  for (i = 1; i < l; ++i)
  {
    GEN pri = gel(pr, i), nf = gel(vnf, i);
    long lp = lg(pri);
    GEN delta = RgX_rem(z, nf_get_pol(nf));
    GEN kp = cgetg(lp, t_VEC);
    for (j = 1; j < lp; ++j)
    {
      GEN prij = gel(pri, j);
      GEN psj = equaliu(modpr_get_p(prij), 2) ? gmael(pstar, i, j): NULL;
      gel(kp, j) = kpmodsquares1(nf, delta, prij, psj);
    }
    gel(vchar, i) = shallowconcat1(kp);
  }
  return gerepilecopy(ltop, shallowconcat1(vchar));
}

static GEN
veckpmodsquares(GEN x, GEN vnf, GEN pr, GEN pstar)
{ pari_APPLY_type(t_MAT,kpmodsquares(vnf, gel(x, i), pr, pstar)) }

static int
Qp_issquare(GEN a, GEN p)
{
  if (typ(a)==t_INT) return Zp_issquare(a, p);
  return Zp_issquare(mulii(gel(a,1), gel(a,2)), p);
}

/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */
/*    GENERIC FUNCTIONS FOR ELLIPTIC CURVES    \\ */
/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */

static GEN
ellabs(GEN P)
{
  return ell_is_inf(P) ? P: mkvec2(gel(P,1), Q_abs(gel(P,2)));
}

static GEN
vecellabs(GEN x)
{ pari_APPLY_same(ellabs(gel(x,i))) }

static GEN
elltwistequation(GEN ell, GEN K)
{
  GEN K2, K3;
  if (!K || equali1(K))
    return ell;
  K2 = sqri(K); K3 = mulii(K, K2);
  return ellinit(mkvec5(gen_0, mulii(ell_get_a2(ell), K),
                gen_0, mulii(ell_get_a4(ell), K2),
                mulii(ell_get_a6(ell), K3)), NULL, DEFAULTPREC);
}

static GEN
elltwistpoint(GEN P, GEN K, GEN K2)
{
  if (ell_is_inf(P)) return ellinf();
  return mkvec2(gmul(gel(P, 1), K), gmul(gel(P, 2), K2));
}

static GEN
elltwistpoints(GEN x, GEN K)
{
  GEN K2;
  if (!K || equali1(K)) return x;
  K2 = gsqr(K);
  pari_APPLY_same(elltwistpoint(gel(x,i), K, K2))
}

static GEN
ellredgen(GEN ell, GEN listgen, GEN K, long prec)
{
  pari_sp ltop = avma;
  GEN ell_K, listgenK;
  if (!K)
    K = gen_1;
  ell_K = elltwistequation(ell, K);
  listgenK = elltwistpoints(listgen, K);
  ell_K = ellinit(ell_K, NULL, prec);
  listgen = ellQ_genreduce(ell_K, listgenK, prec);
  listgen = vecellabs(listgen);
  listgen = elltwistpoints(listgen, ginv(K));
  return gerepilecopy(ltop, listgen);
}

/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */
/*    FUNCTIONS FOR NUMBER FIELDS              \\ */
/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */

static GEN
bestS(GEN bnf,GEN S, ulong p)
{
  pari_sp av = avma;
  long i, lS = S ? lg(S): 1, lS2 = 1;
  ulong l, vD;
  forprime_t P;
  GEN v, w, S2;
  w = cgetg(lS+1,t_VEC);
  gel(w,1) = diagonal(bnf_get_cyc(bnf));
  for (i = 1; i < lS; i++)
    gel(w,i+1) = bnfisprincipal0(bnf,gel(S,i),0);
  v = shallowconcat1(w);
  v = ZM_hnf(v);
  vD = Z_lval(ZM_det(v), p);
  if (!vD) { set_avma(av); return cgetg(1, t_VEC); }
  S2 = cgetg(vD+2, t_VEC);
  u_forprime_init(&P,2,ULONG_MAX);
  while ((l = u_forprime_next(&P)))
  {
    GEN w, Sl = idealprimedec(bnf, utoi(l));
    long lSl = lg(Sl);
    ulong vDl;
    for (i = 1; i<lSl; i++)
    {
      w = ZM_hnf(shallowconcat(v, bnfisprincipal0(bnf,gel(Sl,i),0)));
      vDl = Z_lval(ZM_det(w), p);
      if (vDl < vD)
      {
        gel(S2,lS2++) = gel(Sl,i);
        vD = vDl; v = w;
        if (!vD) { setlg(S2, lS2); return gerepilecopy(av,S2); }
      }
    }
  }
  return NULL;/*LCOV_EXCL_LINE*/
}

static GEN
nfC_pridV_val(GEN nf, GEN G, GEN P)
{
  long i, j, lG = lg(G), lP = lg(P);
  GEN M = cgetg(lG, t_MAT);
  for (i=1; i<lG; i++)
  {
    GEN V = cgetg(lP, t_COL);
    for(j=1; j<lP; j++)
      gel(V,j) = gpnfvalrem(nf,gel(G,i),gel(P,j),NULL);
    gel(M,i) = V;
  }
  return M;
}

static GEN
nffactorbackmod(GEN nf, GEN x, ulong p)
{ return nffactorback(nf, gel(x,1), ZV_to_Flv(gel(x,2), p)); }

static GEN
nfV_factorbackmod(GEN nf, GEN x, ulong p)
{ pari_APPLY_type(t_VEC,nffactorbackmod(nf, gel(x,i), p)) }

static GEN
nfV_Flm_factorbackmod(GEN nf, GEN G, GEN x, ulong p)
{ pari_APPLY_type(t_VEC,nffactorback(nf, G, gel(x,i))) }

static GEN
pridV_ZM_factorback(GEN nf, GEN S, GEN x)
{ pari_APPLY_type(t_VEC,idealfactorback(nf, S, gel(x,i),0)) }

static GEN
nfV_redmodpower(GEN nf, GEN x, long n)
{ pari_APPLY_same(nfmul(nf, gel(x,i), nfsqr(nf, idealredmodpower(nf, gel(x,i), n, 0)))) }

static GEN
bnfselmer(GEN bnf, GEN S, ulong p)
{
  pari_sp av = avma;
  GEN nf, S2, S3;
  GEN e, f, e2;
  GEN kerval, LS2gen, LS2fu, LS2all;
  long lS = S? lg(S)-1: 0, lS3, lS2all, r;
  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  if (S && !is_vec_t(typ(S))) pari_err_TYPE("bnfselmer",S);
  S2 = dvdiu(bnf_get_no(bnf), p)? bestS(bnf, S, p): cgetg(1,t_VEC);
  S3 = S ? shallowconcat(S, S2): S2;
  LS2all = gel(bnfunits(bnf, S3), 1);
  LS2all = nfV_factorbackmod(nf, LS2all, p);
  LS2all = nfV_redmodpower(nf, LS2all, p);
  lS3 = lg(S3)-1; lS2all = lg(LS2all)-1; r = lS2all - lS3 - 1;
  LS2gen = vecslice(LS2all,1,lS3);
  LS2fu  = vecslice(LS2all,lS3+1, lS2all-1);
  e2 = nfC_pridV_val(nf, LS2gen, S2);
  kerval = Flm_ker(ZM_to_Flm(e2, p), p);
  LS2gen = nfV_Flm_factorbackmod(nf, LS2gen, kerval, p);
  e =  S ? nfC_pridV_val(nf, LS2gen, S): zeromat(0,lS3);
  e2 = ZM_divexactu(ZM_zm_mul(e2, kerval), p);
  f = pridV_ZM_factorback(nf, S2, e2);
  LS2gen = shallowconcat(LS2fu, LS2gen);
  e = shallowconcat(zeromat(lS, r), e);
  f = shallowconcat(const_vec(r, gen_1), f);
  if (bnf_get_tuN(bnf) % p == 0)
  {
    LS2gen = shallowconcat( mkvec(bnf_get_tuU(bnf)), LS2gen);
    e = shallowconcat(zeromat(lS, 1),e);
    f = shallowconcat(mkvecs(1),f);
  }
  return gerepilecopy(av, mkvec3(LS2gen,e,f));
}
static GEN
nf2selmer_quad(GEN nf, GEN S)
{
  pari_sp ltop = avma;
  GEN SlistQ, QS2gen, LS2gen2;
  GEN D = nf_get_disc(nf), factD = nf_get_ramified_primes(nf);
  GEN Hlist, H, KerH, norms;
  GEN LS2gen, chpol, Q;
  GEN kerval, S2, e2, G;
  long lQS2gen, lHlist, lLS2gen;
  GEN e, f, b, c;
  long i, j, k;
  long lS = lg(S), lkerH, lS2, lkerval;
  SlistQ = cgetg(lS, t_VEC);
  for (i = 1; i < lS; ++i)
    gel(SlistQ, i) = pr_get_p(gel(S, i));
  SlistQ = ZV_sort_uniq(SlistQ);
  QS2gen = shallowconcat(gen_m1, SlistQ);
  Hlist = ZV_sort_uniq(shallowconcat1(mkvec3(mkvec(gen_2), factD, SlistQ)));
  lQS2gen = lg(QS2gen);
  lHlist = lg(Hlist);
  H = cgetg(lQS2gen, t_MAT);
  for (j = 1; j < lQS2gen; ++j)
  {
    GEN v = cgetg(lHlist, t_VECSMALL);
    for (i = 1; i < lHlist; ++i)
      v[i] = hilbert(D, gel(QS2gen, j), gel(Hlist, i)) < 0;
    gel(H, j) = Flv_to_F2v(v);
  }
  KerH = F2m_ker(H); lkerH = lg(KerH);
  norms = cgetg(lkerH, t_VEC);
  for (i = 1; i < lkerH; ++i)
    gel(norms, i) = factorback2(QS2gen, F2c_to_ZC(gel(KerH, i)));
  LS2gen = cgetg(lkerH, t_VEC);
  chpol = QXQ_charpoly(gel(nf_get_zk(nf), 2), nf_get_pol(nf), 0);
  b = gdivgs(gneg(gel(chpol, 3)), 2);
  c = gel(chpol, 2);
  Q = mkmat3(mkcol3(gen_1,b,gen_0),
             mkcol3(b,c,gen_0),
             mkcol3(gen_0,gen_0,gen_0));
  for (k = 1; k < lkerH; ++k)
  {
    GEN sol;
    gcoeff(Q, 3, 3) = gneg(gel(norms, k));
    sol = qfsolve(Q);
    if (typ(sol) == t_INT)
      pari_err_BUG(" nf2selmer_quad: unsolvable quadratic form");
    sol = mkcol2(gel(sol, 1), gel(sol, 2));
    sol = gdiv(sol, ZV_content(sol));
    gel(LS2gen, k) = basistoalg(nf, sol);
  }
  G = ZV_sort_uniq(shallowconcat1(mkvec3(mkvec(gen_m1), factD, SlistQ)));
  if (gequalgs(D, -4))
    G = setminus(G, mkvec(gen_m1));
  else
    G = setminus(G, mkvec(gel(factD, lg(factD)-1)));
  LS2gen = shallowconcat(G, LS2gen);
  if (lg(SlistQ) > 1)
  {
    long lSlistQ = lg(SlistQ);
    S2 = cgetg(lSlistQ, t_VEC);
    for (i = 1; i < lSlistQ; ++i)
      gel(S2, i) = idealprimedec(nf, gel(SlistQ, i));
    S2 = setminus(shallowconcat1(S2), S);
  }
  else
    S2 = cgetg(1, t_VEC);
  lLS2gen = lg(LS2gen);
  lS2 = lg(S2);
  e2 = cgetg(lLS2gen, t_MAT);
  for (i = 1; i < lLS2gen; ++i)
  {
    GEN v = cgetg(lS2, t_VECSMALL);
    for (j = 1; j < lS2; ++j)
      v[j] = odd(idealval(nf, gel(LS2gen, i), gel(S2, j)));
    gel(e2, i) = Flv_to_F2v(v);
  }
  kerval = F2m_ker(e2); lkerval = lg(kerval);
  LS2gen2 = cgetg(lkerval, t_VEC);
  for (i = 1; i < lkerval; ++i)
    gel(LS2gen2, i) = nffactorback(nf,LS2gen, F2c_to_ZC(gel(kerval, i)));
  LS2gen = LS2gen2;
  e = cgetg(lkerval, t_MAT);
  for (i = 1; i < lkerval; ++i)
  {
    gel(e, i) = cgetg(lS, t_COL);
    for (j = 1; j < lS; ++j)
      gcoeff(e, j, i) = stoi(idealval(nf, gel(LS2gen, i), gel(S, j)));
  }
  f = cgetg(lkerval, t_VEC);
  for (i = 1; i < lkerval; ++i)
  {
    GEN id = idealdiv(nf, gel(LS2gen, i), idealfactorback(nf, S, gel(e, i), 0));
    if (!idealispower(nf, id, 2, &gel(f, i)))
      pari_err_BUG("nf2selmer_quad");
  }
  return gerepilecopy(ltop, mkvec3(LS2gen, e, f));
}

static GEN
makevbnf(GEN ell, long prec)
{
  GEN vbnf, P = gel(factor(ell2pol(ell)), 1);
  long k, l = lg(P);
  vbnf = cgetg(l, t_VEC);
  for (k = 1; k < l; k++)
  {
    GEN t = gel(P,k);
    gel(vbnf,k) = degpol(t) == 2 ? nfinit(t, prec): Buchall(t, nf_FORCE, prec);
  }
  return vbnf;
}

static GEN
bnfpselmer(GEN bnf, GEN S, ulong p)
{
  if (lg(bnf)==10 && p==2)
    return nf2selmer_quad(bnf, S);
  else
    return bnfselmer(bnf, S, p);
}

static GEN
kernorm(GEN gen, GEN S, ulong p, GEN pol)
{
  long i, j, lG = lg(gen), lS;
  GEN normmap = cgetg(lG, t_MAT);
  if (p == 2) S = vec_prepend(S, gen_m1);
  lS = lg(S);
  for (j = 1; j < lG; ++j)
  {
    GEN nj = QXQ_norm(gel(gen,j), pol);
    GEN v = cgetg(lS, t_VECSMALL);
    for (i = 1; i < lS; ++i)
      v[i] =  (i == 1 && p==2) ? gsigne(nj) < 0
                               : smodss(Q_pval(nj, gel(S, i)), p);
    gel(normmap, j) = v;
  }
  return Flm_ker(normmap, p);
}

/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */
/*    FUNCTIONS FOR 2-DESCENT                  \\ */
/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */

static GEN
elllocalimage(GEN pol, GEN K, GEN vnf, GEN pp, GEN ppstar, GEN pts)
{
  pari_sp ltop = avma;
  GEN p = modpr_get_p(gmael(pp, 1, 1));
  long p2, lpp = lg(pp);
  long i, prank, attempt = 0;
  GEN root, bound;
  if (!pts)
    pts = cgetg(1, t_MAT);
  p2 = 0;
  for (i = 1; i < lpp; ++i)
    p2 += lg(gel(pp, i))-1;
  prank = p2 - !gequalgs(p, 2);
  root = polrootsmodpn(gmul(K, pol), p);
  bound = addiu(p, 6);
  while (Flm_rank(pts, 2) < prank)
  {
    pari_sp btop;
    GEN xx, y2, delta, deltamodsquares;
    attempt++;
    if (attempt%16==0)
    {
      pts = Flm_image(pts, 2);
      bound = mulii(bound, p);
    }
    btop = avma;
    do
    {
      GEN r = gel(root, random_Fl(lg(root)-1)+1);
      long pprec = random_Fl(itou(gel(r, 2)) + 3) - 2;
      set_avma(btop);
      xx = gadd(gel(r, 1), gmul(powis(p, pprec), randomi(bound)));
      y2 = gmul(K, poleval(pol, xx));
    } while (gequal0(y2) || !Qp_issquare(y2, p));
    delta = gmul(K, gsub(xx, pol_x(0)));
    deltamodsquares = kpmodsquares(vnf, delta, pp, ppstar);
    pts = vec_append(pts, deltamodsquares);
  }
  pts = Flm_image(pts,2);
  return gerepilecopy(ltop, pts);
}

static GEN
ellLS2image(GEN pol, GEN listpoints, GEN K, GEN vpol)
{
  pari_sp ltop = avma;
  GEN LS2image, var;
  long i, l = lg(listpoints);
  if (l == 1)
    return cgetg(1, t_VEC);
  var = pol_x(varn(pol));
  LS2image = cgetg(l, t_VEC);
  for (i = 1; i < l; ++i)
  {
    GEN point = gel(listpoints, i);
    GEN px = gel(point,1), py = gel(point,2);
    if (ell_is_inf(point))
    {
      gel(LS2image, i) = gen_1;
      continue;
    }
    if (!gequal0(py))
      gel(LS2image, i) = gmul(K, gsub(px, var));
    else
    {
      long k, lp = lg(vpol);
      GEN aux = cgetg(lp, t_VEC);
      for (k = 1; k < lp; ++k)
      {
        gel(aux, k) = signe(poleval(gel(vpol, k), px))==0 ?
          ZX_deriv(pol): gmul(K, gsub(px, var));
        gel(aux, k) = gmodulo(gel(aux, k), gel(vpol, k));
      }
      gel(LS2image, i) = lift(chinese1(aux));
    }
  }
  return gerepilecopy(ltop, LS2image);
}

static GEN
ellsearchtrivialpoints(GEN ell, GEN lim, GEN help)
{
  pari_sp ltop = avma;
  GEN torseven = gtoset(gel(elltors_psylow(ell,2), 3));
  GEN triv = ellratpoints(ell, lim, 0);
  if (help)
    triv = shallowconcat(triv, help);
  triv = gtoset(vecellabs(triv));
  triv = setminus(triv, torseven);
  return gerepilecopy(ltop, mkvec2(torseven, triv));
}

GEN
ellrankinit(GEN ell, long prec)
{
  pari_sp av = avma;
  GEN urst;
  checkell_Q(ell);
  ell = ellintegralbmodel(ell, &urst);
  return gerepilecopy(av, mkvec3(ell, urst, makevbnf(ell, prec)));
}

INLINE GEN
ZV_isneg(GEN x)
{ pari_APPLY_long(signe(gel(x,i))<0) }

static void
check_ell2descent(GEN ell, GEN help, GEN K)
{
  checkell(ell);
  if (gequal0(K))
    pari_err(e_MISC, "ell2descent: twist by 0");
  if (typ(K) != t_INT)
    pari_err(e_MISC, "ell2descent: nonintegral quadratic twist");
  if (!gequalgs(ell_get_a1(ell), 0) || !gequalgs(ell_get_a3(ell), 0))
  {
    if (!gequalgs(K, 1))
      pari_err(e_MISC, "ell2descent: quadratic twist only allowed for a1=a3=0");
  }
}

static void
ell2descent1_checks(GEN ell, GEN help, GEN K)
{
  check_ell2descent(ell, help, K);
  if (!gequalgs(ell_get_a1(ell), 0))
    pari_err(e_MISC, "ell2descent1: nonzero coefficient a1");
  if (!gequalgs(ell_get_a3(ell), 0))
    pari_err(e_MISC, "ell2descent1: nonzero coefficient a3");
  if (((typ(ell_get_a2(ell)) != t_INT) || (typ(ell_get_a4(ell)) != t_INT)) || (typ(ell_get_a2(ell)) != t_INT))
    pari_err(e_MISC, "ell2descent1: nonintegral model");
}

static GEN
selmersign(GEN x, GEN vpol, GEN L)
{ pari_APPLY_same(ZV_isneg(nfeltsign(gel(x, i), RgX_rem(L, gel(vpol, i)), NULL))) }

static GEN
vecselmersign(GEN vnf, GEN vpol, GEN x)
{ pari_APPLY_type(t_VEC, shallowconcat1(selmersign(vnf, vpol, gel(x, i)))) }

static GEN
tracematrix(GEN zc, GEN base, GEN T, GEN dT)
{
  long i, j;
  GEN q2 = cgetg(4, t_MAT);
  for (j = 1; j <= 3; ++j)
  {
    gel(q2, j) = cgetg(4, t_COL);
    for (i = 1; i <= 3; ++i)
      gcoeff(q2, i, j) = RgXQ_trace(
        QXQ_div(gmul(zc, QXQ_mul(gel(base, i), gel(base, j), T)), dT, T),T);
  }
  return q2;
}

static GEN
RgXV_cxeval(GEN x, GEN z)
{ pari_APPLY_same(RgX_cxeval(gel(x,i), z, NULL)) }

static GEN
redquadric(GEN base, GEN q2, GEN pol, GEN zc)
{
  GEN m = vecmax(gabs(RgM_Rg_div(q2, content(q2)),DEFAULTPREC));
  long prec = nbits2prec(2*expi(m))+1;
  GEN r = roots(pol, prec);
  long i, l = lg(r);
  GEN s = NULL;
  for (i = 1; i < l; ++i)
  {
    GEN v = RgXV_cxeval(base, gel(r, i));
    GEN N = gabs(RgX_cxeval(zc, gel(r, i), NULL), prec);
    GEN M = real_i(RgC_RgV_mul(RgV_Rg_mul(v,N), gconj(v)));
    s = s ? RgM_add(s, M): M;
  }
  return lllgram(s);
}

static GEN
vecnfmodprinit(GEN nf, GEN x)
{ pari_APPLY_same(nfmodprinit(nf, gel(x, i))) }

static GEN
RgX_homogenous_evaldeg(GEN P, GEN A, GEN B)
{
  long i, d = degpol(P), e = lg(B)-1;
  GEN s = gmul(gel(P, d+2), gel(B,e-d));
  for (i = d-1; i >= 0; i--)
    s = gadd(gmul(s, A), gmul(gel(B,e-i), gel(P,i+2)));
  return s;
}

static GEN
RgXV_homogenous_evaldeg(GEN x, GEN a, GEN b)
{ pari_APPLY_same(RgX_homogenous_evaldeg(gel(x,i), a, b)) }

static GEN
ZC_shifti(GEN x, long n)
{ pari_APPLY_type(t_COL, shifti(gel(x,i),n)) }

static void
check_oncurve(GEN ell, GEN V)
{
  long i, l = lg(V);
  for(i = 1; i < l; i++)
  {
    GEN vi = gel(V, i);
    if (lg(vi)!=3 || !oncurve(ell,vi))
      pari_err_TYPE("ellrank",vi);
  }
}

static GEN
smallbasis1(GEN nf, GEN polinv, GEN pol)
{
  pari_sp av = avma;
  GEN vpol = nf_get_pol(nf), zk = nf_get_zk(nf);
  long i, l = lg(zk);
  GEN b = cgetg(l, t_COL);
  for (i = 1; i < l; ++i)
  {
    GEN z = nf_to_scalar_or_alg(nf, gel(zk, i));
    if (typ(z) != t_POL) z = scalarpol(z, 0);
    gel(b, i) = RgX_chinese_coprime(z, pol_0(0), vpol, polinv, pol);
  }
  return gerepilecopy(av, b);
}

static GEN
vecsmallbasis(GEN x, GEN vpolinv, GEN pol)
{ pari_APPLY_same(smallbasis1(gel(x, i), gel(vpolinv, i), pol)) }

static GEN
selmerbasis(GEN nf, GEN LS2k, GEN expo, GEN sqrtLS2, GEN factLS2,
            GEN badprimes, GEN polinv, GEN pol)
{
  pari_sp av = avma;
  GEN b, vpol = nf_get_pol(nf);
  long i, l;
  GEN expok = vecslice(expo, LS2k[1], LS2k[2]);
  GEN sqrtzc = idealfactorback(nf, sqrtLS2, zv_neg(expok), 0);
  GEN exposqrtzc = ZC_shifti(ZM_zc_mul(factLS2, expok), -1);
  if (!gequal0(exposqrtzc))
    sqrtzc = idealmul(nf, sqrtzc,
        idealfactorback(nf, badprimes, gneg(exposqrtzc), 0));
  sqrtzc = idealhnf(nf, sqrtzc);
  l = lg(sqrtzc);
  b = cgetg(l, t_COL);
  for (i = 1; i < l; ++i)
  {
    GEN z = nf_to_scalar_or_alg(nf, gel(sqrtzc, i));
    if (typ(z) != t_POL) z = scalarpol(z, 0);
    gel(b, i) = RgX_chinese_coprime(z, pol_0(0), vpol, polinv, pol);
  }
  return gerepilecopy(av, b);
}

static GEN
liftselmer(GEN vec, GEN vnf, GEN sbase, GEN LS2k, GEN LS2, GEN sqrtLS2, GEN factLS2,
           GEN badprimes, GEN vpolinv, GEN pol, GEN selmer, GEN K, long lim, long ntry)
{
  pari_sp av = avma, av2;
  long n = lg(vnf)-1, k, t;
  GEN expo, z, base, polprime;
  expo = Flm_Flc_mul(selmer, vec, 2);
  base = cgetg(n+1, t_VEC);
  for (k = 1; k <= n; k++)
    gel(base,k) = selmerbasis(gel(vnf, k), gel(LS2k,k), expo, gel(sqrtLS2, k),
        gel(factLS2, k), gel(badprimes, k), gel(vpolinv, k), pol);
  base = shallowconcat1(base);
  polprime = ZX_deriv(pol);
  z = RgXQV_factorback(LS2, expo, pol);
  av2 = avma;
  for (t = 1; t <= ntry; t++)
  {
    GEN ttheta, q1, pol4, redq, den, point;
    GEN tttheta, q0, pointxx, point2;
    GEN xx, yy, zz, R, x2, y2, z2;
    GEN rd, zc, q2, change;
    GEN sol, param, newbase;
    if (t==1) zc = z;
    else
    {
      do rd = RgV_dotproduct(sbase,mkcol3s(random_Fl(127)-63, random_Fl(127)-63, random_Fl(127)-63));
      while (degpol(ZX_gcd(rd,pol))!=0);
      zc = RgXQ_mul(z, RgXQ_sqr(rd,pol), pol);
    }
    q2 = tracematrix(zc, base, pol, polprime);
    change = redquadric(base, q2, pol, QXQ_div(zc, polprime, pol));
    if (lg(change) < 4) { set_avma(av2); continue; }
    q2 = qf_apply_RgM(q2, change);
    newbase = RgV_RgM_mul(base, change);
    sol = qfsolve(gdiv(q2, content(q2)));
    param = gmul(qfparam(q2, sol, 0), mkcol3(pol_xn(2,0), pol_x(0), pol_1(0)));
    param = gdiv(param, content(param));
    ttheta = RgX_shift_shallow(pol,-2);
    q1 = RgM_neg(tracematrix(RgXQ_mul(zc, ttheta, pol), newbase, pol, polprime));
    redq = hyperellreduce(qfeval(q1, param));
    pol4 = gel(redq, 1); R = gel(redq, 2);
    den = denom(content(gmul(K, pol4)));
    pol4 = gmul(pol4, sqri(den));
    if (DEBUGLEVEL >= 2)
      err_printf("  reduced quartic: %Ps*Y^2 = %Ps\n", K, pol4);
    point = projratpoint(gmul(K, pol4), lim);
    if (!point)
      point = projratpoint2(gmul(K, pol4), lim);
    if (!point) { set_avma(av2); continue; }
    x2 = gel(point, 1); y2 = gel(point, 2); z2 = gel(point, 3);
    point = RgM_RgC_mul(R, mkcol2(x2, z2));
    xx = gel(point,1); yy = gel(point,2); zz = gdiv(y2, den);
    if (gequal0(zz))
      pari_err_BUG("ell2selmer: wrong point");
    param = RgXV_homogenous_evaldeg(param, xx, gpowers(yy, 2));
    param = gmul(param, gdiv(K, zz));
    tttheta = RgX_shift_shallow(pol, -1);
    q0 = tracematrix(RgXQ_mul(zc, tttheta, pol), newbase, pol, polprime);
    pointxx = gdiv(qfeval(q0, param), K);
    point2 = mkvec2(pointxx,sqrtrat(gdiv(poleval(pol, pointxx), K)));
    if (DEBUGLEVEL) err_printf("Found point: %Ps\n",point2);
    return gerepilecopy(av, point2);
  }
  return gc_NULL(av);
}

static GEN
ell2selmer(GEN ell, GEN help, GEN K, GEN vbnf, long effort, long prec)
{
  pari_sp ltop = avma, btop;
  GEN pol;
  GEN ell_K = gen_0, torseven;
  long i, j, k;
  GEN vnf, vpol, vpolinv, vroots, vr1, sbase;
  GEN factdisc, badprimes;
  GEN LS2, factLS2, sqrtLS2, LS2k;
  GEN selmer, helpLS2, LS2chars, helpchars, newselmer;
  GEN  triv, helplist, listpoints;
  long tr1, n, tors2, mwrank;
  long dimselmer, nbpoints, lfactdisc, lhelp;
  long t, u;
  if (!K) K = gen_1;
  ell2descent1_checks(ell, help, K);
  /* Equations of the curve */
  pol = ell2pol(ell);
  ell_K = elltwistequation(ell, K);
  if (help)
  {
    check_oncurve(ell, help);
    help = elltwistpoints(help, K);
  }
  triv = ellsearchtrivialpoints(ell_K, muluu(LIMTRIV,(effort+1)), help);
  torseven = gel(triv, 1); help = gel(triv, 2);
  torseven = elltwistpoints(torseven, ginv(K));
  help = elltwistpoints(help, ginv(K));
  help = shallowconcat(torseven, help);
  ell = ellinit(ell, NULL, prec);
  tors2 = lg(torseven) - 1;
  n = tors2+1;
  if (lg(vbnf)-1 != n)
    pari_err_TYPE("ell2selmer",vbnf);
  vnf = cgetg(n+1, t_VEC);
  vpol = cgetg(n+1, t_VEC);
  vpolinv = cgetg(n+1, t_VEC);
  vroots = cgetg(n+1, t_VEC);
  vr1 = cgetg(n+1, t_VECSMALL);
  for (k = 1; k <= n; ++k)
  {
    gel(vnf, k) = checknf(gel(vbnf, k));
    gel(vpol, k) = nf_get_pol(gel(vnf, k));
    gel(vpolinv, k) = RgX_div(pol, gel(vpol, k));
    gel(vroots, k) = nf_get_roots(gel(vnf, k));
    uel(vr1, k) = nf_get_r1(gel(vnf, k));
  }
  sbase = shallowconcat1(vecsmallbasis(vnf, vpolinv, pol));
  factdisc = mkvec3(mkcols(2),
    gel(absZ_factor(ZX_disc(pol)), 1),
    gel(absZ_factor(K), 1));
  factdisc = ZV_sort_uniq(shallowconcat1(factdisc));
  badprimes = cgetg(n+1, t_VEC);
  for (k = 1; k <= n; k++)
  {
    GEN nf = gel(vnf, k);
    GEN id = idealadd(nf, nf_get_index(nf), ZX_deriv(gel(vpol, k)));
    GEN f = mkvec3(K, gel(vpolinv, k), id);
    for (i = 1; i <= 3; i++)
      gel(f,i) = gel(idealfactor(nf, gel(f,i)), 1);
    gel(badprimes, k) = gtoset(shallowconcat1(f));
  }
  if (DEBUGLEVEL >= 3)
    err_printf("   local badprimes = %Ps\n", badprimes);
  LS2 = cgetg(n+1, t_VEC);
  factLS2 = cgetg(n+1, t_VEC);
  sqrtLS2 = cgetg(n+1, t_VEC);
  for (k = 1; k <= n; k++)
  {
    GEN sel = bnfpselmer(gel(vbnf, k), gel(badprimes, k), 2);
    gel(LS2, k) = gel(sel, 1);
    gel(factLS2, k) = gel(sel, 2);
    gel(sqrtLS2, k) = gel(sel, 3);
  }
  LS2k = cgetg(n+1, t_VEC);
  for (k = 1; k <= n; ++k)
  {
    long s = 0, t;
    for (i = 1; i < k; i++)
      s += lg(gel(LS2, i))-1;
    t = s + lg(gel(LS2, i))-1;
    gel(LS2k, k) = mkvecsmall2(1+s,t);
  }
  for (k = 1; k <= n; k++)
  {
    long i, lk = lg(gel(LS2, k));
    for (i = 1; i < lk; ++i)
    {
      GEN z = nf_to_scalar_or_alg(gel(vnf, k), gmael(LS2, k, i));
      if (typ(z)!=t_POL) z = scalarpol(z, 0);
      gmael(LS2, k, i) = RgX_chinese_coprime(z, pol_1(0), gel(vpol,k), gel(vpolinv,k), pol);
    }
  }
  LS2 = shallowconcat1(LS2);
  helpLS2 = ellLS2image(pol, help, K, vpol);
  selmer = kernorm(LS2, factdisc, 2, pol);
  tr1 = 0;
  for (k = 1; k <= n; k++) tr1 +=  vr1[k];
  LS2chars = vecselmersign(vnf, vpol, LS2);
  helpchars = vecselmersign(vnf, vpol, helpLS2);
  if (tr1 == 3)
  {
    GEN signs;
    long row;
    if (signe(K) > 0)
    {
      long kmin = 1;
      for (k = 2; k <= n; ++k)
        if (cmprr(gmael(vroots,k,1), gmael(vroots,kmin,1))<0)
          kmin = k;
      row = 1;
      for (k = 1; k < kmin; k++) row += vr1[k];
    }
    else
    {
      long kmax = 1;
      for (k = 2; k <= n; ++k)
        if (cmprr(gmael(vroots,k,vr1[k]), gmael(vroots,kmax,vr1[k])) > 0)
          kmax = k;
      row = 0;
      for (k = 1; k <= kmax; k++) row += vr1[k];
    }
    signs = Flm_transpose(mkmat(Flm_row(LS2chars, row)));
    /* the signs of LS2 for this embedding */
    selmer = Flm_intersect(selmer, Flm_ker(signs, 2), 2);
  }
  btop = avma;
  lfactdisc = lg(factdisc);
  for (i = 1; i < lfactdisc; i++)
  {
    GEN ppstar, LS2image, helpimage, locimage;
    GEN p = gel(factdisc, i);
    GEN pp = cgetg(n+1, t_VEC);
    for (k = 1; k <= n; ++k)
      gel(pp, k) = vecnfmodprinit(gel(vnf, k), idealprimedec(gel(vnf, k), p));
    if (equaliu(p, 2))
    {
      ppstar = cgetg(n+1, t_VEC);
      for (k = 1; k <= n; ++k)
      {
        GEN ppk = gel(pp, k);
        long lppk = lg(ppk);
        GEN pk = cgetg(lppk, t_VEC);
        for (j = 1; j < lppk; ++j)
        {
          GEN pkj3 = gmael(ppk,j,3);
          gel(pk, j) = idealstar0(gel(vnf, k),
              idealpows(gel(vnf, k), pkj3, 1 + 2*pr_get_e(pkj3)), 1);
        }
        gel(ppstar, k) = pk;
      }
    } else ppstar = gen_0;
    LS2image = veckpmodsquares(LS2, vnf, pp, ppstar);
    LS2chars = vconcat(LS2chars, LS2image);
    helpimage = veckpmodsquares(helpLS2, vnf, pp, ppstar);
    helpchars = vconcat(helpchars, helpimage);
    locimage = elllocalimage(pol, K, vnf, pp, ppstar, helpimage);
    locimage = Flm_intersect(LS2image, locimage, 2);
    selmer = Flm_intersect(selmer, shallowconcat(Flm_ker(LS2image,2),
                                                 Flm_invimage(LS2image, locimage,2)), 2);
    dimselmer = lg(selmer)-1;
    if (dimselmer == Flm_rank(helpimage,2))
      break;
    if (i==lfactdisc-1 && Flm_rank(Flm_mul(LS2chars, selmer, 2), 2) < dimselmer)
    {
      long B = 10;
      GEN sp;
      do
      {
        sp = setminus(primes(B), gtoset(factdisc));
        B *= 2;
      } while (lg(sp)==1);
      factdisc = shallowconcat(factdisc, gel(sp, 1));
      lfactdisc++;
    }
    if (gc_needed(btop, 1))
      gerepileall(btop, 4, &factdisc, &selmer, &LS2chars, &helpchars);
  }
  helplist = gel(Flm_indexrank(helpchars,2),2);
  help = shallowextract(help, helplist);
  helpchars = shallowextract(helpchars, helplist);
  helpLS2 = shallowextract(helpLS2, helplist);
  lhelp = lg(help);
  dimselmer = lg(selmer)-1;
  newselmer = cgetg(dimselmer+1, t_MAT);
  if (lhelp>1)
  {
    GEN M = Flm_mul(LS2chars, selmer, 2);
    for (i = 1; i < lhelp; ++i)
      gel(newselmer, i) = Flm_Flc_invimage(M, gel(helpchars, i), 2);
  }
  setlg(newselmer, lhelp);
  if (DEBUGLEVEL) err_printf("Selmer rank: %ld\n", dimselmer);
  listpoints = vec_lengthen(help, dimselmer);
  nbpoints = lg(help)-1;
  for (i=1; i <= dimselmer; ++i)
  {
    pari_sp btop = avma;
    GEN P, vec = vecsmall_ei(dimselmer, i);
    if (Flm_Flc_invimage(newselmer, vec, 2)) continue;
    P = liftselmer(vec, vnf, sbase, LS2k, LS2, sqrtLS2, factLS2, badprimes,
        vpolinv, pol, selmer, K, LIM1, 1);
    if (P)
    {
      gel(listpoints, ++nbpoints) = P;
      gel(newselmer, nbpoints) = vec;
      setlg(newselmer, nbpoints+1);
    } else set_avma(btop);
  }
  for (t=1, u=1; nbpoints < dimselmer && effort > 0; t++)
  {
    pari_sp btop = avma;
    GEN P, vec;
    do vec = random_Flv(dimselmer, 2);
    while (zv_equal0(vec) || Flm_Flc_invimage(newselmer, vec, 2));
    P = liftselmer(vec, vnf, sbase, LS2k, LS2, sqrtLS2, factLS2, badprimes,
        vpolinv, pol, selmer, K, u*LIM1, u);
    if (P)
    {
      gel(listpoints, ++nbpoints) = P;
      gel(newselmer, nbpoints) = vec;
      if (nbpoints>dimselmer) pari_err_BUG("nbpoints");
      setlg(newselmer, nbpoints+1);
    } else set_avma(btop);
    if (t==dimselmer) { t=0; u++; effort--; }
  }
  setlg(listpoints, nbpoints+1);
  mwrank = nbpoints - tors2;
  if (odd(dimselmer - mwrank - tors2))
    mwrank++;
  listpoints = vecslice(listpoints, 1+tors2, nbpoints);
  listpoints = ellredgen(ell, listpoints, K, prec);
  return gerepilecopy(ltop, mkvec3(stoi(mwrank),stoi(dimselmer-tors2), listpoints));
}

static GEN
ell2descent(GEN ell, GEN help, GEN K, long effort, long prec)
{
  pari_sp ltop = avma;
  GEN urst, mwrank, vbnf;
  if (!K)
    K = gen_1;
  if (lg(ell)==4 && typ(ell)==t_VEC)
  {
    vbnf = gel(ell,3); urst = gel(ell,2); ell = gel(ell,1);
    check_ell2descent(ell, help, K);
  }
  else
  {
    checkell_Q(ell);
    ell = ellintegralbmodel(ell, &urst);
    vbnf = makevbnf(ell, prec);
    check_ell2descent(ell, help, K);
  }
  if (help && urst)
     help = ellchangepoint(help, urst);
  mwrank = ell2selmer(ell, help, K, vbnf, effort, prec);
  if (urst)
    gel(mwrank, 3) = ellchangepoint(gel(mwrank, 3), ellchangeinvert(urst));
  return gerepilecopy(ltop, mwrank);
}

GEN
ellrank(GEN ell, long effort, GEN help, long prec)
{
  return ell2descent(ell, help, NULL, effort, prec);
}
