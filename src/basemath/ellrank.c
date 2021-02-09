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

static long LIM1 = 10000;
static long LIMTRIV = 10000;

/*******************************************************************/
/*               NFHILBERT and LOCAL SOLUBILITY                    */
/*     adapted from Denis Simon's original C limplementation       */
/*******************************************************************/
/* p > 2, T ZX, p prime, x t_INT */
static long
lemma6(GEN T, GEN p, long nu, GEN x)
{
  long la, mu;
  pari_sp av = avma;
  GEN gpx, gx = poleval(T, x);

  if (Zp_issquare(gx, p)) return gc_long(av,1);

  la = Z_pval(gx, p);
  gpx = poleval(ZX_deriv(T), x);
  mu = signe(gpx)? Z_pval(gpx,p)
                 : la+nu+1; /* mu = +oo */
  set_avma(av);
  if (la > mu<<1) return 1;
  if (la >= nu<<1 && mu >= nu) return 0;
  return -1;
}
/* p = 2, T ZX, x t_INT: return 1 = yes, -1 = no, 0 = inconclusive */
static long
lemma7(GEN T, long nu, GEN x)
{
  long odd4, la, mu;
  pari_sp av = avma;
  GEN gpx, oddgx, gx = poleval(T, x);

  if (Zp_issquare(gx,gen_2)) return 1;

  gpx = poleval(ZX_deriv(T), x);
  la = Z_lvalrem(gx, 2, &oddgx);
  odd4 = umodiu(oddgx,4); set_avma(av);

  mu = vali(gpx);
  if (mu < 0) mu = la+nu+1; /* mu = +oo */

  if (la > mu<<1) return 1;
  if (nu > mu)
  {
    long mnl = mu+nu-la;
    if (odd(la)) return -1;
    if (mnl==1) return 1;
    if (mnl==2 && odd4==1) return 1;
  }
  else
  {
    long nu2 = nu << 1;
    if (la >= nu2) return 0;
    if (la == nu2 - 2 && odd4==1) return 0;
  }
  return -1;
}

/* T a ZX, p a prime, pnu = p^nu, x0 t_INT */
static long
zpsol(GEN T, GEN p, long nu, GEN pnu, GEN x0)
{
  long i, res;
  pari_sp av = avma, btop;
  GEN x, pnup;

  res = absequaliu(p,2)? lemma7(T,nu,x0): lemma6(T,p,nu,x0);
  if (res== 1) return 1;
  if (res==-1) return 0;
  x = x0; pnup = mulii(pnu,p);
  btop = avma;
  for (i=0; i < itos(p); i++)
  {
    x = addii(x,pnu);
    if (zpsol(T,p,nu+1,pnup,x)) return gc_long(av,1);
    if (gc_needed(btop, 2))
    {
      x = gerepileupto(btop, x);
      if (DEBUGMEM > 1)
        pari_warn(warnmem, "hyperell_locally_soluble: %ld/%Ps",i,p);
    }
  }
  return gc_long(av,0);
}

/* return 1 if equation y^2=T(x) has a rational p-adic solution (possibly
 * infinite), 0 otherwise. */
long
hyperell_locally_soluble(GEN T,GEN p)
{
  pari_sp av = avma;
  long res;
  if (typ(T)!=t_POL) pari_err_TYPE("hyperell_locally_soluble",T);
  if (typ(p)!=t_INT) pari_err_TYPE("hyperell_locally_soluble",p);
  RgX_check_ZX(T, "hyperell_locally_soluble");
  res = zpsol(T,p,0,gen_1,gen_0) || zpsol(RgX_recip_shallow(T), p, 1, p, gen_0);
  return gc_long(av, res);
}

/* is t a square in (O_K/pr) ? Assume v_pr(t) = 0 */
static long
quad_char(GEN nf, GEN t, GEN pr)
{
  GEN T, p, modpr = zk_to_Fq_init(nf, &pr,&T,&p);
  return Fq_issquare(nf_to_Fq(nf,t,modpr), T, p)? 1: -1;
}
/* quad_char(x), x in Z, nonzero mod p */
static long
Z_quad_char(GEN x, GEN pr)
{
  long f = pr_get_f(pr);
  if (!odd(f)) return 1;
  return kronecker(x, pr_get_p(pr));
}

/* (pr,2) = 1. return 1 if x in Z_K is a square in Z_{K_pr}, 0 otherwise.
 * modpr = zkmodprinit(nf,pr) */
static long
psquarenf(GEN nf,GEN x,GEN pr,GEN modpr)
{
  pari_sp av = avma;
  GEN p = pr_get_p(pr);
  long v;

  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) == t_INT) {
    if (!signe(x)) return 1;
    v = Z_pvalrem(x, p, &x) * pr_get_e(pr);
    if (v&1) return 0;
    v = (Z_quad_char(x, pr) == 1);
  } else {
    v = ZC_nfvalrem(x, pr, &x);
    if (v&1) return 0;
    v = (quad_char(nf, x, modpr) == 1);
  }
  return gc_long(av,v);
}

static long
ZV_iseven(GEN zlog)
{
  long i, l = lg(zlog);
  for (i = 1; i < l; i++)
    if (mpodd(gel(zlog,i))) return 0;
  return 1;
}

/* pr | 2, project to principal units (trivializes later discrete log) */
static GEN
to_principal_unit(GEN nf, GEN x, GEN pr, GEN sprk)
{
  if (pr_get_f(pr) != 1)
  {
    GEN prk = gel(sprk,3);
    x = nfpowmodideal(nf, x, gmael(sprk,5,1), prk);
  }
  return x;
}
/* pr | 2. Return 1 if x in Z_K is square in Z_{K_pr}, 0 otherwise */
static int
psquare2nf(GEN nf, GEN x, GEN pr, GEN sprk)
{
  long v = nfvalrem(nf, x, pr, &x);
  if (v == LONG_MAX) return 1; /* x = 0 */
  /* (x,pr) = 1 */
  if (odd(v)) return 0;
  x = to_principal_unit(nf, x, pr, sprk); /* = 1 mod pr */
  return ZV_iseven(sprk_log_prk1(nf, x, sprk));
}

/* pr above an odd prime */
static long
lemma6nf(GEN nf, GEN T, GEN pr, long nu, GEN x, GEN modpr)
{
  pari_sp av = avma;
  long la, mu;
  GEN gpx, gx = nfpoleval(nf, T, x);

  if (psquarenf(nf,gx,pr,modpr)) return 1;

  la = nfval(nf,gx,pr);
  gpx = nfpoleval(nf, RgX_deriv(T), x);
  mu = gequal0(gpx)? la+nu+1 /* +oo */: nfval(nf,gpx,pr);
  set_avma(av);
  if (la > (mu<<1)) return 1;
  if (la >= (nu<<1) && mu >= nu) return 0;
  return -1;
}
/* pr above 2 */
static long
lemma7nf(GEN nf, GEN T, GEN pr, long nu, GEN x, GEN sprk)
{
  long i, res, la, mu, q, e, v;
  GEN M, y, gpx, loggx = NULL, gx = nfpoleval(nf, T, x);

  la = nfvalrem(nf, gx, pr, &gx); /* gx /= pi^la, pi a pr-uniformizer */
  if (la == LONG_MAX) return 1;
  if (!odd(la))
  {
    gx = to_principal_unit(nf, gx, pr, sprk); /* now 1 mod pr */
    loggx = sprk_log_prk1(nf, gx, sprk); /* cheap */
    if (ZV_iseven(loggx)) return 1;
  }
  gpx = nfpoleval(nf, RgX_deriv(T), x);
  mu = gequal0(gpx)? la+nu+1 /* oo */: nfval(nf,gpx,pr);

  if (la > (mu << 1)) return 1;
  if (nu > mu)
  {
    if (odd(la)) return -1;
    q = mu+nu-la; res = 1;
  }
  else
  {
    q = (nu << 1) - la;
    if (q <= 0) return 0;
    if (odd(la)) return -1;
    res = 0;
  }
  /* la even */
  e = pr_get_e(pr);
  if (q > e << 1)  return -1;
  if (q == 1) return res;

  /* gx = 1 mod pr; square mod pi^q ? */
  v = nfvalrem(nf, nfadd(nf, gx, gen_m1), pr, &y);
  if (v >= q) return res;
  /* 1 + pi^v y = (1 + pi^vz z)^2 mod pr^q ? v < q <= 2e => vz < e => vz = vy/2
   * => y = x^2 mod pr^(min(q-v, e+v/2)), (y,pr) = 1 */
  if (odd(v)) return -1;
  /* e > 1 */
  M = cgetg(2*e+1 - q + 1, t_VEC);
  for (i = q+1; i <= 2*e+1; i++) gel(M, i-q) = sprk_log_gen_pr(nf, sprk, i);
  M = ZM_hnfmodid(shallowconcat1(M), gen_2);
  return hnf_solve(M,loggx)? res: -1;
}
/* zinit either a sprk (pr | 2) or a modpr structure (pr | p odd).
   pnu = pi^nu, pi a uniformizer */
static long
zpsolnf(GEN nf,GEN T,GEN pr,long nu,GEN pnu,GEN x0,GEN repr,GEN zinit)
{
  long i, res;
  pari_sp av = avma;
  GEN pnup;

  res = typ(zinit) == t_VEC? lemma7nf(nf,T,pr,nu,x0,zinit)
                           : lemma6nf(nf,T,pr,nu,x0,zinit);
  set_avma(av);
  if (res== 1) return 1;
  if (res==-1) return 0;
  pnup = nfmul(nf, pnu, pr_get_gen(pr));
  nu++;
  for (i=1; i<lg(repr); i++)
  {
    GEN x = nfadd(nf, x0, nfmul(nf,pnu,gel(repr,i)));
    if (zpsolnf(nf,T,pr,nu,pnup,x,repr,zinit)) return gc_long(av,1);
  }
  return gc_long(av,0);
}

/* Let y = copy(x); y[k] := j; return y */
static GEN
ZC_add_coeff(GEN x, long k, long j)
{ GEN y = shallowcopy(x); gel(y, k) = utoipos(j); return y; }

/* system of representatives for Zk/pr */
static GEN
repres(GEN nf, GEN pr)
{
  long f = pr_get_f(pr), N = nf_get_degree(nf), p = itos(pr_get_p(pr));
  long i, j, k, pi, pf = upowuu(p, f);
  GEN perm = pr_basis_perm(nf, pr), rep = cgetg(pf+1,t_VEC);

  gel(rep,1) = zerocol(N);
  for (pi=i=1; i<=f; i++,pi*=p)
  {
    long t = perm[i];
    for (j=1; j<p; j++)
      for (k=1; k<=pi; k++) gel(rep, j*pi+k) = ZC_add_coeff(gel(rep,k), t, j);
  }
  return rep;
}

/* = 1 if equation y^2 = z^deg(T) * T(x/z) has a pr-adic rational solution
 * (possibly (1,y,0) = oo), 0 otherwise.
 * coeffs of T are algebraic integers in nf */
static long
locally_soluble(GEN nf,GEN T,GEN pr)
{
  GEN repr, zinit;

  if (typ(T)!=t_POL) pari_err_TYPE("nf_hyperell_locally_soluble",T);
  if (gequal0(T)) return 1;
  checkprid(pr); nf = checknf(nf);
  if (absequaliu(pr_get_p(pr), 2))
  { /* tough case */
    zinit = log_prk_init(nf, pr, 1+2*pr_get_e(pr), NULL);
    if (psquare2nf(nf,constant_coeff(T),pr,zinit)) return 1;
    if (psquare2nf(nf, leading_coeff(T),pr,zinit)) return 1;
  }
  else
  {
    zinit = zkmodprinit(nf, pr);
    if (psquarenf(nf,constant_coeff(T),pr,zinit)) return 1;
    if (psquarenf(nf, leading_coeff(T),pr,zinit)) return 1;
  }
  repr = repres(nf,pr); /* FIXME: inefficient if Npr is large */
  return zpsolnf(nf, T, pr, 0, gen_1, gen_0, repr, zinit) ||
         zpsolnf(nf, RgX_recip_shallow(T), pr, 1, pr_get_gen(pr),
                 gen_0, repr, zinit);
}
long
nf_hyperell_locally_soluble(GEN nf,GEN T,GEN pr)
{
  pari_sp av = avma;
  return gc_long(av, locally_soluble(nf, T, pr));
}

/* return a * denom(a)^2, as an 'liftalg' */
static GEN
den_remove(GEN nf, GEN a)
{
  GEN da;
  a = nf_to_scalar_or_basis(nf, a);
  switch(typ(a))
  {
    case t_INT: return a;
    case t_FRAC: return mulii(gel(a,1), gel(a,2));
    case t_COL:
      a = Q_remove_denom(a, &da);
      if (da) a = ZC_Z_mul(a, da);
      return nf_to_scalar_or_alg(nf, a);
    default: pari_err_TYPE("nfhilbert",a);
      return NULL;/*LCOV_EXCL_LINE*/
  }
}

static long
hilb2nf(GEN nf,GEN a,GEN b,GEN p)
{
  pari_sp av = avma;
  GEN pol;
  a = den_remove(nf, a);
  b = den_remove(nf, b);
  pol = mkpoln(3, a, gen_0, b);
  /* varn(nf.pol) = 0, pol is not a valid GEN  [as in Pol([x,x], x)].
   * But it is only used as a placeholder, hence it is not a problem */
  return gc_long(av, nf_hyperell_locally_soluble(nf,pol,p)? 1: -1);
}

/* local quadratic Hilbert symbol (a,b)_pr, for a,b (nonzero) in nf */
static long
nfhilbertp(GEN nf, GEN a, GEN b, GEN pr)
{
  GEN t;
  long va, vb;
  pari_sp av = avma;

  if (absequaliu(pr_get_p(pr), 2)) return hilb2nf(nf,a,b,pr);

  /* pr not above 2, compute t = tame symbol */
  va = nfval(nf,a,pr);
  vb = nfval(nf,b,pr);
  if (!odd(va) && !odd(vb)) return gc_long(av,1);
  /* Trick: pretend the exponent is 2, result is OK up to squares ! */
  t = famat_makecoprime(nf, mkvec2(a,b), mkvec2s(vb, -va),
                        pr, pr_hnf(nf, pr), gen_2);
  /* quad. symbol is image of t = (-1)^(v(a)v(b)) a^v(b) b^(-v(a))
   * by the quadratic character  */
  switch(typ(t))
  {
    default: /* t_COL */
      if (!ZV_isscalar(t)) break;
      t = gel(t,1); /* fall through */
    case t_INT:
      if (odd(va) && odd(vb)) t = negi(t);
      return gc_long(av,  Z_quad_char(t, pr));
  }
  if (odd(va) && odd(vb)) t = ZC_neg(t);
  return gc_long(av, quad_char(nf, t, pr));
}

/* Global quadratic Hilbert symbol (a,b):
 *  =  1 if X^2 - aY^2 - bZ^2 has a point in projective plane
 *  = -1 otherwise
 * a, b should be nonzero */
long
nfhilbert(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  long i, l;
  GEN S, S2, Sa, Sb, sa, sb;

  nf = checknf(nf);
  a = nf_to_scalar_or_basis(nf, a);
  b = nf_to_scalar_or_basis(nf, b);
  /* local solutions in real completions ? [ error in nfsign if arg is 0 ]*/
  sa = nfsign(nf, a);
  sb = nfsign(nf, b); l = lg(sa);
  for (i=1; i<l; i++)
    if (sa[i] && sb[i])
    {
      if (DEBUGLEVEL>3)
        err_printf("nfhilbert not soluble at real place %ld\n",i);
      return gc_long(av,-1);
    }

  /* local solutions in finite completions ? (pr | 2ab)
   * primes above 2 are toughest. Try the others first */
  Sa = idealfactor(nf, a);
  Sb = idealfactor(nf, b);
  S2 = idealfactor(nf, gen_2);
  S = merge_factor(Sa, Sb, (void*)&cmp_prime_ideal, &cmp_nodata);
  S = merge_factor(S,  S2, (void*)&cmp_prime_ideal, &cmp_nodata);
  S = gel(S,1);
  /* product of all hilbertp is 1 ==> remove one prime (above 2!) */
  for (i=lg(S)-1; i>1; i--)
    if (nfhilbertp(nf,a,b,gel(S,i)) < 0)
    {
      if (DEBUGLEVEL>3)
        err_printf("nfhilbert not soluble at finite place %Ps\n",S[i]);
      return gc_long(av,-1);
    }
  return gc_long(av,1);
}

long
nfhilbert0(GEN nf,GEN a,GEN b,GEN p)
{
  nf = checknf(nf);
  if (p) {
    checkprid(p);
    if (gequal0(a)) pari_err_DOMAIN("nfhilbert", "a", "=", gen_0, a);
    if (gequal0(b)) pari_err_DOMAIN("nfhilbert", "b", "=", gen_0, b);
    return nfhilbertp(nf,a,b,p);
  }
  return nfhilbert(nf,a,b);
}

/*******************************************************************/
/*                         ELLRANK                                 */
/*******************************************************************/
/* This section is a port by Bill Allombert of ellQ.gp by Denis Simon
 * Copyright (C) 2019 Denis Simon
 * Distributed under the terms of the GNU General Public License (GPL) */

/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */
/*    FUNCTIONS FOR POLYNOMIALS                \\ */
/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */

static GEN
ell2pol(GEN ell)
{ return mkpoln(4, gen_1, ell_get_a2(ell), ell_get_a4(ell), ell_get_a6(ell)); }

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
  gel(U,2) = ZC_lincomb(gen_1, truedivii(negi(c), d), gel(U,2), gel(U,1));
  return U;
}

static GEN
polreduce(GEN P, GEN M)
{
  long v = varn(P);
  GEN A = deg1pol_shallow(gcoeff(M,1,1), gcoeff(M,1,2), v);
  GEN B = deg1pol_shallow(gcoeff(M,2,1), gcoeff(M,2,2), v);
  return gel(RgX_homogenous_evalpow(P, A, gpowers(B, degpol(P))),1);
}

static GEN
hyperellreduce(GEN Q, GEN *pM)
{
  long d = degpol(Q);
  GEN q1, q2, q3, D, M, R, vD, den, P = Q_primitive_part(Q, &den);
  GEN a = gel(P,d+2), b = gel(P,d+1), c = gel(P, d);

  q1 = muliu(sqri(a), d);
  q2 = shifti(mulii(a,b), 1);
  q3 = subii(sqri(b), shifti(mulii(a,c), 1));
  D = gcdii(gcdii(q1, q2), q3);
  if (!equali1(D))
  {
    q1 = diviiexact(q1, D);
    q2 = diviiexact(q2, D);
    q3 = diviiexact(q3, D);
  }
  D = qfb_disc3(q1, q2, q3);
  if (!signe(D))
    M = mkmat22(gen_1, truedivii(negi(q2),shifti(q1,1)), gen_0, gen_1);
  else if (issquareall(D,&vD))
    M = redqfbsplit(q1, q2, q3, vD);
  else
    M = gel(qfbredsl2(mkqfb(q1,q2,q3,D), NULL), 2);
  R = polreduce(P, M); if (den) R = gmul(R, den);
  *pM = M; return R;
}

/* find point (x:y:z) on y^2 = pol, return [x,z]~ and set *py = y */
static GEN
projratpointxz(GEN pol, long lim, GEN *py)
{
  pari_timer ti;
  GEN P;
  if (issquareall(leading_coeff(pol), py)) return mkcol2(gen_1, gen_0);
  if (DEBUGLEVEL) timer_start(&ti);
  P = hyperellratpoints(pol, stoi(lim), 1);
  if (DEBUGLEVEL) timer_printf(&ti,"hyperellratpoints(%ld)",lim);
  if (lg(P) == 1) return NULL;
  P = gel(P,1); *py = gel(P,2); return mkcol2(gel(P,1), gen_1);
}

/* P a list of integers (actually primes) one of which divides x; return
 * the first one */
static GEN
first_divisor(GEN x, GEN P)
{
  long i, n = lg(P);
  for (i = 1; i < n; i++)
    if (dvdii(x, gel(P,i))) return gel(P,i);
  return gel(P,i);
}

/* find point (x:y:z) on y^2 = pol, return [x,z]~ and set *py = y */
static GEN
projratpointxz2(GEN pol, long lim, GEN *py)
{
  pari_sp av = avma;
  GEN list = mkvec(mkvec4(pol, matid(2), gen_1, gen_1));
  long i, j;

  for (i = 1; i < lg(list); i++)
  {
    GEN K, k, ff, co, p, M, C, r, pol, L = gel(list, i);
    long lr;

    list = vecsplice(list, i); i--;
    pol = Q_primitive_part(gel(L,1), &K);
    M = gel(L,2);
    K = K? mulii(gel(L,3), K): gel(L,3);
    C = gel(L,4);
    if (Z_issquareall(K, &k))
    {
      GEN xz, y, aux, U;
      pol = hyperellreduce(pol, &U);
      xz = projratpointxz(pol, lim, &y); if (!xz) continue;
      *py = gmul(y, mulii(C, k));
      aux = RgM_RgC_mul(ZM2_mul(M, U), xz);
      if (gequal0(gel(aux, 2))) return mkcol2(gel(aux,1), gen_0);
      *py = gdiv(*py, gpowgs(gel(aux, 2), degpol(pol)>>1));
      return mkcol2(gdiv(gel(aux, 1), gel(aux, 2)), gen_1);
    }
    ff = Z_factor(K); co = core2(mkvec2(K, ff)); K = gel(co,1); /* > 1 */
    p = first_divisor(K, gel(ff,1));
    K = diviiexact(K, p);
    C = mulii(mulii(C, gel(co,2)), p);
    /* root at infinity */
    if (dvdii(leading_coeff(pol), p))
    {
      GEN U = mkmat2(gel(M,1), ZC_Z_mul(gel(M,2), p));
      if (equali1(content(U)))
      {
        GEN t = ZX_rescale(pol, p);
        list = vec_append(list, mkvec4(ZX_Z_divexact(t,p), U, K, C));
      }
    }
    r = FpC_center(FpX_roots(pol, p), p, shifti(p,-1)); lr = lg(r);
    for (j = 1; j < lr; j++)
    {
      GEN U = ZM2_mul(M, mkmat22(p, gel(r, j), gen_0, gen_1));
      if (equali1(content(U)))
      {
        GEN t = ZX_unscale(ZX_translate(pol, gel(r,j)), p);
        list = vec_append(list, mkvec4(ZX_Z_divexact(t,p), U, K, C));
      }
    }
    if (gc_needed(av, 1)) gerepileall(av, 2, &pol, &list);
  }
  return NULL;
}

static GEN
polrootsmodpn(GEN pol, GEN p)
{
  pari_sp av = avma, av2;
  long j, l, i = 1, vd = Z_pval(ZX_disc(pol), p);
  GEN v, r, P;

  if (!vd) { set_avma(av); retmkvec(mkvec2(gen_0, gen_0)); }
  pol = Q_primpart(pol);
  P = gpowers0(p, vd-1, p); av2 = avma;
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

/* z is integral; sprk true (pr | 2) [t_VEC] or modpr structure (pr | p odd)
 * [t_COL] */
static GEN
kpmodsquares1(GEN nf, GEN z, GEN sprk)
{
  GEN modpr = (typ(sprk) == t_VEC)? gmael(sprk, 4, 1): sprk;
  GEN pr = modpr_get_pr(modpr), p = pr_get_p(pr);
  long v = nfvalrem(nf, z, pr, &z);
  if (equaliu(p, 2))
  {
    GEN c;
    z = to_principal_unit(nf, z, pr, sprk); /* = 1 mod pr */
    c = ZV_to_Flv(sprk_log_prk1(nf, z, sprk), 2);
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
kpmodsquares(GEN vnf, GEN z, GEN PP)
{
  pari_sp av = avma;
  long i, j, l = lg(vnf);
  GEN dz, vchar = cgetg(l, t_VEC);
  z = Q_remove_denom(z, &dz); if (dz) z = gmul(z, dz);
  for (i = 1; i < l; i++)
  {
    GEN nf = gel(vnf, i), pp = gel(PP, i);
    GEN kp, delta = RgX_rem(z, nf_get_pol(nf));
    long lp = lg(pp);
    kp = cgetg(lp, t_VEC);
    for (j = 1; j < lp; j++) gel(kp, j) = kpmodsquares1(nf, delta, gel(pp,j));
    gel(vchar, i) = shallowconcat1(kp);
  }
  return gerepileuptoleaf(av, shallowconcat1(vchar));
}

static GEN
veckpmodsquares(GEN x, GEN vnf, GEN PP)
{ pari_APPLY_type(t_MAT, kpmodsquares(vnf, gel(x, i), PP)) }

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
ellabs(GEN P) { return ell_is_inf(P) ? P: mkvec2(gel(P,1), Q_abs(gel(P,2))); }

static GEN
vecellabs(GEN x) { pari_APPLY_same(ellabs(gel(x,i))) }

static GEN
elltwistequation(GEN ell, GEN K)
{
  GEN K2, a2, a4, a6;
  if (!K || equali1(K)) return ell;
  K2 = sqri(K);
  a2 = mulii(ell_get_a2(ell), K);
  a4 = mulii(ell_get_a4(ell), K2);
  a6 = mulii(ell_get_a6(ell), mulii(K, K2));
  return ellinit(mkvec5(gen_0, a2, gen_0, a4, a6), NULL, DEFAULTPREC);
}

static GEN
elltwistpoint(GEN P, GEN K, GEN K2)
{
  if (ell_is_inf(P)) return ellinf();
  return mkvec2(gmul(gel(P,1), K), gmul(gel(P,2), K2));
}

static GEN
elltwistpoints(GEN x, GEN K)
{
  GEN K2;
  if (!K || gequal1(K)) return x;
  K2 = gsqr(K);
  pari_APPLY_same(elltwistpoint(gel(x,i), K, K2))
}

static GEN
ellredgen(GEN E, GEN vP, GEN K, long prec)
{
  if (equali1(K)) K = NULL;
  if (K)
  {
    E = elltwistequation(E, K);
    E = ellinit(E, NULL, prec);
    vP = elltwistpoints(vP, K);
  }
  vP = vecellabs(ellQ_genreduce(E, vP, prec));
  if (K) vP = elltwistpoints(vP, ginv(K));
  return vP;
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

  if (!dvdiu(bnf_get_no(bnf), p)) return cgetg(1,t_VEC);
  w = cgetg(lS+1,t_VEC);
  gel(w,1) = diagonal(bnf_get_cyc(bnf));
  for (i = 1; i < lS; i++) gel(w,i+1) = bnfisprincipal0(bnf,gel(S,i),0);
  v = ZM_hnf(shallowconcat1(w));
  vD = Z_lval(ZM_det(v), p);
  if (!vD) { set_avma(av); return cgetg(1, t_VEC); }
  S2 = cgetg(vD+2, t_VEC);
  u_forprime_init(&P,2,ULONG_MAX);
  while ((l = u_forprime_next(&P)))
  {
    GEN w, Sl = idealprimedec(bnf, utoi(l));
    long lSl = lg(Sl);
    ulong vDl;
    for (i = 1; i < lSl; i++)
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
nfC_prV_val(GEN nf, GEN G, GEN P)
{
  long i, j, lG = lg(G), lP = lg(P);
  GEN M = cgetg(lG, t_MAT);
  for (i = 1; i < lG; i++)
  {
    GEN V = cgetg(lP, t_COL);
    for (j = 1; j < lP; j++)
      gel(V,j) = gpnfvalrem(nf, gel(G,i), gel(P,j), NULL);
    gel(M,i) = V;
  }
  return M;
}

static GEN
_factorbackmod(GEN nf, GEN g, GEN e, ulong p)
{
  GEN y = nffactorback(nf, g, e);
  return nfmul(nf, y, nfsqr(nf, idealredmodpower(nf, y, p, 0)));
}
static GEN
nfV_factorbackmod(GEN nf, GEN x, ulong p)
{
  long i, l = lg(x);
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN y = gel(x,i), g = gel(y,1), e = gel(y,2);
    gel(v,i) = _factorbackmod(nf, g, ZV_to_Flv(e,p), p);
  }
  return v;
}
static GEN
nfV_zm_factorback(GEN nf, GEN G, GEN x, long p)
{ pari_APPLY_type(t_VEC, _factorbackmod(nf, G, gel(x,i), p)) }

static GEN
prV_ZM_factorback(GEN nf, GEN S, GEN x)
{ pari_APPLY_type(t_VEC,idealfactorback(nf, S, gel(x,i), 0)) }

static GEN
bnfselmer(GEN bnf, GEN S, ulong p)
{
  pari_sp av = avma;
  GEN nf = bnf_get_nf(bnf), S2, S3, e, f, e2, kerval, LS2gen, LS2fu, LS2all;
  long n = S? lg(S)-1: 0, n3, n2all, r;

  S2 = bestS(bnf, S, p);
  S3 = S? shallowconcat(S, S2): S2;
  LS2all = nfV_factorbackmod(nf, gel(bnfunits(bnf, S3), 1), p);
  n3 = lg(S3)-1; n2all = lg(LS2all)-1; r = n2all - n3 - 1;
  LS2gen = vecslice(LS2all,1,n3);
  LS2fu  = vecslice(LS2all,n3+1, n2all-1);
  e2 = nfC_prV_val(nf, LS2gen, S2);
  kerval = Flm_ker(ZM_to_Flm(e2, p), p);
  LS2gen = nfV_zm_factorback(nf, LS2gen, kerval, p);
  e = S? nfC_prV_val(nf, LS2gen, S): zeromat(0,n3);
  e2 = ZM_divexactu(ZM_zm_mul(e2, kerval), p);
  f = prV_ZM_factorback(nf, S2, e2);
  LS2gen = shallowconcat(LS2fu, LS2gen);
  if (bnf_get_tuN(bnf) % p == 0)
  {
    LS2gen = vec_prepend(LS2gen, bnf_get_tuU(bnf));
    r++;
  }
  e = shallowconcat(zeromat(n, r), e);
  f = shallowconcat(const_vec(r, gen_1), f);
  return gerepilecopy(av, mkvec3(LS2gen,e,f));
}

static GEN
get_kerval(GEN nf, GEN S2, GEN LS2gen)
{
  long i, j, lS2 = lg(S2), l = lg(LS2gen);
  GEN e = cgetg(l, t_MAT);
  for (i = 1; i < l; i++)
  {
    GEN v = cgetg(lS2, t_VECSMALL);
    for (j=1; j < lS2; j++) v[j] = odd(idealval(nf, gel(LS2gen, i), gel(S2,j)));
    gel(e, i) = Flv_to_F2v(v);
  }
  return F2m_ker(e);
}
static GEN
nf2selmer_quad(GEN nf, GEN S)
{
  pari_sp ltop = avma;
  GEN D = nf_get_disc(nf), factD = nf_get_ramified_primes(nf);
  GEN SlistQ, QS2gen, gen, Hlist, H, KerH, norms, LS2gen, chpol, Q;
  GEN kerval, S2, G, e, f, b, c, bad;
  long lS = lg(S), l, lHlist, i, j, k;

  SlistQ = cgetg(lS, t_VEC);
  for (i = 1; i < lS; i++) gel(SlistQ, i) = pr_get_p(gel(S, i));
  SlistQ = ZV_sort_uniq(SlistQ);
  QS2gen = vec_prepend(SlistQ, gen_m1);
  bad = ZV_sort_uniq(shallowconcat(factD, SlistQ));
  Hlist = ZV_search(bad, gen_2)? bad: vec_prepend(bad, gen_2);
  l = lg(QS2gen);
  lHlist = lg(Hlist);
  H = cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    GEN v = cgetg(lHlist, t_VECSMALL);
    for (i = 1; i < lHlist; i++)
      v[i] = hilbert(D, gel(QS2gen, j), gel(Hlist, i)) < 0;
    gel(H, j) = Flv_to_F2v(v);
  }
  KerH = F2m_ker(H); l = lg(KerH);
  norms = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
    gel(norms, i) = factorback2(QS2gen, F2c_to_ZC(gel(KerH, i)));
  LS2gen = cgetg(l, t_VEC);
  chpol = QXQ_charpoly(gel(nf_get_zk(nf), 2), nf_get_pol(nf), 0);
  b = gdivgs(negi(gel(chpol, 3)), 2);
  c = gel(chpol, 2);
  Q = mkmat3(mkcol3(gen_1, b, gen_0),
             mkcol3(b, c, gen_0),
             mkcol3(gen_0, gen_0, gen_0));
  for (k = 1; k < l; k++)
  {
    GEN sol;
    gcoeff(Q, 3, 3) = negi(gel(norms, k));
    sol = qfsolve(Q); /* must be solvable */
    sol = Q_primpart(mkcol2(gel(sol,1), gel(sol,2)));
    gel(LS2gen, k) = basistoalg(nf, sol);
  }
  if (equalis(D, -4)) G = bad;
  else
  {
    G = vecsplice(bad, ZV_search(bad, gel(factD, lg(factD)-1)));
    G = vec_prepend(G, gen_m1);
  }
  LS2gen = shallowconcat(G, LS2gen);
  l = lg(SlistQ); S2 = cgetg(l, t_VEC);
  if (l > 1)
  {
    for (i = 1; i < l; i++) gel(S2, i) = idealprimedec(nf, gel(SlistQ, i));
    S2 = setminus(shallowconcat1(S2), S);
  }
  kerval = get_kerval(nf, S2, LS2gen); l = lg(kerval);
  gen = cgetg(l, t_VEC);
  e = cgetg(l, t_MAT);
  f = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN id, ei, x = nffactorback(nf, LS2gen, F2v_to_Flv(gel(kerval, i)));
    gel(e,i) = ei = cgetg(lS, t_COL);
    for (j = 1; j < lS; j++) gel(ei,j) = stoi(idealval(nf, x, gel(S,j)));
    id = idealdiv(nf, x, idealfactorback(nf, S, gel(e,i), 0));
    if (!idealispower(nf, id, 2, &gel(f,i))) pari_err_BUG("nf2selmer_quad");
    gel(gen, i) = x;
  }
  return gerepilecopy(ltop, mkvec3(gen, e, f));
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
kernorm(GEN gen, GEN S, ulong p, GEN pol)
{
  long i, j, lS, lG = lg(gen);
  GEN M = cgetg(lG, t_MAT);
  if (p == 2) S = vec_prepend(S, gen_m1);
  lS = lg(S);
  for (j = 1; j < lG; j++)
  {
    GEN N = QXQ_norm(gel(gen,j), pol);
    GEN v = cgetg(lS, t_VECSMALL);
    for (i = 1; i < lS; i++)
      v[i] = (i == 1 && p==2)? gsigne(N) < 0
                             : smodss(Q_pvalrem(N, gel(S, i), &N), p);
    gel(M, j) = v;
  }
  return Flm_ker(M, p);
}

/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */
/*    FUNCTIONS FOR 2-DESCENT                  \\ */
/* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ */
/* vector of t_VEC; return total number of entries */
static long
RgVV_nb(GEN v)
{
  long i, l = lg(v), n = 0;
  for (i = 1; i < l; i++) n += lg(gel(v,i)) - 1;
  return n;
}

static GEN
elllocalimage(GEN pol, GEN K, GEN vnf, GEN p, GEN pp, GEN pts)
{
  pari_sp av = avma;
  long attempt = 0, p2 = RgVV_nb(pp), prank = equaliu(p, 2)? p2: p2 - 1;
  GEN R = polrootsmodpn(gmul(K, pol), p), bound = addiu(p, 6);

  if (!pts) pts = cgetg(1, t_MAT);
  for(;;)
  {
    pari_sp btop;
    GEN xx, y2, delta;
    pts = Flm_image(pts, 2); if (lg(pts)-1 == prank) break;
    attempt++;
    if (attempt%16 == 0) bound = mulii(bound, p);
    btop = avma;
    do
    {
      GEN r = gel(R, random_Fl(lg(R)-1)+1);
      long pprec = random_Fl(itou(gel(r, 2)) + 3) - 2; /* >= -2 */
      set_avma(btop);
      xx = gadd(gel(r, 1), gmul(powis(p, pprec), randomi(bound)));
      y2 = gmul(K, poleval(pol, xx));
    } while (gequal0(y2) || !Qp_issquare(y2, p));
    delta = deg1pol_shallow(negi(K), gmul(K, xx), 0);
    pts = vec_append(pts, kpmodsquares(vnf, delta, pp));
  }
  return gerepilecopy(av, pts);
}

static GEN
ellLS2image(GEN pol, GEN vP, GEN K, GEN vpol)
{
  GEN v;
  long i, l = lg(vP);

  if (l == 1) return cgetg(1, t_VEC);
  v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN P = gel(vP, i), x, t;
    if (ell_is_inf(P)) { gel(v, i) = gen_1; continue; }
    x = gel(P,1); t = deg1pol_shallow(gen_m1, x, 0);
    if (!gequal0(gel(P,2)))
      gel(v, i) = gmul(K, t);
    else
    {
      long k, lp = lg(vpol);
      GEN aux = cgetg(lp, t_VEC);
      for (k = 1; k < lp; k++)
      {
        GEN a = signe(poleval(gel(vpol, k), x))? gmul(K, t): ZX_deriv(pol);
        gel(aux, k) = gmodulo(a, gel(vpol, k));
      }
      gel(v, i) = liftpol_shallow(chinese1(aux));
    }
  }
  return v;
}

static GEN
ellsearchtrivialpoints(GEN ell, GEN lim, GEN help)
{
  pari_sp av = avma;
  GEN torseven = gtoset(gel(elltors_psylow(ell,2), 3));
  GEN triv = ellratpoints(ell, lim, 0);

  if (help) triv = shallowconcat(triv, help);
  triv = gtoset(vecellabs(triv));
  triv = setminus(triv, torseven);
  return gerepilecopy(av, mkvec2(torseven, triv));
}

GEN
ellrankinit(GEN ell, long prec)
{
  pari_sp av = avma;
  GEN urst;
  checkell_Q(ell); ell = ellintegralbmodel(ell, &urst);
  return gerepilecopy(av, mkvec3(ell, urst, makevbnf(ell, prec)));
}

INLINE GEN
ZV_isneg(GEN x) { pari_APPLY_long(signe(gel(x,i)) < 0) }

static GEN
selmersign(GEN x, GEN vpol, GEN L)
{ pari_APPLY_same(ZV_isneg(nfeltsign(gel(x, i), RgX_rem(L, gel(vpol, i)), NULL))) }

static GEN
vecselmersign(GEN vnf, GEN vpol, GEN x)
{ pari_APPLY_type(t_VEC, shallowconcat1(selmersign(vnf, vpol, gel(x, i)))) }

static GEN
_trace(GEN z, GEN T)
{
  long n = degpol(T)-1;
  if (degpol(z) < n) return gen_0;
  return gdiv(gel(z, 2+n), gel(T, 3+n));
}
static GEN
tracematrix(GEN zc, GEN b, GEN T)
{
  long i, j;
  GEN q = cgetg(4, t_MAT);
  for (j = 1; j <= 3; j++) gel(q,j) = cgetg(4, t_COL);
  for (j = 1; j <= 3; j++)
  {
    for (i = 1; i < j; i++) gcoeff(q,i,j) = gcoeff(q,j,i) =
      _trace(QXQ_mul(zc, QXQ_mul(gel(b,i), gel(b,j), T), T), T);
    gcoeff(q,i,i) = _trace(QXQ_mul(zc, QXQ_sqr(gel(b,i), T), T), T);
  }
  return q;
}

static GEN
RgXV_cxeval(GEN x, GEN r, GEN ri)
{ pari_APPLY_same(RgX_cxeval(gel(x,i), r, ri)) }

static GEN
redquadric(GEN base, GEN q2, GEN pol, GEN zc)
{
  long i, l, prec = nbits2prec(2*gexpo(q2)) + 1;
  GEN s = NULL, R = roots(pol, prec);
  l = lg(R);
  for (i = 1; i < l; ++i)
  {
    GEN r = gel(R,i), ri = gexpo(r) > 1? ginv(r): NULL;
    GEN b = RgXV_cxeval(base, r, ri), z = RgX_cxeval(zc, r, ri);
    GEN M = RgC_RgV_mulrealsym(RgV_Rg_mul(b, gabs(z, prec)), gconj(b));
    s = s? RgM_add(s, M): M;
  }
  return lllgram(s);
}

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

static void
check_oncurve(GEN ell, GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN P = gel(v, i);
    if (lg(P) != 3 || !oncurve(ell,P)) pari_err_TYPE("ellrank",P);
  }
}

static GEN
smallbasis1(GEN nf, GEN crt, GEN pol)
{
  GEN b, zk = nf_get_zk(nf);
  long i, l = lg(zk);

  b = cgetg(l, t_COL);
  for (i = 1; i < l; ++i)
  {
    GEN z = nf_to_scalar_or_alg(nf, gel(zk, i));
    gel(b, i) = grem(gsub(z, gmul(crt, z)), pol); /* z mod T, 0 mod (pol/T) */
  }
  return b;
}

static GEN
vecsmallbasis(GEN x, GEN vcrt, GEN pol)
{ pari_APPLY_same(smallbasis1(gel(x,i), gel(vcrt,i), pol)) }

static GEN
ZC_shifti(GEN x, long n) { pari_APPLY_type(t_COL, shifti(gel(x,i), n)) }

static GEN
selmerbasis(GEN nf, GEN LS2k, GEN expo, GEN sqrtLS2, GEN factLS2,
            GEN badprimes, GEN crt, GEN pol)
{
  GEN b, ek = vecslice(expo, LS2k[1], LS2k[2]);
  GEN sqrtzc = idealfactorback(nf, sqrtLS2, zv_neg(ek), 0);
  GEN E = ZC_shifti(ZM_zc_mul(factLS2, ek), -1);
  long i, n = nf_get_degree(nf);

  if (ZV_equal0(E))
    sqrtzc = idealhnf(nf, sqrtzc);
  else
    sqrtzc = idealmul(nf, sqrtzc, idealfactorback(nf, badprimes, ZC_neg(E), 0));
  b = cgetg(n+1, t_COL);
  for (i = 1; i <= n; i++)
  {
    GEN z = nf_to_scalar_or_alg(nf, gel(sqrtzc, i));
    gel(b, i) = grem(gsub(z, gmul(crt, z)), pol); /* z mod T, 0 mod (pol/T) */
  }
  return b;
}

static long randu(void) { return random_Fl(127) - 63; }
static GEN
randS(GEN b)
{
  return gadd(gmulgs(gel(b,1), randu()),
              gadd(gmulgs(gel(b,2), randu()), gmulgs(gel(b,3), randu())));
}

static GEN
liftselmer(GEN vec, GEN vnf, GEN sbase, GEN LS2k, GEN LS2, GEN sqrtLS2, GEN factLS2,
           GEN badprimes, GEN vcrt, GEN pol, GEN selmer, GEN K, long lim, long ntry)
{
  pari_sp av = avma, av2;
  long n = lg(vnf)-1, k, t;
  GEN ttheta, tttheta, z, b, polprime, expo = Flm_Flc_mul(selmer, vec, 2);

  b = cgetg(n+1, t_VEC);
  for (k = 1; k <= n; k++)
    gel(b,k) = selmerbasis(gel(vnf,k), gel(LS2k,k), expo, gel(sqrtLS2,k),
                           gel(factLS2,k), gel(badprimes,k), gel(vcrt,k), pol);
  b = shallowconcat1(b);
  z = RgXQV_factorback(LS2, expo, pol);
  ttheta = RgX_shift_shallow(pol,-2);
  tttheta = RgX_shift_shallow(pol, -1);
  polprime = ZX_deriv(pol); av2 = avma;
  for (t = 1; t <= ntry; t++, set_avma(av2))
  {
    GEN P, Q, R, den, q0, q1, q2, xz, x, y, zz, zc, U, param, newb;
    if (t == 1) zc = z;
    else
    {
      GEN r;
      do r = randS(sbase); while (degpol(QX_gcd(r, pol)));
      zc = RgXQ_mul(z, QXQ_sqr(r, pol), pol);
    }
    q2 = Q_primpart(tracematrix(zc, b, pol));
    U = redquadric(b, q2, pol, QXQ_div(zc, polprime, pol));
    if (lg(U) < 4) continue;
    q2 = qf_apply_RgM(q2, U);
    newb = RgV_RgM_mul(b, U);

    param = Q_primpart(qfparam(q2, qfsolve(q2), 0));
    param = RgM_to_RgXV_reverse(shallowtrans(param), 0);
    q1 = RgM_neg(tracematrix(RgXQ_mul(zc, ttheta, pol), newb, pol));
    Q = hyperellreduce(qfeval(q1, param), &R);
    if (!equali1(K)) Q = RgX_Rg_mul(Q, K);
    Q = Q_remove_denom(Q, &den);
    if (den) Q = ZX_Z_mul(Q, den);
    if (DEBUGLEVEL>1) err_printf("  reduced quartic: Y^2 = %Ps\n", Q);

    xz = projratpointxz(Q, lim, &zz);
    if (!xz)
    {
      xz = projratpointxz2(Q, lim, &zz);
      if (!xz) continue;
    }
    P = RgM_RgC_mul(R, xz); x = gel(P,1); y = gel(P,2);

    param = RgXV_homogenous_evaldeg(param, x, gpowers(y, 2));
    param = gmul(param, gdiv(den? mulii(K, den): K, zz));
    q0 = tracematrix(RgXQ_mul(zc, tttheta, pol), newb, pol);
    x = gdiv(qfeval(q0, param), K);
    (void)issquareall(gdiv(poleval(pol, x), K), &y);
    P = mkvec2(x, y);
    if (DEBUGLEVEL) err_printf("Found point: %Ps\n", P);
    return gerepilecopy(av, P);
  }
  return NULL;
}

static GEN
ell2selmer(GEN ell, GEN help, GEN K, GEN vbnf, long effort, long prec)
{
  pari_sp av;
  GEN ell_K, KP, torseven, pol, vnf, vpol, vroots, vr1, vcrt, sbase;
  GEN LS2, factLS2, sqrtLS2, LS2k, selmer, helpLS2, LS2chars, helpchars;
  GEN newselmer, factdisc, badprimes, triv, helplist, listpoints;
  long i, j, k, n, tors2, mwrank, dim, nbpoints, lfactdisc, t, u;

  if (!K) K = gen_1;
  pol = ell2pol(ell);
  ell_K = elltwistequation(ell, K);
  if (help) help = elltwistpoints(help, K);
  triv = ellsearchtrivialpoints(ell_K, muluu(LIMTRIV,(effort+1)), help);

  torseven = elltwistpoints(gel(triv, 1), ginv(K));
  help = elltwistpoints(gel(triv, 2), ginv(K));
  help = shallowconcat(torseven, help);
  ell = ellinit(ell, NULL, prec);
  n = lg(torseven); tors2 = n - 1;
  if (lg(vbnf)-1 != n) pari_err_TYPE("ell2selmer",vbnf);
  KP = gel(absZ_factor(K), 1);
  factdisc = mkvec3(KP, mkcol(gen_2), gel(absZ_factor(ZX_disc(pol)), 1));
  factdisc = ZV_sort_uniq(shallowconcat1(factdisc));
  badprimes = cgetg(n+1, t_VEC);
  vnf = cgetg(n+1, t_VEC);
  vpol = cgetg(n+1, t_VEC);
  vroots = cgetg(n+1, t_VEC);
  vcrt = cgetg(n+1, t_VEC);
  vr1 = cgetg(n+1, t_VECSMALL);
  LS2 = cgetg(n+1, t_VEC);
  factLS2 = cgetg(n+1, t_VEC);
  sqrtLS2 = cgetg(n+1, t_VEC);
  LS2k = cgetg(n+1, t_VEC);
  for (k = 1, t = 0; k <= n; ++k)
  {
    GEN T, Tinv, id, f, sel, L, S, NF = gel(vbnf,k), nf = checknf(NF);
    long i, lk;
    gel(vnf, k) = nf;
    gel(vpol, k) = T = nf_get_pol(nf);
    Tinv = RgX_div(pol, gel(vpol, k));
    gel(vcrt, k) = QX_mul(QXQ_inv(T, Tinv), T);
    gel(vroots, k) = nf_get_roots(gel(vnf, k));
    uel(vr1, k) = nf_get_r1(gel(vnf, k));

    id = idealadd(nf, nf_get_index(nf), ZX_deriv(T));
    f = nf_pV_to_prV(nf, KP); settyp(f, t_COL);
    f = mkvec3(gel(idealfactor(nf, Tinv), 1),
               gel(idealfactor(nf, id), 1), f);
    gel(badprimes, k) = S = gtoset(shallowconcat1(f));
    sel = (NF == nf)? nf2selmer_quad(NF, S): bnfselmer(NF, S, 2);
    gel(LS2, k) = L = gel(sel, 1); lk = lg(L);
    gel(factLS2, k) = gel(sel, 2);
    gel(sqrtLS2, k) = gel(sel, 3);
    gel(LS2k, k) = mkvecsmall2(t + 1, t + lk - 1); t += lk - 1;
    for (i = 1; i < lk; i++)
    {
      GEN z = nf_to_scalar_or_alg(nf, gel(L,i));
      /* z mod T, 1 mod (pol/T) */
      gel(L,i) = grem(gadd(z, gmul(gsubsg(1,z), gel(vcrt,k))), pol);
    }
  }
  sbase = shallowconcat1(vecsmallbasis(vnf, vcrt, pol));
  if (DEBUGLEVEL>2) err_printf("   local badprimes = %Ps\n", badprimes);
  LS2 = shallowconcat1(LS2);
  helpLS2 = ellLS2image(pol, help, K, vpol);
  selmer = kernorm(LS2, factdisc, 2, pol);
  LS2chars = vecselmersign(vnf, vpol, LS2);
  helpchars = vecselmersign(vnf, vpol, helpLS2);
  if (zv_sum(vr1) == 3)
  {
    GEN signs;
    long row, m = 1;
    if (signe(K) > 0)
    {
      for (k = 2; k <= n; ++k)
        if (cmprr(gmael(vroots,k,1), gmael(vroots,m,1)) < 0) m = k;
      row = 1; for (k = 1; k < m; k++) row += vr1[k];
    }
    else
    {
      for (k = 2; k <= n; ++k)
        if (cmprr(gmael(vroots,k,vr1[k]), gmael(vroots,m,vr1[k])) > 0) m = k;
      row = 0; for (k = 1; k <= m; k++) row += vr1[k];
    }
    signs = Flm_transpose(mkmat(Flm_row(LS2chars, row)));
    /* the signs of LS2 for this embedding */
    selmer = Flm_intersect(selmer, Flm_ker(signs, 2), 2);
  }
  av = avma; lfactdisc = lg(factdisc);
  for (i = 1; i < lfactdisc; i++)
  {
    GEN LS2image, helpimage, locimage;
    GEN p = gel(factdisc, i), pp = cgetg(n+1, t_VEC);
    int pis2 = equaliu(p, 2);

    for (k = 1; k <= n; k++)
    {
      GEN v, nf = gel(vnf,k), PR = idealprimedec(nf, p);
      long l = lg(PR);
      gel(pp, k) = v = cgetg(l, t_VEC);
      for (j = 1; j < l; j++)
      {
        GEN pr = gel(PR,j);
        gel(v,j) = pis2? log_prk_init(nf, pr, 1 + 2 * pr_get_e(pr), NULL)
                       : zkmodprinit(nf, pr);
      }
    }
    LS2image = veckpmodsquares(LS2, vnf, pp);
    LS2chars = vconcat(LS2chars, LS2image);
    helpimage = veckpmodsquares(helpLS2, vnf, pp);
    helpchars = vconcat(helpchars, helpimage);
    locimage = elllocalimage(pol, K, vnf, p, pp, helpimage);
    locimage = Flm_intersect(LS2image, locimage, 2);
    selmer = Flm_intersect(selmer, shallowconcat(Flm_ker(LS2image,2),
                                                 Flm_invimage(LS2image, locimage,2)), 2);
    dim = lg(selmer)-1;
    if (dim == Flm_rank(helpimage,2)) break;
    if (i==lfactdisc-1 && Flm_rank(Flm_mul(LS2chars, selmer, 2), 2) < dim)
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
    if (gc_needed(av, 1))
      gerepileall(av, 4, &factdisc, &selmer, &LS2chars, &helpchars);
  }
  helplist = gel(Flm_indexrank(helpchars,2), 2);
  help = shallowextract(help, helplist);
  helpchars = shallowextract(helpchars, helplist);
  helpLS2 = shallowextract(helpLS2, helplist);
  dim = lg(selmer)-1;
  newselmer = Flm_invimage(Flm_mul(LS2chars, selmer, 2), helpchars, 2);
  if (DEBUGLEVEL) err_printf("Selmer rank: %ld\n", dim);
  listpoints = vec_lengthen(help, dim);
  nbpoints = lg(help) - 1;
  for (i=1; i <= dim; i++)
  {
    pari_sp btop = avma;
    GEN P, vec = vecsmall_ei(dim, i);
    if (Flm_Flc_invimage(newselmer, vec, 2)) continue;
    P = liftselmer(vec, vnf, sbase, LS2k, LS2, sqrtLS2, factLS2, badprimes,
        vcrt, pol, selmer, K, LIM1, 1);
    if (P)
    {
      gel(listpoints, ++nbpoints) = P;
      gel(newselmer, nbpoints) = vec;
      setlg(newselmer, nbpoints+1);
    } else set_avma(btop);
  }
  for (t=1, u=1; nbpoints < dim && effort > 0; t++)
  {
    pari_sp btop = avma;
    GEN P, vec;
    do vec = random_Flv(dim, 2);
    while (zv_equal0(vec) || Flm_Flc_invimage(newselmer, vec, 2));
    P = liftselmer(vec, vnf, sbase, LS2k, LS2, sqrtLS2, factLS2, badprimes,
        vcrt, pol, selmer, K, u*LIM1, u);
    if (P)
    {
      gel(listpoints, ++nbpoints) = P;
      gel(newselmer, nbpoints) = vec;
      setlg(newselmer, nbpoints+1);
    } else set_avma(btop);
    if (t == dim) { t = 0; u++; effort--; }
  }
  setlg(listpoints, nbpoints+1);
  mwrank = nbpoints - tors2;
  if (odd(dim - nbpoints)) mwrank++;
  listpoints = vecslice(listpoints, 1+tors2, nbpoints);
  listpoints = ellredgen(ell, listpoints, K, prec);
  return mkvec3(utoi(mwrank), utoi(dim-tors2), listpoints);
}

static GEN
ell2descent(GEN ell, GEN help, long effort, long prec)
{
  pari_sp ltop = avma;
  GEN urst, v, vbnf, K = gen_1;

  if (lg(ell)==3 && typ(ell)==t_VEC)
  {
    K = gel(ell, 2); ell = gel(ell, 1);
    if (typ(K) != t_INT)
      pari_err(e_MISC, "ell2descent: nonintegral quadratic twist");
    if (!signe(K)) pari_err(e_MISC, "ell2descent: twist by 0");
  }
  if (lg(ell)==4 && typ(ell)==t_VEC)
  {
    vbnf = gel(ell,3); urst = gel(ell,2);
    ell = gel(ell,1); checkell_Q(ell);
    if (!ell_is_integral(ell))
      pari_err(e_MISC, "ell2descent: nonintegral model");
    if (signe(ell_get_a1(ell)))
      pari_err(e_MISC, "ell2descent: nonzero coefficient a1");
    if (signe(ell_get_a3(ell)))
      pari_err(e_MISC, "ell2descent: nonzero coefficient a3");
  }
  else
  {
    checkell_Q(ell);
    ell = ellintegralbmodel(ell, &urst);
    vbnf = makevbnf(ell, prec);
  }
  if (!equali1(K) && (!gequal0(ell_get_a1(ell)) || !gequal0(ell_get_a3(ell))))
    pari_err(e_MISC, "ell2descent: quadratic twist only allowed for a1=a3=0");
  if (help)
  {
    if (urst) help = ellchangepoint(help, urst);
    check_oncurve(ell, help);
  }
  v = ell2selmer(ell, help, K, vbnf, effort, prec);
  if (urst) gel(v,3) = ellchangepoint(gel(v,3), ellchangeinvert(urst));
  return gerepilecopy(ltop, v);
}

GEN
ellrank(GEN ell, long effort, GEN help, long prec)
{ return ell2descent(ell, help, effort, prec); }
