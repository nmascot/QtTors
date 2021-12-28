/* Copyright (C) 2018  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/****************************************************************/
/*                   HYPERGEOMETRIC MOTIVES                     */
/****************************************************************/
#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_hgm
static THREAD GEN HGMDATA2, HGMDATA3;

void
pari_init_hgm(void) { HGMDATA2 = HGMDATA3 = NULL; }

void
pari_close_hgm(void)
{ guncloneNULL_deep(HGMDATA2); guncloneNULL_deep(HGMDATA3); }

/* For now: only HGM defined over Q. Can be given as
 * [alpha] two lists (alpha_i), (beta_j) of the same length of
 *      rational numbers in [0,1[ with the cyclotomic property.
 * [cyclo] two lists (d_i), (e_j) of positive integers with
 *      sum_i phi(d_i) = sum_j phi(e_j).
 * [gamma] a list of (g_i) such that P=prod_i(x^i-1)^{g_i}
 *
 * Initialization computes all HGM data independent of t (hgm) */
/***************************************************************/
/*            PART I: functions independent of t, p            */
/***************************************************************/

static GEN
RgV_addhalf(GEN x) { pari_APPLY_same(gadd(ghalf, gel(x,i))); }
static GEN
RgV_mirror(GEN x) { pari_APPLY_same(gsubsg(1, gel(x,i))); }

static GEN
hodge(GEN val, GEN vbe, long *pTT)
{
  long r = lg(val) - 1, T, s, k;
  GEN H, w = indexsort( shallowconcat(val, RgV_mirror(vbe)) );
  for (k = 1, s = T = 0; k <= 2*r; k++)
    if (w[k] > r) { if (--s < T) T = s; } else s++;
  H = zero_zv(r + 1 - T);
  for (k = 1, s = 0; k <= 2*r; k++) /* (x^-T * Hodge) += x^s, s - T >= 0 */
    if (w[k] > r) s--; else { H[s + 1 - T]++; s++; }
  *pTT = -T; return zv_to_zx(H, evalvarn(0));
}

/* Conversion from [val] to cyclotomic factorization: t_VECSMALL E encodes
 * prod_i polcyclo(i)^E[i] */
static GEN
al2cyE(GEN v)
{
  GEN dv, E, F, w;
  long N, i, j, l = lg(v);
  if (l == 1) return cgetg(1, t_VECSMALL);
  w = Q_remove_denom(v, &dv);
  if (!dv) return mkvecsmall(l-1);
  N = itou(dv); w = ZV_to_Flv(w, N); vecsmall_sort(w);
  E = zero_zv(N); /* to record polcyclo(i)^E[i] */
  F = cgetg(l, t_VECSMALL); /* to check input */
  for (i = j = 1; i < l; i++)
  {
    long k, m = w[i];
    if (!m) { E[1]++; F[j++] = 0; }
    else if (N % m == 0)
    {
      long d = N/m, km;
      E[d]++;
      for (k = 1, km = m; k <= d; k++, km += m)
        if (ugcd(k,d) == 1) F[j++] = km;
    }
  }
  setlg(F,j); vecsmall_sort(F);
  return gequal(w,F)? E: NULL;
}

static int
cyE_intersect(GEN a, GEN b)
{
  long i, l = minss(lg(a), lg(b));
  for (i = 1; i < l; i++) if (a[i] && b[i]) return 1;
  return 0;
}
static GEN
get_CYCLOE(GEN val, GEN vbe)
{
  GEN Ea = al2cyE(val), Eb = al2cyE(vbe);
  if (!Ea || !Eb || cyE_intersect(Ea, Eb))
    pari_err_TYPE("hgminit [not a Q motive]", mkvec2(val,vbe));
  return mkvec2(Ea, Eb);
}

/* R[n/d] += mu(d) * r, for all d | n */
static void
moebiusadd(GEN R, long n, long r)
{
  if (r) {
    GEN D = divisorsu_moebius(gel(factoru(n), 1));
    long j, l = lg(D);
    R[n] += r; /* d = 1 */
    for (j = 2; j < l; j++) { long d = D[j]; R[n / labs(d)] += d < 0? -r: r; }
  }
}
/* Use Phi_n(x) = Prod_{d|n} (x^d-1)^mu(n/d); Ea/Eb in terms of (x^i-1) */
static GEN
get_VPOLGA(GEN E)
{
  GEN Ea = gel(E,1), Eb = gel(E,2), R;
  long i, la = lg(Ea), lb = lg(Eb), n = maxuu(la, lb) - 1;
  pari_sp av;
  R = zero_zv(n); av = avma;
  for (i = 1; i < la; i++) moebiusadd(R, i, Ea[i]);
  for (i = 1; i < lb; i++) moebiusadd(R, i, -Eb[i]);
  for (i = n; i; i--) if (R[i]) break;
  setlg(R,i+1); set_avma(av); return R;
}

/* disc(polcyclo(n)) modulo squares */
static GEN
cyclodiscmodsq(ulong n)
{
  long e, s;
  ulong p;

  if (n <= 2) return gen_1;
  if ((n & 3) == 2) n >>= 1;
  e = uisprimepower(n, &p);
  if (!e) return gen_1;
  if (p == 2) return e == 2? gen_m1: gen_1;
  s = odd(e)? p: 1;
  if ((p & 3) == 3) s = -s;
  return stoi(s);
}
/* E encodes prod polcyclo(i)^E(i) */
static GEN
discprod(GEN E)
{
  long i, j, l = lg(E);
  GEN P = cgetg(l, t_VEC);
  for (i = 3, j = 1; i < l; i++) /* can skip polcyclo(1 or 2) */
    if (odd(E[i])) gel(P,j++) = cyclodiscmodsq(i);
  setlg(P,j); return ZV_prod(P);
}

/* Fundamental initialization of hgm independent of t */
static GEN
normalizeval(GEN val)
{
  long l = lg(val), i;
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(val, i);
    if (!is_rational_t(typ(c)))
      pari_err_TYPE("hgminit [not rational params]",c);
    gel(v, i) = gfrac(c);
  }
  return v;
}

static GEN
mangoldtexp(long n)
{
  GEN D = divisorsu_moebius(gel(factoru(n),1)), P = gen_1;
  long i, l = lg(D);
  for (i = 1; i < l; i++)
  { /* prod (n/d) ^ (n/d mu(d)) */
    long mud = D[i], nd = n / mud; /* mud = mu(d) * d */
    P = gmul(P, powis(utoi(labs(nd)), nd));
  }
  return P;
}
static GEN
E2exp(GEN E)
{
  long n, r, l = lg(E);
  GEN P = gen_1;
  for (n = 1; n < l; n++)
    if ((r = E[n])) P = gmul(P, gpowgs(mangoldtexp(n), r));
  return P;
}
static long
get_b1(GEN CYCLOE) { return gel(CYCLOE,2)[1]; }

static GEN get_u(GEN al, GEN be, GEN CYCLOE, GEN VPOLGA, long DEG, long WT);
static GEN
initalbe(GEN val, GEN vbe)
{
  GEN VALNUM, VALDEN, VBENUM, VBEDEN, CYCLOE, SIGNPAR;
  GEN BAD, HODGE, VPOLGA, res;
  long j, WT, TT, OFFMPOL, l = lg(val), DEG = l-1, SWAP = 0;

  if (lg(vbe) != l) pari_err_TYPE("hgminit [#al != #be]", mkvec2(val,vbe));
  val = normalizeval(val);
  vbe = normalizeval(vbe);
  if (RgV_isin(val, gen_0))
  {
    if (RgV_isin(vbe, gen_0))
      pari_err_TYPE("hgminit [nonempty intersection]", mkvec2(val,vbe));
    swap(val, vbe); SWAP = 1;
  }
  VALNUM = cgetg(l, t_VECSMALL);
  VALDEN = cgetg(l, t_VECSMALL);
  VBENUM = cgetg(l, t_VECSMALL);
  VBEDEN = cgetg(l, t_VECSMALL);
  for (j = 1; j < l; j++)
  {
    Qtoss(gel(val,j), &VALNUM[j], &VALDEN[j]);
    Qtoss(gel(vbe,j), &VBENUM[j], &VBEDEN[j]);
  }
  BAD = negi(lcmii(ZV_lcm(zv_to_ZV(VALDEN)), ZV_lcm(zv_to_ZV(VBEDEN))));
  HODGE = hodge(val, vbe, &TT);
  WT = degpol(HODGE);
  CYCLOE = get_CYCLOE(val, vbe);
  VPOLGA = get_VPOLGA(CYCLOE);
  SIGNPAR = odd(WT)? gen_1: discprod(gel(CYCLOE, odd(DEG)? 2: 1));
  OFFMPOL = (get_b1(CYCLOE) - zv_sum(VPOLGA)) >> 1;
  res = cgetg(13, t_VEC);
  gel(res, 1) = val;
  gel(res, 2) = vbe;
  gel(res, 3) = CYCLOE;
  gel(res, 4) = VBENUM;
  gel(res, 5) = VBEDEN;
  gel(res, 6) = gdiv(E2exp(gel(CYCLOE,1)), E2exp(gel(CYCLOE,2))); /*MVALUE*/
  gel(res, 7) = VPOLGA;
  gel(res, 8) = BAD;
  gel(res, 9) = HODGE;
  gel(res, 10) = get_u(val, vbe, CYCLOE, VPOLGA, DEG, WT);
  gel(res, 11) = SIGNPAR;
  gel(res, 12) = mkvecsmall3(OFFMPOL, TT, SWAP);
  return res;
}
static int
checkhgm(GEN v)
{
  return typ(v) == t_VEC && lg(v) == 13
      && typ(gel(v,12)) == t_VECSMALL && lg(gel(v,12)) == 4;
}

/* accessors */
static GEN hgm_get_VAL(GEN v) { return gel(v, 1); }
static GEN hgm_get_VBE(GEN v) { return gel(v, 2); }
static GEN hgm_get_CYCLOE(GEN v) { return gel(v, 3); }
static GEN hgm_get_VBENUM(GEN v) { return gel(v, 4); }
static GEN hgm_get_VBEDEN(GEN v) { return gel(v, 5); }
static GEN hgm_get_MVALUE(GEN v) { return gel(v, 6); }
static GEN hgm_get_VPOLGA(GEN v) { return gel(v, 7); }
static GEN hgm_get_BAD(GEN v) { return gel(v, 8); }
static GEN hgm_get_HODGE(GEN v) { return gel(v, 9); }
static GEN hgm_get_U(GEN v) { return gmael(v, 10,1); }
static GEN hgm_get_U0(GEN v) { return gmael(v, 10,2); }
static GEN hgm_get_SIGNPAR(GEN v) { return gel(v, 11); }
static long hgm_get_DEG(GEN v) { return lg(hgm_get_VAL(v))-1; }
static long hgm_get_OFFMPOL(GEN v) { return gel(v, 12)[1]; }
static long hgm_get_TT(GEN v) { return gel(v, 12)[2]; }
static long hgm_get_SWAP(GEN v) { return gel(v, 12)[3]; }
static long hgm_get_WT(GEN v) { return degpol(hgm_get_HODGE(v)); }

/***************************************************************/
/*                 PART II: p-adic functions                   */
/***************************************************************/

/* Compute p^k u_{pk+r} for 0 <= r < p and 0 <= k < ell */
static GEN
compu(long ell, long p, long D)
{
  GEN v = cgetg(p + 1, t_VEC), w = cgetg(ell + 2, t_VEC);
  long s, t, k, i, L = ell * p;

  gel(v,1) = gel(v,2) = cvtop(gen_1, stoi(p), D);
  for (i = 2; i < p; i++) gel(v, i+1) = gdivgs(gel(v, i), i);
  gel(w, 1) = shallowcopy(v);
  for (k = s = 1, t = p; k <= L; k++)
  {
    gel(v, s) = gdivgs(gadd(gel(v, t), gel(v, s)), k + p - 1);
    if (++s > p) { s = 1; gel(w, k/p + 1) = shallowcopy(v); }
    if (++t > p) t = 1;
  }
  return w;
}

/* [binom(x + k - 1, k) k! p^k, k = 1..N], x a t_PADIC */
static GEN
binomfact(GEN x, long N)
{
  GEN z, v = cgetg(N+1, t_VEC);
  long i;
  gel(v,1) = z = leafcopy(x);
  setvalp(z, valp(z)+1);
  for (i = 1; i < N; i++)
  {
    gel(v, i+1) = z = gmul(z, gaddgs(x, i));
    setvalp(z, valp(z) + 1);
  }
  return v;
}
/* gamma(m /p^f-1) mod p^dfp, m = m0 (mod p), x = (m\p + m0*p^(f-1)) / p^f-1 */
static ulong
sumbinom(GEN v, GEN x, long m0, long N, ulong pD)
{
  pari_sp av = avma;
  GEN C = binomfact(x, N), S = gmael(v, 1, m0+1); /* k = 0 */
  long k;
  for (k = 1; k <= N; k++) S = gadd(S, gmul(gel(C,k), gmael(v, k+1, m0+1)));
  return gc_ulong(av, Rg_to_Fl(S, pD));
}
/* x * y mod p^D, y a p-unit */
static GEN
umultop(ulong x, ulong y, GEN gp, GEN gpD, long D)
{
  ulong pD = gpD[2];
  long v;
  GEN z;
  if (!x) return zeropadic(gp, D);
  v = u_lvalrem(x, gp[2], &x);
  if (x >= pD) x %= pD;
  z = cgetg(5, t_PADIC);
  z[1] = evalprecp(D) | evalvalp(v);
  gel(z,2) = gp;
  gel(z,3) = gpD;
  gel(z,4) = utoi( Fl_mul(x, y, pD) ); return z;
}

/* Compute all gamma(m/(p^f-1)) mod p^D for 0 <= m < p^f-1 */
static GEN
precomp(long p, long f, long D)
{
  pari_sp av, av2;
  GEN vall, gp, gpD, vres, x, l2;
  long m, m0, m1, M, q, v, vpo, vva, vpowv, pf1;
  long N = ceildivuu(D * p, p-1), pf = upowuu(p,f), pD = upowuu(p, D), pM;
  long ga12, S, Q = pf - 1, iQ = D <= f? pD - 1: Fl_inv(Q, pD);

  vres = cgetg(pf, t_VECSMALL); vres[1] = 1; av = avma;
  gp = utoipos(p); gpD = utoipos(pD);
  vall = compu(N, p, D);
  if (p == 2)
  {
    if (f == 1) return gc_const(av, vres);
    av2 = avma;
    for (m = 1; m < Q; m++, set_avma(av2))
    {
      m0 = m&1, m1 = m >> 1;
      x = umultop(m1 + (m0 << (f - 1)), iQ, gp, gpD, D);
      vres[m+1] = sumbinom(vall, x, m0, N, pD);
    }
    return gc_const(av, vres);
  }
  q = Q >> 1; pf1 = pf / p;
  vva = z_lval(Q, 2); vpowv = 1 << vva;
  av2 = avma;
  for (m = 1; m <= q; m += 2, set_avma(av2))
  {
    if (f > 1) { m0 = m%p; m1 = m / p; M = m1 + m0 * pf1; } else M = m0 = m;
    x = umultop(M, iQ, gp, gpD, D);
    vres[m+1] = S = sumbinom(vall, x, m0, N, pD);
    if (!odd(m0)) S = pD - S;
    vres[pf - m] = Fl_inv(S, pD);
  }
  for (m = vpowv; m <= q; m += 2*vpowv, set_avma(av2))
  {
    if (f > 1) { m0 = m%p; m1 = m / p; M = m1 + m0 * pf1; } else M = m0 = m;
    x = umultop(M, iQ, gp, gpD, D);
    vres[m+1] = S = sumbinom(vall, x, m0, N, pD);
    if (!odd(m0)) S = pD - S;
    vres[pf - m] = Fl_inv(S, pD);
  }
  l2 = gmulsg(p - 1, Qp_log(cvtop(gen_2, gp, D)));
  ga12 = Fl_inv(Rg_to_Fl(Qp_gamma(cvtop(ghalf, gp, D)), pD), pD);
  pM = maxuu(pD, pf); av2 = avma;
  for (v = 1, vpo = 2; vpo < Q; v++, vpo <<= 1)
  {
    if (v == vva) continue;
    for (m = vpo; m <= q; m += 2*vpo, set_avma(av2))
    {
      long ms2 = (m >> 1) + 1;
      long t = Fl_mul(Fl_mul(vres[ms2], vres[ms2+q], pD), ga12, pD);
      GEN mp;
      /* - m  = -m1 * p + m0, 1 <= m0 <= p */
      m0 = p - m%p; m1 = m/p + 1; M = pM + m1 - m0 * pf1;
      mp = umultop(M, iQ, gp, gpD, D);
      S = Rg_to_Fl(gmul2n(gmulgs(Qp_exp(gmul(mp, l2)), t), m0-1), pD);
      vres[m+1] = S;
      if (odd(m0)) S = pD - S;
      vres[pf - m] = Fl_inv(S, pD);
    }
  }
  return gc_const(av, vres);
}

static long
get_pad(long p)
{ switch(p) {
    case 2: return 18;
    case 3: return 11;
    case 5: return  8;
    default:return  6; }}

GEN
Flv_red(GEN z, ulong p)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) x[i] = uel(z,i)%p;
  return x;
}

static GEN
block0(long l)
{
  GEN v = cgetg_block(l, t_VEC);
  long i;
  for (i = 1; i < l; i++) gel(v,i) = gen_0;
  return v;
}

/* f > 0, p prime */
static GEN
doprecomp(long p, long f, long dfp)
{
  GEN t, T;
  long m, q, F;
  if (f > 3 || (F = get_pad(p)) > dfp) return precomp(p, f, dfp);
  if (f == 3)
  {
    T = HGMDATA3; if (!T) T = HGMDATA3 = block0(100);
    if (p >= lg(T)) return precomp(p, f, dfp);
    t = gel(T,p);
    if (typ(t) == t_INT) t = gel(T,p) = gclone(precomp(p, f, F));
    if (F == dfp) return t;
    return Flv_red(t, upowuu(p, dfp));
  }
  /* f <= 2, dfp <= F */
  T = HGMDATA2; if (!T) T = HGMDATA2 = block0(1000);
  if (p >= lg(T)) return precomp(p, f, dfp);
  t = gel(T,p);
  if (typ(t) == t_INT)
  {
    if (f == 1) return precomp(p, f, dfp);
    t = gel(T,p) = gclone(precomp(p, f, F));
  }
  /* t = precomp(p, 2, dfp) = HGMDATA2[p] */
  if (f == 2)
  {
    if (F == dfp) return t;
    return Flv_red(t, upowuu(p, dfp));
  }
  /* f = 1 */
  T = cgetg(p, t_VECSMALL); q = upowuu(p, dfp);
  for (m = 1; m < p; m++) T[m] = uel(t, (m-1)*(p+1) + 1) % q;
  return T;
}

/* W[N] = teich(N ^ (N * sign(VPOLGA[N]))) mod p^2 */
static GEN
teichmodp2(GEN VPOLGA, long p, long PSQ)
{
  long c, l, N, pN;
  GEN W = cgetg_copy(VPOLGA,&l); /* W[N] = teich(N)^N */
  for (N = 1, pN = p; N < l; N++, pN += p)
    if ((c = VPOLGA[N]))
    {
      long N0; (void)z_lvalrem(N, p, &N0);
      if (c < 0) N0 = Fl_inv(N0 % p, p);
      W[N] = Fl_powu(N0, pN, PSQ);
    }
  return W;
}
/* GF[i] = i! mod p^2 */
static GEN
get_GF(long p, long PSQ)
{
  GEN F = cgetg(p, t_VECSMALL);
  long i;
  F[1] = 1; F[2] = 2; for (i = 3; i < p; i++) F[i] = Fl_mul(F[i-1], i, PSQ);
  return F;
}

/* p odd, return v s.t. v[i] = 1/i mod p, i < p/2 */
static GEN
Flv_inv_p2(ulong p)
{
  long i, g = pgener_Fl(p), p2 = (p >> 1);
  GEN v = cgetg(p2 + 1, t_VECSMALL);
  pari_sp av = avma;
  GEN w = cgetg(p2, t_VECSMALL);
  w[1] = g;
  for (i = 2; i < p2; i++) w[i] = Fl_mul(w[i-1], g, p); /* w[i]=g^i */
  for (i = 1; i < p2; i++)
  {
    long x = w[i], y = w[p2 - i]; /* g^(-i) = - g^(p2 - i) */
    if (x > p2) v[p - x] = y; else v[x] = p - y; /* 1/(-x) = y, 1/x = -y */
  }
  v[1] = 1; return gc_const(av, v);
}

/* H[i] = i * (H_i - ((p-1)! + 1) / p) mod p */
static GEN
get_GH(GEN F, long p)
{
  long i, g, p2 = p >> 1;
  GEN H = cgetg(p, t_VECSMALL), v = Flv_inv_p2(p);
  H[p-1] = (F[p-1] + 1) / p; g = p - H[p-1];
  for (i = 1; i <= p2; i++)
  {
    long c = g = Fl_add(g, v[i], p);
    H[i] = c = Fl_mul(c, i, p);
    H[p-1 - i] = Fl_neg(Fl_add(c, g, p), p);
  }
  return H;
}
/* p odd, GPB[m+1] = Gamma_p(m/(p-1)) mod p^2 */
static GEN
doprecompmodp2(long p, long PSQ)
{
  GEN F = get_GF(p, PSQ), H = get_GH(F, p), GPV = cgetg(p, t_VECSMALL);
  long r;
  for (r = 1; r < p; r++)
  {
    long t = Fl_mul(F[r], 1 + p * H[r], PSQ);
    GPV[p - r] = odd(r)? t: PSQ-t;
  }
  return GPV;
}

/***************************************************************/
/*        PART III: Motive initializations depending on p      */
/***************************************************************/
static GEN
get_L1(GEN hgm, long PFM1, long f)
{
  GEN VBEDEN = hgm_get_VBEDEN(hgm);
  GEN VBENUM = hgm_get_VBENUM(hgm), v;
  long DEG = hgm_get_DEG(hgm), j;
  v = const_vecsmall(PFM1, f * hgm_get_TT(hgm));
  for (j = 1; j <= DEG; j++)
    if (PFM1 % VBEDEN[j] == 0)
    {
      long t = ((-(PFM1 / VBEDEN[j]) * VBENUM[j]) % PFM1) + 1;
      if (t <= 0) t += PFM1;
      v[t] -= f;
    }
  return v;
}
/* Stickelberger valuation: L0(p, f, m), power of (-p)
 * = f * OFFMPOL - sum_{e < f, N < l} gamma_N [N p^e m / (p^f-1)]*/
/* 1) amortized (all m < p^f-1), good when p >> N log N. Assume f=1 */
static GEN
get_L0(GEN hgm, long PM1)
{
  GEN perm, vt, vc, VL0, VPOLGA = hgm_get_VPOLGA(hgm);
  long w, S, c, d, j, N, m, l = lg(VPOLGA), D = (l * (l-1)) >> 1;
  vt = cgetg(D+1, t_VECSMALL);
  vc = cgetg(D+1, t_VECSMALL);
  for (N = 2, c = 1; N < l; N++)
    if (VPOLGA[N])
    {
      long q, Q;
      for (q = 1, Q = 0; q <= N; q++, Q += PM1, c++)
      {
        vt[c] = ceildivuu(Q, N);
        vc[c] = VPOLGA[N];
      }
    }
  setlg(vt,c); setlg(vc,c); perm = vecsmall_indexsort(vt);
  vt = vecsmallpermute(vt, perm);
  vc = vecsmallpermute(vc, perm);
  w = vt[1];
  for (j = 2, d = 1; j < c; j++)
    if (vt[j] == w) vc[d] += vc[j];
    else
    {
      d++;
      vt[d] = w = vt[j];
      vc[d] = vc[j];
    }
  d++; vt[d] = PM1; vc[d] = 0; /* sentinels */
  VL0 = cgetg(PM1+1, t_VECSMALL); S = hgm_get_OFFMPOL(hgm);
  for (j = 1; j < d; j++)
  {
    for (m = vt[j]; m < vt[j+1]; m++) VL0[m+1] = S;
    S -= vc[j+1];
  }
  return VL0;
}
/* 2) direct computation (single m), good when p << N log N */
static long
L0(GEN hgm, long p, long f, long PFM1, long m)
{
  GEN VPOLGA = hgm_get_VPOLGA(hgm);
  long e, pem, S = hgm_get_OFFMPOL(hgm) * f, l = lg(VPOLGA);
  for (e = 0, pem = m; e < f; e++, pem *= p)
  {
    long N, Npem, s = 0;
    for (N = 1, Npem = pem; N < l; N++, Npem += pem)
      if (VPOLGA[N]) s += VPOLGA[N] * (Npem / PFM1);
    S -= s;
  }
  return S;
}

static GEN
get_teich1(GEN VPOLGA, GEN ZP, long p)
{
  long l = lg(VPOLGA), N;
  GEN v = zerovec(l - 1);
  for (N = 2; N < l; N++)
    if (VPOLGA[N])
    {
      long N0; (void)z_lvalrem(N, p, &N0);
      gel(v, N) = teich(gaddsg(N0, ZP));
    }
  return v;
}
static GEN
get_teich(GEN VPOLGA, GEN ZP, long p, long f, long PFM1)
{
  GEN v, Q;
  long l, N;
  if (f == 1) return get_teich1(VPOLGA, ZP, p);
  l = lg(VPOLGA); v = zerovec(l - 1); Q = utoipos(PFM1 / (p - 1));
  for (N = 2; N < l; N++)
    if (VPOLGA[N])
    {
      long N0; (void)z_lvalrem(N, p, &N0);
      gel(v,N) = Qp_sqrtn(gdivsg(N0, teich(gaddsg(N0,ZP))), Q, NULL);
    }
  return v;
}

/* compute N^{-[N*s-1-(N*s-1)\p]}, N*s=a/(p^f-1) with a=N*m*p^e */
static GEN
gapnpow(GEN T, long p, long f, long PFM1, long N, ulong Nmpe)
{
  GEN Vr;
  long Nm, i, S;

  if (f == 1) return gpowgs(T, Nmpe);
  Nm = Fl_neg(Nmpe, PFM1);
  Vr = cgetg(f + 1, t_VECSMALL);
  for (i = 1; i <= f; i++) { Vr[i] = Nm % p; Nm /= p; }
  S = Vr[1]; for (i = 1; i < f; i++) S = Vr[f + 1 - i] + p * S;
  return gdiv(gpowgs(T, S), powuu(N, Vr[1]));
}

/* prod_{j = 1}^DEG prod_{e = 0}^{f - 1}
 *   gamma_p({p^e * (VAL[j] + m/(p^f-1))}) /
 *   gamma_p({p^e * (VBE[j] + m/(p^f-1))}), a p-unit. 0 <= m < p^f-1 */
static GEN
hgmC(GEN VPOLGA, GEN GPV, GEN TEICH, long p, long f, long PFM1, long m, long dfp)
{
  GEN r = gen_1;
  long c, Nmpe, mpe, e, N, l = lg(VPOLGA);
  for (e = 0, mpe = m; e < f; e++, mpe = Fl_mul(mpe, p, PFM1))
    for (N = 1, Nmpe = mpe; N < l; N++, Nmpe = Fl_add(Nmpe, mpe, PFM1))
      if ((c = VPOLGA[N]))
      { /* Gamma_p(frac(N*m*p^e/(p^f-1)))  */
        GEN z = utoi(GPV[Nmpe + 1]);
        if (N > 1) z = gmul(z, gapnpow(gel(TEICH, N), p, f, PFM1, N, Nmpe));
        /* z = prod_{0 <= j < N} Gamma_p( frac(p^e * (m/(p^f-1) + j/N)) ) */
        r = gmul(r, gpowgs(z, c));
      }
  if (typ(r) != t_PADIC) r = cvtop(r, utoipos(p), dfp);
  return r;
}

/* Same modulo p^2, Wm[N] = teich(N^(sign(VPOLGA[N]) * m)) */
static ulong
hgmCmodp2(GEN VPOLGA, GEN Wm, GEN GPV, long PFM1, long m, long PSQ)
{
  long l = lg(VPOLGA), c, N;
  ulong res = 1, Nm;
  for (N = 1, Nm = m; N < l; N++, Nm = Fl_add(Nm, m, PFM1))
    if ((c = VPOLGA[N]))
    {
      ulong z;
      if (c > 0) z = GPV[Nm + 1];
      else
      {
        c = -c;
        if (!Nm) z = 1;
        else
        {
          z = GPV[PFM1 + 1 - Nm];
          if (!odd(Nm)) z = PSQ - z; /* GPV[Nm+1]^(-1) by reflection formula */
        }
      }
      if (N > 1) z = Fl_mul(z, Wm[N], PSQ);
      z = Fl_powu(z, c, PSQ);
      /* z = (GPV[Nm+1] * teich(N^m))^VPOLGA[N] */
      res = res == 1? z: Fl_mul(res, z, PSQ);
    }
  return res;
}

/***************************************************************/
/*        PART IV: Motive functions depending on p, t          */
/***************************************************************/
static long
get_dfp(GEN hgm, long p, long f)
{
  long DEG = hgm_get_DEG(hgm), WT = hgm_get_WT(hgm);
  long dfp = ceil(log((double)2*DEG) / log((double)p) + f * (WT * 0.5 ) + 1e-5);
  if (p == 2) dfp++; /* FIXME: why ? */
  return dfp;
}
/* V being a vecsmall, compute all p^TT*hgmC(m)/hgmC(0) for indices in V */
static GEN
hgmCall(GEN hgm, long p, long f, GEN V)
{
  GEN v, c, GPV, VL0, VL1, TEICH;
  GEN VPOLGA = hgm_get_VPOLGA(hgm), ZP;
  long i, L, l0, PFM1 = upowuu(p, f) - 1, lV = V? lg(V): PFM1+1;
  long fTT = f * hgm_get_TT(hgm), dfp = get_dfp(hgm, p, f);

  GPV = doprecomp(p, f, dfp);
  VL0 = (V && f == 1)? get_L0(hgm, PFM1): NULL;
  VL1 = get_L1(hgm, PFM1, f);
  ZP = zeropadic(utoipos(p), dfp);
  TEICH = get_teich(VPOLGA, ZP, p, f, PFM1);
  l0 = hgm_get_OFFMPOL(hgm) * f;
  v = cgetg(lV, t_VEC); i = 1; /* m = 0 */
  if (!V) { gel(v,i++) = c = gadd(gen_1, ZP); setvalp(c, valp(c) + fTT); }
  for (; i < lV; i++)
  {
    long e, m = V? V[i]: i-1;
    L = VL0? VL0[m+1]: L0(hgm, p, f, PFM1, m);
    e = L + VL1[m+1];
    if (!V && e >= dfp) c = gen_0;
    else
    { /* FIXME: dfp is fishy in Jordantame, don't trust if V = NULL */
      pari_sp av = avma;
      c = hgmC(VPOLGA, GPV, TEICH, p, f, PFM1, m, dfp);
      setvalp(c, e); if (odd(L ^ l0)) c = gneg(c);
      c = gerepileupto(av, c);
    }
    gel(v,i) = c;
  }
  return mkvec5(v, ZP, utoipos(p), utoipos(f), V? V : gen_0);
}

/* General H function */
static GEN
hgmH(GEN Call, GEN t)
{
  GEN C = gel(Call, 1), ZP = gel(Call, 2), v, c0;
  long p = itos(gel(Call, 3)), f = itos(gel(Call, 4));
  long l = lg(t), j;
  v = cgetg(l, t_VEC);
  c0 = ginv(gaddsg(1 - (long)upowuu(p, f), ZP));
  for (j = 1; j < l; j++)
  {
    GEN z = poleval(C, teich(gadd(gel(t, j), ZP)));
    gel(v,j) = centerlift(gmul(z, c0));
  }
  return v;
}

/* Same mod p^2, f = 1 */
static GEN
hgmCallmodp2(GEN hgm, long p)
{
  GEN C, GPV, VL0, VL1, W1, Wm, VPOLGA = hgm_get_VPOLGA(hgm);
  long m, l = lg(VPOLGA), PSQ = p * p, PFM1 = p - 1, TT = hgm_get_TT(hgm);

  VL0 = get_L0(hgm, PFM1);
  VL1 = get_L1(hgm, PFM1, 1);
  W1 = teichmodp2(VPOLGA, p, PSQ);
  Wm = shallowcopy(W1);
  GPV = doprecompmodp2(p, PSQ);
  C = cgetg(PFM1+2, t_VECSMALL); C[1] = evalvarn(0);
  C[2] = TT > 1? 0: (TT == 1? p : 1); /* m = 0 */
  for (m = 1; m < PFM1; m++)
  {
    long e = VL0[m + 1] + VL1[m + 1], c, j;
    if (e >= 2) c = 0;
    else
    {
      c = hgmCmodp2(VPOLGA, Wm, GPV, PFM1, m, PSQ);
      if (odd(VL0[m + 1] ^ VL0[1])) c = Fl_neg(c, PSQ);
      if (e == 1) c = (c % p) * p;
    }
    C[m + 2] = c;
    for (j = 2; j < l; j++)
      if (VPOLGA[j]) Wm[j] = Fl_mul(Wm[j], W1[j], PSQ);
  }
  return mkvec4(C, gen_0, utoipos(p), gen_1);
}

static GEN
hgmCallboth(GEN hgm, long p, long f, GEN V)
{
  long fl = (f == 1 && get_dfp(hgm, p, f) <= 2);
  return fl ? hgmCallmodp2(hgm, p) : hgmCall(hgm, p, f, V);
}

static GEN
hgmHmodp2(GEN Callmodp2, GEN t)
{
  GEN C = gel(Callmodp2, 1), v;
  long p = itos(gel(Callmodp2, 3)), p2 = p * p, ph = p2 >> 1, c0 = 1 + p;
  long l = lg(t), j;

  v = cgetg(l, t_VEC);
  for (j = 1; j < l; j++)
  {
    ulong wt = Fl_powu(Rg_to_Fl(gel(t, j), p2), p, p2);
    gel(v,j) = stoi( Fl_center(Fl_mul(Flx_eval(C, wt, p2), c0, p2), p2, ph) );
  }
  return v;
}

enum { C_OK = 0, C_FAKE, C_BAD, C_TAME0, C_TAME1};
static GEN hgmU(GEN hgm, long p, long f, GEN t, long dfp);
static long hgmclass(GEN hgm, long p, GEN t);
static GEN
hgmtrace(GEN hgm, GEN Call, GEN t, GEN C)
{
  long p = itos(gel(Call, 3)), f = itos(gel(Call, 4)), dfp = get_dfp(hgm, p, f);
  if (C[1] == C_FAKE) return hgmU(hgm, p, f, t, dfp);
  return (f == 1 && dfp <= 2)? hgmHmodp2(Call, t): hgmH(Call, t);
}

static GEN
F2v_factorback(GEN E)
{
  long i, l = lg(E);
  GEN c = gen_1;
  for (i = 1; i < l; i++)
    if (odd(E[i])) c = muliu(c, i);
  return c;
}

static long
Q_krois(GEN T, long p) { return krouu(Rg_to_Fl(T, (p == 2)? 8: p), p); }
static long
hgmsign(GEN hgm, long p, GEN t)
{
  GEN u;
  if (odd(hgm_get_WT(hgm))) return 1;
  t = ginv(t); u = gmul(gsubsg(1, t), hgm_get_SIGNPAR(hgm));
  return odd(hgm_get_DEG(hgm))? -Q_krois(u, p): Q_krois(gmul(gneg(t), u), p);
}
/* conductor of the central character */
static GEN
hgmcharcond(GEN hgm, GEN t)
{
  GEN u;
  if (odd(hgm_get_WT(hgm))) return gen_1;
  t = ginv(t); u = gmul(gsubsg(1, t), hgm_get_SIGNPAR(hgm));
  if (!odd(hgm_get_DEG(hgm))) u = gmul(gneg(t), u);
  if (typ(u) == t_FRAC) u = mulii(gel(u,1), gel(u,2));
  return gequal0(u) ? gen_1 : coredisc(u);
}
/* valuations of central character conductor at BAD */
static GEN
get_achi(GEN hgm, GEN t, GEN BAD)
{
  long i, l = lg(BAD);
  GEN Nchi = hgmcharcond(hgm, t), v = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) v[i] = Z_lval(Nchi, BAD[i]);
  return v;
}

/* complete local factor E (of degree d) at p using functional equation
 * E(T) = SIGN p^(WT*d)/2 T^d E(1/(p^WT*T)) */
static GEN
Efuneq(GEN E, GEN vp, long d, long SIGN, long B)
{
  long j = maxss(d - B, 0), k = d + 1 - j, nE = lg(E)-1, l = (d + 1) >> 1;
  GEN T = cgetg(k + 1, t_VEC);
  for (; j < l; j++, k--)
  {
    GEN q = gel(vp,l-j);
    if (SIGN < 0) q = negi(q); /* q = SIGN * p^(WT(d-2*j) >> 1) */
    gel(T, k) = gmul(q, RgX_coeff(E, j));
  }
  for (; k >= nE; k--) gel(T, k) = gen_0;
  for (; k > 0; k--) gel(T, k) = gel(E, k+1);
  return RgV_to_RgX(T,0);
}

/* [a,a*r, ..., a*r^n] */
static GEN
upowers_u(ulong r, long n, ulong a)
{
  long i, l = n + 2, t = a;
  GEN v = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) { v[i] = t; t *= r; }
  return v;
}
static GEN
powers_u(ulong r, long n, ulong a)
{
  long i, l = n + 2;
  GEN v = cgetg(l, t_VEC), t = utoi(a);
  for (i = 1; i < l; i++) { gel(v,i) = t; t = muliu(t, r); }
  return v;
}
static GEN
mkpowers(long p, long DEG, long WT)
{
  ulong q, r;
  if (WT == 0) q = r = 1;
  else if (!odd(DEG)) q = r = upowuu(p, WT);
  else if (WT == 1) { q = 1; r = p; }
  else { q = upowuu(p, WT >> 1); r = q*q; if (odd(WT)) r *= p; }
  return powers_u(r, (DEG-1)>>1, q);
}

static long
hgmclass(GEN hgm, long p, GEN t)
{
  GEN BAD = hgm_get_BAD(hgm);
  long ap, bp;
  if (!umodiu(BAD, p))
  {
    long v = Q_lval(t, p);
    if (v && v + Q_lval(hgm_get_MVALUE(hgm), p) == 0)
    {
      GEN N = hgmcharcond(hgm, t);
      if (umodiu(N, p)) return C_FAKE; /* a(chi) = 0 */
    }
    return C_BAD;
  }
  if (typ(t) == t_INT)
  {
    ap = umodiu(t, p); if (!ap) return C_TAME0;
    bp = 1;
  }
  else
  {
    ap = umodiu(gel(t,1), p); if (!ap) return C_TAME0;
    bp = umodiu(gel(t,2), p); if (!bp) return C_TAME0;
  }
  return ap == bp? C_TAME1 : C_OK;
}
static int
hgmadditive(long c) { return (c == C_BAD || c == C_TAME0); }

/* p good or Tame1; return local factor at p: 1/E + O(x^(B+1)); t a t_VEC,
 * C a t_VECSMALL giving their class. FIXME: t a vector of values now
 * useless: can call hgmCall or hgmQ[all] which do not depend on t; then
 * evaluate polynomial at t */
static GEN
frobpoltrunc(GEN hgm, GEN t, GEN C, long p, long B, GEN* pF)
{
  GEN S, vp, vp1, F;
  long DEG = hgm_get_DEG(hgm), DEG2, WT = hgm_get_WT(hgm);
  long f, i, mi, lt = lg(t), q = upowuu(p, WT >> 1), DEGNEW = DEG;

  /* FIXME: what if not first ? */
  if (gequal1(gel(t, 1))) { DEGNEW = odd(WT) ? DEG - 2 : DEG - 1; }
  DEG2 = DEGNEW >> 1;
  mi = minss(B, (C[1] == C_FAKE)? DEGNEW: DEG2); /* if one is fake, all are */
  S = cgetg(lt, t_VEC); F = zero_zv(lt - 1);
  for (i = 1; i < lt; i++) gel(S,i) = cgetg(mi+1, t_VEC);
  for (f = 1; f <= mi; f++)
  { /* FIXME: f = mi unused if C_TAME1 and even DEG */
    GEN Call = hgmCallboth(hgm, p, f, NULL), co = hgmtrace(hgm, Call, t, C);
    for (i = 1; i < lt; i++) gmael(S, i, f) = negi(gel(co, i));
  }
  vp = vp1 = NULL;
  for (i = 1; i < lt; i++)
  {
    GEN E, s = RgV_to_RgX(gel(S,i), 0);;
    long minew = (mi == DEGNEW && C[i] == C_TAME1 && !odd(DEG))? mi: mi+1;
    s = RgXn_expint(s, minew);
    if (mi == DEGNEW) { gel(S,i) = s; continue; }
    if (C[i] == C_TAME1)
    {
      long SIGN = kroiu(hgm_get_U(hgm), p);
      if (odd(DEG))
      {
        if (!vp1) vp1 = mkpowers(p,DEG-1,WT);
        E = Efuneq(s, vp1, DEG-1, SIGN, B);
      }
      else
      {
        GEN T = deg1pol_shallow(stoi(- SIGN * q), gen_1, 0);
        E = RgXn_mul(s, RgXn_inv(T, minew), minew);
        if (!vp) vp = mkpowers(p,DEG,WT);
        E = Efuneq(E, vp, DEG - 2, 1, B);
        if (!gequal1(gel(t, i)) || !odd(WT)) E = gmul(E, T);
      }
      F[i] = 1;
      if (!odd(WT))
      {
        GEN T, u, t0;
        long v = Q_lvalrem(gsubgs(gel(t,i), 1), p, &t0);
        if (!odd(v))
        {
          if (typ(t0) == t_FRAC) t0 = mulii(gel(t0,1), gel(t0,2));
          u = coredisc(mulii(t0, hgm_get_U0(hgm)));
          T = deg1pol_shallow(stoi(-kroiu(u, p) * q), gen_1, 0);
          E = gmul(E, T); F[i] = 0;
        }
      }
    }
    else
    {
      long SIGN = hgmsign(hgm, p, gel(t,i));
      if (!vp) vp = mkpowers(p,DEG,WT);
      E = Efuneq(s, vp, DEG, SIGN, B);
    }
    gel(S, i) = E;
  }
  if (pF) *pF = F;
  return S;
}

GEN
hgmcoef(GEN hgm, GEN t, GEN n)
{
  pari_sp av = avma;
  GEN C, T, P, E, F = check_arith_all(n, "hgmcoef");
  long flag = 0, i, lt, lP;

  if (!checkhgm(hgm)) pari_err_TYPE("hgmcoef", hgm);
  switch(typ(t))
  {
    case t_INT: case t_FRAC: t = mkvec(t); flag = 1; break;
    case t_VEC: if (RgV_is_QV(t)) break;
    default: pari_err_TYPE("hgmcoef",t);
  }
  if (hgm_get_SWAP(hgm)) t = vecinv(t);
  if (!F) { F = Z_factor(n); P = gel(F,1); }
  else
  {
    P = gel(F,1);
    if (lg(P) == 1 || signe(gel(P,1)) <= 0) return gen_0;
    n = typ(n) == t_VEC? gel(n,1): factorback(F);
  }
  if (signe(n) <= 0) pari_err_DOMAIN("hgmcoef", "n", "<=", gen_0, n);
  E = gel(F,2); lP = lg(P); T = gen_1;
  lt = lg(t); C = cgetg(lt, t_VECSMALL);
  T = const_vec(lt-1, gen_1);
  for (i = 1; i < lP; i++)
  {
    long j, p = itos(gel(P, i)), f = itos(gel(E, i));
    GEN A;
    for (j = 1; j < lt; j++)
    {
      C[j] = hgmclass(hgm, p, gel(t, j));
      if (C[j] == C_BAD) pari_err_IMPL("hgmcoef for bad primes");
    }
    A = frobpoltrunc(hgm, t, C, p, f, NULL);
    for (j = 1; j < lt; j++) gel(A,j) = RgX_coeff(RgXn_inv(gel(A,j), f+1), f);
    T = vecmul(T, A);
  }
  return gerepilecopy(av, flag? gel(T, 1): T);
}

static GEN
count2list(GEN E)
{
  long i, j, r, l = lg(E);
  GEN v = cgetg(zv_sum(E)+1, t_VECSMALL);
  for (i = j = 1; i < l; i++)
    if ((r = E[i])) while(r--) v[j++] = i;
  setlg(v,j); return v;
}
static GEN hgminit_i(GEN val, GEN vbe);
#if 0
static long
minval(GEN F, long p)
{
  long i, d = degpol(F), m = LONG_MAX;
  for (i = 1; i <= d; i++) m = minss(m, Z_lval(gel(F,i+2), p) / i);
  return m;
}
static GEN
cycloE_filter(GEN A, long p)
{
  long i, j, l = lg(A);
  GEN B = shallowcopy(A);
  if (p < l)
    for (i = p; i < l; i += p)
      if (A[i])
      {
        (void)z_lvalrem(i / p, p, &j);
        B[j] += A[i];
        B[i] = 0;
      }
  return B;
}
/* doesn't work because A/B is not valid hypergeometric data */
static GEN
eulfacbadnew(GEN hgm, GEN t, long p, long *pe)
{
  GEN AB = hgm_get_CYCLOE(hgm), gp = utoipos(p);
  GEN A = cycloE_filter(gel(AB,1), p);
  GEN B = cycloE_filter(gel(AB,2), p);
  GEN hgmp = hgminit_i(count2list(A), count2list(B));
  GEN cF, E, F = hgmeulerfactor(hgmp, t, p, &E);
  long s, v, d = degpol(F), w = hgm_get_WT(hgm);
  *pe = 0;
  if (!d) return pol_1(0);
  cF = leading_coeff(F);
  v = Z_lvalrem(cF, p, &cF);
  if (!is_pm1(cF)) return pol_1(0);
  s = minval(F, p);
  if (s) { F = RgX_unscale(F, powis(gp, -s)); v -= s * d; }
  if ((2 * v) % d || (!odd(w) && v % d)) return F;
  return RgX_unscale(F, powis(gp, w / 2 - v / d));
}
#endif
static GEN eulfactame(GEN hgm, GEN t, long p, long *pe);
static GEN
eulfacspec(GEN hgm, GEN t, long p, long cla, long flag, long *pe)
{
  if (cla == C_TAME0) return eulfactame(hgm, t, p, pe);
  if (cla == C_BAD)
  {
    if (flag) { *pe = -1; return gen_0; }
    else      { *pe = 0; return pol_1(0); }
  }
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
hgmeulerfactorlimit_i(GEN hgm, GEN t, long p, long d, long flag, GEN *pE)
{
  GEN P, E, F;
  long e;

  if (typ(t) != t_VEC)
  {
    long c = hgmclass(hgm, p, t);
    if (hgmadditive(c)) P = eulfacspec(hgm, t, p, c, flag, &e);
    else
    {
      P = gel(frobpoltrunc(hgm, mkvec(t), mkvecsmall(c), p, d, &F), 1);
      e = F[1];
    }
    E = e? stoi(e): gen_0;
  }
  else
  {
    long ct, j, l = lg(t);
    GEN T = cgetg(l,t_VEC), C = cgetg(l,t_VECSMALL), perm = cgetg(l,t_VECSMALL);
    P = cgetg(l, t_VEC); E = zero_zv(l - 1);
    for (j = ct = 1; j < l; j++)
    {
      GEN tj = gel(t, j);
      long c = hgmclass(hgm, p, tj);
      if (hgmadditive(c)) gel(P, j) = eulfacspec(hgm, tj, p, c, flag, &E[j]);
      else { perm[ct] = j; gel(T, ct) = tj; C[ct++] = c; }
    }
    setlg(T, ct);
    if (ct > 1)
    {
      GEN Q = frobpoltrunc(hgm, T, C, p, d, &F);
      for (j = 1; j < ct; j++) {gel(P, perm[j]) = gel(Q,j); E[perm[j]] = F[j];}
    }
  }
  if (pE) *pE = E;
  return P;
}
GEN
hgmeulerfactorlimit(GEN hgm, GEN t, long p, long d, GEN *pE)
{ return hgmeulerfactorlimit_i(hgm, t, p, d, 0, pE); }

GEN
hgmeulerfactor(GEN hgm, GEN t, long p, GEN* pE)
{
  pari_sp av = avma;
  long B;
  GEN v;
  if (!checkhgm(hgm)) pari_err_TYPE("hgmeulerfactor", hgm);
  switch(typ(t))
  {
    case t_INT: case t_FRAC: break;
    case t_VEC: if (RgV_is_QV(t)) break;
    default: pari_err_TYPE("hgmeulerfactor",t);
  }
  if (hgm_get_SWAP(hgm)) t = vecinv(t);
  B = (long)(hgm_get_DEG(hgm) * log(p)) + 1;
  v = hgmeulerfactorlimit_i(hgm, t, p, B, 1, pE);
  gerepileall(av, pE? 2: 1, &v, pE); return v;
}

/***********************************************************************/
/*                        Tame Euler factors                           */
/***********************************************************************/
/* FIXME: implement properly like RgXn_sqrt */
static GEN
RgXn_sqrtnu(GEN h, long f, long e)
{
  if (f == 1) return h;
  if (f == 2) return RgXn_sqrt(h, e);
  return ser2rfrac_i(gsqrtn(RgX_to_ser(h, e + 2), utoipos(f), NULL, 0));
}
static GEN
Jordantame(GEN hgm, GEN t0, long m, long p)
{
  GEN P, T, C, ZP, V, Call;
  long d, phim, f, j, c, q, qm;

  if (m == 1)
  {
    long e = hgm_get_WT(hgm) - get_b1(hgm_get_CYCLOE(hgm));
    return deg1pol_shallow(negi(powuu(p, (e+1) >> 1)), gen_1, 0);
  }
  phim = eulerphiu(m); f = Fl_order(p % m, phim, m);
  d = phim + 1; /* DEG >= phim >= f */
  q = upowuu(p, f); qm = (q - 1) / m;
  V = cgetg(phim + 1, t_VECSMALL);
  for (j = c = 1; j < m; j++)
    if (cgcd(j, m) == 1) V[c++] = j * qm;
  Call = hgmCall(hgm, p, f, V); C = gel(Call, 1); ZP = gel(Call, 2);
  T = teich(gadd(t0, ZP)); P = pol_1(0);
  for (j = 1; j < lg(V); j++)
  {
    GEN Q, c = gmul(gpowgs(T, V[j]), gel(C,j));
    Q = RgXn_red_shallow(RgX_shift_shallow(RgX_Rg_mul(P, c), f), d);
    P = RgX_sub(P, Q); /* P * (1 - c x^f) mod X^d */
  }
  return centerlift(RgXn_sqrtnu(P, f, d));
}

static GEN
eulfactameinit(GEN hgm, long v)
{
  GEN C = hgm_get_CYCLOE(hgm);
  if (!v) pari_err_BUG("hgmeulerfactor [incorrect t in eulfactame]");
  if (hgm_get_SWAP(hgm)) v = -v;
  return gel(C, (v < 0)? 2: 1);
}
static long
tameexpo(GEN hgm, long v)
{
  GEN W = eulfactameinit(hgm,v);
  long e, m, l = lg(W);
  for (m = 1, e = 0; m < l; m++)
    if (W[m] && v % m == 0) e += eulerphiu(m);
  return hgm_get_DEG(hgm) - e;
}
static GEN
Jordantameexpo(GEN hgm, long v, GEN t0, long p, long *pe)
{
  GEN P = pol_1(0), W = eulfactameinit(hgm, v);
  long e, m, l = lg(W);
  for (m = 1, e = 0; m < l; m++)
    if (W[m] && v % m == 0)
    {
      P = gmul(P, Jordantame(hgm, t0, m, p));
      e += eulerphiu(m);
    }
  *pe = hgm_get_DEG(hgm) - e; return P;
}

static GEN
eulfactame(GEN hgm, GEN t, long p, long *pe)
{
  long v = Q_lvalrem(t, p, &t);
  return Jordantameexpo(hgm, v, t, p, pe);
}

/***************************************************************/
/*         PART IV.5: Fake wild primes for t                   */
/***************************************************************/
/* Compute g_q(r)=pi^sq(r)*gauss(r) */
static GEN
gkgauss(long p, long f, GEN vp, long r, GEN ZP, GEN *sp)
{
  GEN S = gen_0, P = gen_m1;
  long i, qm1 = vp[f+1] - 1;
  for (i = 1; i <= f; i++)
  {
    GEN t = gfrac(sstoQ(r * vp[i], qm1));
    S = gadd(S, t);
    P = gmul(P, Qp_gamma(gadd(t, ZP)));
  }
  *sp = gmulsg(p - 1, S); /* t_INT */
  return P;
}

static GEN
hgmG(GEN hgm, long p, long f, GEN vp, long r, GEN ZP)
{
  GEN S = gen_0, P = gen_1, VPOLGA = hgm_get_VPOLGA(hgm);
  long n, c;
  for (n = 1; n < lg(VPOLGA); n++)
    if ((c = VPOLGA[n]))
    {
      GEN sq, g = gkgauss(p, f, vp, r*n, ZP, &sq);
      S = addii(S, mulsi(c, sq));
      P = gmul(P, gpowgs(g, c));
    }
  /* p - 1 | S */
  return gmul(P, powis(utoineg(p), itos(S) / (p - 1)));
}

/* multiplicity of -r / (q-1) in beta */
static long
hgmmulti(GEN B, long q, long r)
{
  long d = (q-1) / ugcd(r, q-1);
  return d >= lg(B)? 0: B[d];
}

/* We must have w(M)^r*hgmQ(q,r)=hgmC(q,r)/hgmC(q,0) */
static GEN
hgmQ(GEN hgm, long p, long f, GEN vp, long r, GEN ZP)
{
  pari_sp av = avma;
  GEN B = gel(hgm_get_CYCLOE(hgm), 2);
  long q = vp[f+1], m0 = hgmmulti(B, q, 0), m1 = hgmmulti(B, q, r);
  GEN c = powis(utoipos(q), hgm_get_TT(hgm) + m0 - m1);
  if (odd(m0)) c = negi(c);
  return gerepileupto(av, gmul(c, hgmG(hgm, p, f, vp, r, ZP)));
}

/* not suitable for gerepileupto if p = 2 */
static GEN
hgmU(GEN hgm, long p, long f, GEN vt, long dfp)
{
  pari_sp av = avma;
  GEN v, ZP = zeropadic(utoipos(p), dfp), vp = upowers_u(p, f, 1);
  long q = vp[f+1], lt = lg(vt), i;
  GEN Q = cgetg(q, t_VEC);
  for (i = 1; i < q; i++) gel(Q, i) = hgmQ(hgm, p, f, vp, i-1, ZP);
  if (p == 2)
  {
    v = gerepileupto(av, centerlift(gdivgs(RgV_sum(Q), 1 - q)));
    return const_vec(lt-1, v);
  }
  v = cgetg(lt, t_VEC);
  for (i = 1; i < lt; i++)
  {
    GEN Mt = gmul(hgm_get_MVALUE(hgm), gel(vt,i));
    gel(v, i) = poleval(Q, teich(gadd(Mt, ZP)));
  }
  return gerepileupto(av, centerlift(gdivgs(v, 1 - q)));
}

/***************************************************************/
/*         PART V: Utility programs and main init              */
/***************************************************************/
static GEN
cycloE2cyclo(GEN A, GEN B)
{ return mkvec2(count2list(A), count2list(B)); }
#if 0
GEN
hgmalphatocyclo(GEN val, GEN vbe)
{ GEN C = get_CYCLOE(val,vbe); return cycloE2cyclo(gel(C,1), gel(C,2)); }
#endif

static GEN
allprims(long n, GEN cache)
{
  long l, i, c;
  GEN z, v;
  if (gel(cache,n)) return gel(cache,n);
  z = coprimes_zv(n); l = lg(z); v = cgetg(l, t_VEC);
  for (i = c = 1; i < l; i++)
    if (z[i]) gel(v, c++) = mkfracss(i, n);
  setlg(v, c); return gel(cache,n) = v;
}
static GEN
zv_to_prims(GEN D, GEN cache)
{
  long i, l = lg(D);
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    if (D[i] <= 0) pari_err_TYPE("hgmcyclotoalpha", D);
    gel(v, i) = allprims(D[i], cache);
  }
  return sort(shallowconcat1(v));
}
static void
hgmcyclotoalpha(GEN *pA, GEN *pB)
{
  GEN v, D = *pA, E = *pB;
  if (typ(D) != t_VECSMALL) D = gtovecsmall(D);
  if (typ(E) != t_VECSMALL) E = gtovecsmall(E);
  v = const_vec(maxss(vecsmall_max(D), vecsmall_max(E)), NULL);
  gel(v,1) = mkvec(gen_0);
  *pA = zv_to_prims(D, v);
  *pB = zv_to_prims(E, v);
  if (lg(*pA) != lg(*pB))
    pari_err_TYPE("hgminit [incorrect lengths]", mkvec2(D,E));
}

static GEN
hgmalphatogamma(GEN val, GEN vbe) { return get_VPOLGA(get_CYCLOE(val, vbe)); }

static void
hgmgammatocyclo(GEN VPOLGA, GEN *pD, GEN *pE)
{
  long i, cn, cd, l = lg(VPOLGA);
  GEN d, n, v = zero_zv(l - 1);
  if (typ(VPOLGA) != t_VECSMALL) VPOLGA = gtovecsmall(VPOLGA);
  for (i = 1; i < l; i++)
  {
    long e = VPOLGA[i];
    if (e)
    {
      GEN D = divisorsu(i);
      long j, lD = lg(D);
      for (j = 1; j < lD; j++) v[ D[j] ] += e;
    }
  }
  n = cgetg(l, t_VECSMALL);
  d = cgetg(l, t_VECSMALL);
  for (i = cn = cd = 1; i < l; i++)
  {
    long e = v[i], j;
    if (e < 0) for (j = 1; j <= -e; j++) d[cd++] = i;
    else if (e > 0) for (j = 1; j <= e; j++) n[cn++] = i;
  }
  setlg(d, cd); *pD = d;
  setlg(n, cn); *pE = n;
}

static void
hgmgammatoalpha(GEN VPOLGA, GEN *pA, GEN *pB)
{
  hgmgammatocyclo(VPOLGA, pA, pB);
  hgmcyclotoalpha(pA, pB);
}

/* A and B sorted */
static long
zv_intersect(GEN A, GEN B)
{
  long a = 1, b = 1, lA = lg(A), lB = lg(B);
  while (a < lA && b < lB)
  {
    if      (A[a] < B[b]) a++;
    else if (A[a] > B[b]) b++; else return 1;
  }
  return 0;
}
static void
remove_intersect(GEN *pA, GEN *pB)
{
  GEN V, W, A = *pA, B = *pB;
  long a = 1, b = 1, v = 1, w = 1, lA, lB;
  *pA = V = cgetg_copy(A, &lA);
  *pB = W = cgetg_copy(B, &lB);
  while (a < lA && b < lB)
  {
    int s = gcmp(gel(A,a), gel(B,b));
    if   (s < 0) gel(V,v++) = gel(A,a++);
    else if (s > 0) gel(W,w++) = gel(B,b++);
    else { a++; b++; }
  }
  while (a < lA) gel(V,v++) = gel(A,a++);
  while (b < lB) gel(W,w++) = gel(B,b++);
  setlg(V,v); setlg(W,w);
}

/* al, be normalized, sorted, unknown intersection */
static GEN
albe2u(GEN al, GEN be)
{
  GEN ga;
  remove_intersect(&al, &be);
  ga = hgmalphatogamma(al, be);
  return F2v_factorback(ga);
}
static GEN
get_u(GEN al, GEN be, GEN CYCLOE, GEN VPOLGA, long DEG, long WT)
{
  GEN u, u0 = F2v_factorback(VPOLGA);
  long b1 = get_b1(CYCLOE);
  if (odd(DEG))
  {
    be = sort(normalizeval(RgV_addhalf(be)));
    u = albe2u(al, be);
    if ((DEG & 3) == 3) u = negi(u);
  }
  else if (odd(WT)) { u = u0; if ((b1 & 3) == 2) u = negi(u); }
  else
  {
    al = sort(normalizeval(RgV_addhalf(al)));
    u = shifti(albe2u(al, be), 1);
    if (((DEG + b1) & 3) == 1) u = negi(u);
  }
  u0 = shifti(u0, 1); if ((b1 & 3) == 3) u0 = negi(u0);
  return mkvec2(coredisc(u), u0);
}

static long
zv_sumeuler(GEN v)
{
  long i, l = lg(v);
  GEN s = gen_0;
  for (i = 1; i < l; i++)
  {
    if (v[i] <= 0) pari_err_TYPE("hgminit", v);
    s = addiu(s, eulerphiu(v[i]));
  }
  return itou(s);
}

/* (a, b): format (1) if denominator, format (2) if no denominator,
 * format (3) if b not vector. */
static GEN
hgminit_i(GEN a, GEN b)
{
  long ta = typ(a);
  if (ta != t_VEC && ta != t_VECSMALL) pari_err_TYPE("hgminit", a);
  if (!b)
  {
    if (ta == t_VECSMALL || RgV_is_ZV(a))
    {
      long i, l;
      if (ta != t_VECSMALL) a = vec_to_vecsmall(a);
      l = lg(a);
      for (i = 1; i < l; i++)
        if (a[i] <= 0) break;
      if (i != l)
        hgmgammatoalpha(a, &a, &b); /* gamma */
      else
      { /* cyclo */
        b = const_vecsmall(zv_sumeuler(a), 1);
        hgmcyclotoalpha(&a, &b);
      }
    }
    else /* alpha */
      b = zerovec(lg(a) - 1);
  }
  else
  {
    if (typ(b) != ta) pari_err_TYPE("hgminit", b);
    if (ta == t_VECSMALL || (RgV_is_ZV(a) && RgV_is_ZV(b)))
      hgmcyclotoalpha(&a, &b); /* cyclo */
    else
    { a = sort(a); b = sort(b); } /* alpha */
  }
  return initalbe(a, b);
}
GEN
hgminit(GEN val, GEN vbe)
{ pari_sp av = avma; return gerepilecopy(av, hgminit_i(val, vbe)); }

GEN
hgmalpha(GEN hgm)
{
  GEN al = hgm_get_VAL(hgm), be = hgm_get_VBE(hgm);
  if (hgm_get_SWAP(hgm)) swap(al, be);
  retmkvec2(gcopy(al), gcopy(be));
}
GEN
hgmgamma(GEN hgm)
{
  pari_sp av = avma;
  GEN g;
  if (!checkhgm(hgm)) pari_err_TYPE("hgmgamma", hgm);
  g = hgm_get_VPOLGA(hgm);
  if (hgm_get_SWAP(hgm)) g = zv_neg(g);
  return gerepilecopy(av, g);
}
GEN
hgmcyclo(GEN hgm)
{
  pari_sp av = avma;
  GEN A, B, C;
  if (!checkhgm(hgm)) pari_err_TYPE("hgmcyclo", hgm);
  C = hgm_get_CYCLOE(hgm); A = gel(C,1); B = gel(C,2);
  if (hgm_get_SWAP(hgm)) swap(A, B);
  return gerepilecopy(av, cycloE2cyclo(A, B));
}

GEN
hgmtwist(GEN hgm)
{
  pari_sp av = avma;
  GEN val, vbe;
  if (!checkhgm(hgm)) pari_err_TYPE("hgmtwist", hgm);
  val = hgm_get_VAL(hgm);
  vbe = hgm_get_VBE(hgm);
  if (hgm_get_SWAP(hgm)) swap(val, vbe);
  val = RgV_addhalf(val);
  vbe = RgV_addhalf(vbe);
  return gerepilecopy(av, initalbe(val, vbe));
}

GEN
hgmparams(GEN hgm)
{
  pari_sp av = avma;
  GEN H, M;
  long TT, DEG, WT;
  if (!checkhgm(hgm)) pari_err_TYPE("hgmparams", hgm);
  H = zx_to_ZX(hgm_get_HODGE(hgm));
  TT = hgm_get_TT(hgm); DEG = hgm_get_DEG(hgm);
  WT = hgm_get_WT(hgm); M = hgm_get_MVALUE(hgm);
  return gerepilecopy(av, mkvec4(utoipos(DEG), utoi(WT),
                                 mkvec2(H,stoi(TT)), M));
}

/* symmetry at one ? */
long
hgmissymmetrical(GEN hgm)
{
  GEN A, B, C;
  long a, i, j, lA, lB;
  if (!checkhgm(hgm)) pari_err_TYPE("hgmissymmetrical", hgm);
  C = hgm_get_CYCLOE(hgm);
  if (odd(hgm_get_DEG(hgm))) return 0;
  A = gel(C,1); lA = lg(A);
  B = gel(C,2); lB = lg(B);
  for (i = 1; i < lA; i++) if ((a = A[i]))
  {
    switch(i & 3)
    { /* polcyclo(i)[-X] = polcyclo(j) */
      case 0: j = i; break;
      case 2: j = i >> 1; break;
      default: j = i << 1; break;
    }
    if (j >= lB || B[j] != a) return 0;
  }
  return 1;
}

/***************************************************************/
/*         PART VI: Experimental euler factors                 */
/***************************************************************/
/* FIXME: one prime at a time */
static GEN
hgmmodif(GEN an, GEN PPol)
{
  pari_sp av = avma;
  long i, L = lg(an), lP = lg(PPol);

  for (i = 1; i < lP; i++)
  {
    GEN E = gel(PPol, i), pol = gel(E, 2);
    long d = degpol(pol);
    if (d)
    {
      GEN v = vec_ei(L, 1);
      long j, p = itos(gel(E, 1)), pj = p;
      for (j = 1; j <= d && pj <= L; j++, pj *= p)
        gel(v, pj) = RgX_coeff(pol, j);
      an = dirdiv(an, v);
    }
  }
  return gerepileupto(av, an);
}

/***************************************************************/
/*             PART VII: Make tables of HGMs                   */
/***************************************************************/

static int
ok_part(GEN v, GEN W)
{
  long l = lg(v), j;
  for (j = 1; j < l; j++)
    if (!gel(W,v[j])) return 0;
  return 1;
}
static GEN
mkphi()
{
  GEN W = const_vec(20, NULL);
  gel(W,1) = mkvecsmall2(1,2);
  gel(W,2) = mkvecsmall3(3,4,6);
  gel(W,4) = mkvecsmall4(5,8,10,12);
  gel(W,6) = mkvecsmall4(7,9,14,18);
  gel(W,8) = mkvecsmall5(15,16,20,24,30);
  gel(W,10)= mkvecsmall2(11,22);
  gel(W,12)= mkvecsmalln(6, 13L,21L,26L,28L,36L,42L);
  gel(W,16)= mkvecsmalln(6, 17L,32L,34L,40L,48L,60L);
  gel(W,18)= mkvecsmall4(19,27,38,54);
  gel(W,20)= mkvecsmall5(25,33,44,50,66);
  return W;
}

static GEN
mkal(GEN p, GEN W)
{
  GEN res, V;
  long l = lg(p), lV, i, j;
  V = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) V[i] = lg(gel(W, p[i])) - 1;
  V = cyc2elts(V); lV = lg(V);
  res = cgetg(1, t_VEC);
  for (j = 1; j < lV; j++)
  {
    GEN t = cgetg(l, t_VECSMALL), v = gel(V,j);
    for (i = 1; i < l; i++) t[i] = umael2(W, p[i], v[i]+1);
    vecsmall_sort(t); if (!RgV_isin(res, t)) res = vec_append(res, t);
  }
  return res;
}
static GEN
mkallal(long n)
{
  GEN W = mkphi(), p = partitions(n, NULL, NULL);
  long i, c, l = lg(p);
  for (i = c = 1; i < l; i++)
    if (ok_part(gel(p,i), W)) gel(p, c++) = mkal(gel(p,i), W);
  setlg(p, c); return shallowconcat1(p);
}

static GEN
mkalbe(long n)
{
  GEN w, L = mkallal(n);
  long i, j, c, l = lg(L);
  w = cgetg(l * (l / 2) + 1, t_VEC);
  for (i = c = 1; i < l; i++)
  {
    GEN A = gel(L, i);
    long a = A[lg(A)-1];
    for (j = i + 1; j < l; j++)
    {
      GEN B = gel(L, j);
      if (!zv_intersect(A, B))
        gel(w,c++) = (A[1]==1 || (B[1]!=1 && a > B[lg(B)-1]))?
                     mkvec2(B,A): mkvec2(A,B);
    }
  }
  setlg(w,c); return w;
}

static long
cyclowt(GEN a, GEN b)
{
  pari_sp av = avma;
  long TT;
  hgmcyclotoalpha(&a, &b);
  return gc_long(av, degpol(hodge(a, b, &TT)));
}

GEN
hgmbydegree(long n)
{
  pari_sp av = avma;
  GEN w = cgetg(n+1, t_VEC), c = const_vecsmall(n, 1), v = mkalbe(n);
  long i, l = lg(v);
  for (i = 1; i <= n; i++) gel(w,i) = cgetg(l,t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN z = gel(v,i);
    long k = cyclowt(gel(z,1), gel(z,2)) + 1;
    gmael(w, k, c[k]++) = z;
  }
  for (i = 1; i <= n; i++) setlg(gel(w,i), c[i]);
  return gerepilecopy(av, w);
}

/***************************************************************/
/*             PART VIII: L-function data                      */
/***************************************************************/
/* BAD sorted t_VECSMALL */
static GEN
removebad(GEN v, GEN BAD)
{
  long i, c, l = lg(v);
  GEN w = cgetg(l, t_VECSMALL);
  for (i = c = 1; i < lg(v); i++)
    if (!zv_search(BAD, v[i])) w[c++] = v[i];
  setlg(w, c); return w;
}
static GEN
primedivisors(GEN t)
{ GEN fa = absZ_factor(t); return ZV_to_zv(gel(fa,1)); }

static GEN
gacfac(long p, long m, long c)
{
  long i, l = p + m + 1;
  GEN v = cgetg(l, t_VECSMALL);
  for (i = 1; i <= p; i++) v[i] = -c;
  for (     ; i <  l; i++) v[i] = 1 - c;
  return v;
}

static GEN
hgmfindvga(GEN hgm, GEN t)
{
  GEN v, HODGE = hgm_get_HODGE(hgm);
  long WT = degpol(HODGE), WT2 = (WT - 1) >> 1, i, c, h, fl = gequal1(t);
  v = cgetg(WT + 2, t_VEC);
  for (i = 0, c = 1; i <= WT2; i++)
  {
    if ((h = HODGE[i+2]))
    {
      if (fl && 2*i == WT - 1) h--;
      if (h) gel(v, c++) = gacfac(h, h, i);
    }
  }
  if (!odd(WT))
  {
    long h = HODGE[WT2+3], hp = h >> 1, hm;
    if (!fl)
    {
      hm = hp;
      if (odd(h))
      { if (gsigne(t) >= 0 && gcmpgs(t, 1) <= 0) hm++; else hp++; }
      else
      { if (gcmpgs(t, 1) > 0) { hp++; hm--; } }
      if (odd(hgm_get_TT(hgm) + WT2 + 1)) lswap(hp, hm);
    }
    else
    {
      h--; hm = h - hp;
      if (odd(h) && odd(hgm_get_TT(hgm) + WT2 + 1)) lswap(hp, hm);
    }
    if (hp || hm) gel(v, c++) = gacfac(hp, hm, WT2 + 1);
  }
  if (c == 1) return cgetg(1, t_VECSMALL);
  setlg(v, c); v = shallowconcat1(v);
  vecsmall_sort(v); return v;
}

/* Return [VGA, k, BAD, COND] where VGA as in lfun, k non motivic
 * weight (s -> k - s), BAD is the list of wild primes and Euler factors,
 * COND is the tame part of the conductor */
static GEN
hgmlfuninfty(GEN hgm, GEN t)
{
  pari_sp av = avma;
  GEN VGA = hgmfindvga(hgm, t), T0, T1, v;
  GEN COND, t1 = gsubgs(t, 1), BAD = primedivisors(hgm_get_BAD(hgm));
  long k = hgm_get_WT(hgm) + 1, i, j, l;

  if (isintzero(t1)) T1 = cgetg(1, t_VECSMALL);
  else
  {
    GEN fa = absZ_factor(numer_i(t1)), P = gel(fa,1), E = gel(fa,2);
    if (!odd(k)) T1 = removebad(ZV_to_zv(P), BAD);
    else
    {
      long j, lP = lg(P);
      T1 = cgetg(lP, t_VECSMALL);
      for (i = j = 1; i < lP; i++)
      {
        long p = itos(gel(P,i));
        if (mpodd(gel(E,i)) && !zv_search(BAD, p)) T1[j++] = p;
      }
      setlg(T1,j);
    }
  }
  COND = zv_prod_Z(T1);
  T0 = removebad(gconcat(primedivisors(numer_i(t)),
                         primedivisors(denom_i(t))), BAD);
  for (i = 1; i < lg(T0); i++)
  {
    long p = T0[i], e = tameexpo(hgm, Q_lval(t, p));
    COND = mulii(powuu(p, e), COND);
  }
  l = lg(BAD); v = cgetg(l, t_VEC);
  for (i = j = 1; i < l; i++) /* FIXME: precompute wild Euler factors */
    if (hgmclass(hgm, BAD[i], t) == C_BAD)
      gel(v,j++) = mkvec2(utoipos(BAD[i]), pol_1(0));
  setlg(v, j); return gerepilecopy(av, mkvec4(VGA, utoi(k), v, COND));
}

/***************************************************************/
/*             PART IX: GUESS OF WILD PRIMES                   */
/***************************************************************/
static GEN
vecmellin(GEN L, GEN K, GEN t, GEN td, GEN vroots, long bitprec)
{
  long i, N = lfunthetacost(L, t, 0, bitprec);
  GEN v = cgetg(N+1, t_VEC);
  for (i = 1; i <= N; i++)
    gel(v,i) = gammamellininvrt(K, gmul(td, gel(vroots,i)), bitprec);
  return v;
}

/* List of Weil polynomials for prime p of degree d and weight w */
static GEN
listweil_i(ulong d, ulong p, ulong w)
{
  GEN V;
  if (d == 0) return mkvec(pol_1(0));
  if (odd(d))
  {
    GEN P;
    if (odd(w)) return cgetg(1, t_VEC);
    V = listweil_i(d - 1, p, w);
    P = monomial(powuu(p, w / 2), 1, 0);
    return shallowconcat(gmul(gsubsg(1, P), V), gmul(gaddsg(1, P), V));
  }
  if (d == 2)
  {
    long q = upowuu(p, w), s = usqrt(4 * q), i;
    GEN Q = utoi(q);
    V = cgetg(2*s + 3, t_VEC);
    for (i = 1; i <= 2*s + 1; i++) gel(V,i) = mkpoln(3, Q, stoi(1+s-i), gen_1);
    gel(V, 2*s + 2) = mkpoln(3, negi(Q), gen_0, gen_1);
    return V;
  }
  if (d == 4)
  {
    long q = upowuu(p, w), s = usqrt(16 * q), a, c, is2 = usqrt(4 * q);
    double s2 = 2 * sqrt((double)q);
    GEN Q2 = sqru(q), W, A, mA, tmp, Q;
    V = cgetg(s + 3, t_VEC);
    for (a = 0; a <= s; a++)
    {
      long b, m = ceil(a * s2) - 2 * q, M = ((a * a) >> 2) + 2 * q;
      GEN AQ = stoi(a * q), mAQ = stoi(-a * q);
      A = stoi(a); mA = stoi(-a);
      W = cgetg(2*(M - m) + 3, t_VEC);
      for (b = m, c = 1; b <= M; b++)
      {
        if (a) gel(W, c++) = mkpoln(5, Q2, mAQ, stoi(b), mA, gen_1);
        gel(W, c++) = mkpoln(5, Q2, AQ, stoi(b), A, gen_1);
      }
      setlg(W, c); gel(V, a + 1) = W;
    }
    W = cgetg(2 * is2 + 2, t_VEC);
    tmp = mkpoln(3, stoi(-q), gen_0, gen_1);
    Q = utoipos(q);
    for (a = 0, c = 1; a <= is2; a++)
    {
      A = stoi(a); mA = stoi(-a);
      if (a) gel(W, c++) = gmul(tmp, mkpoln(3, Q, mA, gen_1));
      gel(W, c++) = gmul(tmp, mkpoln(3, Q, A, gen_1));
    }
    setlg(W, c); gel(V, s + 2) = W;
    return shallowconcat1(V);
  }
  pari_err_IMPL("d > 5 in listweil");
  return NULL; /* LCOV_EXCL_LINE */
}

/* Same, weight <= w, by decreasing weight */
static GEN
listweilallw_i(ulong d, ulong p, ulong w)
{
  long i = d? w: 0;
  GEN V = cgetg(i+2, t_VEC);
  for (; i >= 0; i--) gel(V,i+1) = listweil_i(d, p, i);
  return shallowconcat1(V);
}

static long
sumdeg(GEN W, GEN M)
{
  long i, l = lg(M), s = 0;
  for (i = 1; i < l; i++) s += degpol(gmael(W,i,M[i]+1));
  return s;
}

static GEN
mul(GEN a, GEN b, ulong lim)
{
  long na = lg(a)-1, nb = lg(b)-1, i, j, n;
  GEN c = cgetg(na * nb + 1, t_VECSMALL);
  for (i = n = 1; i <= na; i++)
    for (j = 1; j <= nb; j++)
    {
      ulong m = umuluu_or_0(a[i], b[j]);
      if (m && m <= lim) c[n++] = m;
    }
  setlg(c, n); return c;
}
static GEN
listcond(GEN BAD, GEN achi, ulong min, ulong max)
{
  long i, j, l = lg(BAD);
  GEN P = cgetg(l, t_VEC), z;
  for (i = 1; i < l; i++)
  {
    long p = BAD[i], v = achi[i];
    gel(P,i) = upowers_u(p, ulogint(max, p) - v, upowuu(p, v));
  }
  z = gel(P,1); for (i = 2; i < l; i++) z = mul(z, gel(P,i), max);
  if (min > 1)
  {
    l = lg(z);
    for (i = j = 1; i < l; i++)
      if ((ulong)z[i] >= min) z[j++] = z[i];
    setlg(z, j);
  }
  vecsmall_sort(z); return z;
}

/* Artificial lfundiv by zeta(s - (k - 1) / 2). */
static GEN
lfundivraw(GEN L)
{
  long k = itos(ldata_get_k(L));
  L = shallowcopy(L);
  gel(L, 3) = lfunvgasub(ldata_get_gammavec(L), mkvec(stoi(-(k - 1) >> 2)));
  setlg(L, 7); return L;
}

static long
zv_max(GEN v)
{
  long m = -1, i;
  for (i = 1; i < lg(v); i++) m = maxss(m, v[i]);
  return m;
}

/* Compute forvec vectors from v only with entries <= ctmax (no limit if
 * ctmax = 0) and max entries >= ctmin. */
static GEN
forvectrunc(GEN vF, GEN v, long ctmin, long ctmax)
{
  long i, lE, lM, lv = lg(v);
  GEN vM, w, E;

  if (ctmax)
  {
    w = cgetg(lv, t_VECSMALL);
    for (i = 1; i < lv; i++) w[i] = minss(v[i], ctmax);
    v = w;
  }
  E = cyc2elts(v); lE = lg(E); vM = cgetg(lE, t_VEC);
  for (i = lM = 1; i < lE; i++)
    if (zv_max(gel(E,i)) >= ctmin) gel(vM, lM++) = gel(E,i);
  setlg(vM, lM); w = cgetg(lM, t_VECSMALL);
  for (i = 1; i < lM; i++) w[i] = sumdeg(vF, gel(vM, i));
  return vecpermute(vM, vecsmall_indexsort(w)); /* by increasing total degree */
}

static GEN
lfunhgmwild(GEN L, GEN H, GEN t, GEN BAD, long pole, long limdeg, long bitprec)
{
  GEN v, K, t0, t0r, t0ir, t0i, t0k, N0, vM, vD, val, PPOL, vF, achi;
  long d, lM, iN, iM, i, k, k2, prec = nbits2prec(bitprec), lB = lg(BAD);
  ulong minN = 1, maxN = 2048;

  v = cgetg(lB, t_VECSMALL); PPOL = cgetg(lB, t_VEC);
  for (i = 1; i < lB; i++)
  {
    v[i] = itou( gmael(BAD,i,1) );
    gel(PPOL,i) = shallowcopy(gel(BAD,i));
  }
  BAD = v;
  achi = get_achi(H, t, BAD);
  if (pole) L = lfundivraw(L);
  d = ldata_get_degree(L);
  k = itos(ldata_get_k(L)); k2 = (k-1) >> 1;
  N0 = ldata_get_conductor(L);
  K = gammamellininvinit(ldata_get_gammavec(L), 0, bitprec + 32);
  t0 = sstoQ(11, 10); t0i = ginv(t0); t0k = gpowgs(t0, k);
  t0r = gpow(t0, sstoQ(2,d), prec); t0ir = ginv(t0r);
  /* vF[i] list of Weil polynomials F for p = BAD[i],
   * F = prod_j Fj, |reciprocal root of Fj|^2 = p^(w + 1 - nj)
   * 2v_p(lc(F)) = deg F * (w + 1) - sum_j deg Fj * nj; */
  vF = cgetg(lB, t_VEC);
  vD = cgetg(lB, t_VEC); /* vD[k][l] = sum_j deg Fj * nj for F = vF[k][l] */
  v = cgetg(lB, t_VECSMALL);
  for (i = 1; i < lB; i++)
  {
    GEN W = cgetg(d+2, t_VEC), D;
    long p = BAD[i], j, lW;
    for (j = 0; j <= d; j++) gel(W,j+1) = listweilallw_i(j, p, k-1);
    gel(vF, i) = W = shallowconcat1(W);
    lW = lg(W); v[i] = lW-1;
    gel(vD,i) = D = cgetg(lW, t_VEC);
    for (j = 1; j < lW; j++)
    {
      GEN F = gel(W,j);
      D[j] = degpol(F) * k - 2 * Z_lval(leading_coeff(F), p);
    }
  }
  vM = forvectrunc(vF, v, 0, limdeg); lM = lg(vM);
  if (DEBUGLEVEL) { err_printf(" lM = %ld ", lM); err_flush(); }
  L = shallowcopy(L);
  val = cgetg(lB, t_VECSMALL);
  for(;;minN = maxN+1, maxN <<= 2)
  {
    GEN z = listcond(BAD, achi, minN, maxN), vroots, an0, vN;
    long lN = lg(z), lim;

    if (lN == 1) continue;
    vN = cgetg(lN, t_VEC);
    for (i = 1; i < lN; i++) gel(vN, i) = muliu(N0, z[i]);
    gel(L, 5) = gel(vN, lN - 1);
    if (DEBUGLEVEL) err_printf("\nmaxN = %ld\n", itos(gel(L,5)));
    lim = lfunthetacost(L, t0i, 0, bitprec);
    vroots = dirpowers(lim, sstoQ(2, d), prec + EXTRAPRECWORD);
    an0 = hgmcoefs(H, t, lim);
    if (pole)
    {
      GEN w = vecpowuu(lim, k2);
      long pb = 1;
      for (i = 1; i < lB; i++) pb = BAD[i] * pb;
      for (i = 1; i <= lim; i++)
        if (cgcd(i, pb) > 1) gel(w, i) = gen_0;
      an0 = dirdiv(an0, w);
    }
    for (iN = 1; iN < lN; iN++)
    {
      pari_sp av0 = avma, av2;
      GEN vecK, vecKi, N = gel(vN,iN), isqN = gpow(N, sstoQ(-1,d), prec);
      if (DEBUGLEVEL) { err_printf(" %ld ", itos(N)); err_flush(); }
      gel(L,5) = N;
      vecK = vecmellin(L, K, t0, gmul(t0r,  isqN), vroots, bitprec);
      vecKi= vecmellin(L, K, t0i,gmul(t0ir, isqN), vroots, bitprec);
      for (i = 1; i < lB; i++) val[i] = Z_lval(N, BAD[i]);
      setlg(an0, lg(vecKi)); av2 = avma;
      for (iM = 1; iM < lM; iM++, set_avma(av2))
      {
        GEN M = gel(vM, iM), an, eno, den;
        for (i = 1; i < lB; i++)
        {
          GEN F = gmael(vF, i, M[i]+1);
          long D, dF = degpol(F), a = val[i];
          if (a < d - dF) break;
          if (a)
          {
            if (d == dF) break;
            D = mael(vD, i, M[i]+1); /* sum_j deg Fj nj */
            if (D == d && d - dF != a) break;
            /* a = a(chi) + d - deg F - 1 */
            if (D == d-1 && a != d - dF + achi[i] - 1 && !gequal1(t)) break;
          }
          gmael(PPOL, i, 2) = F;
        }
        if (i < lB) continue;
        an = hgmmodif(an0, PPOL);
        den = gmul(t0k, RgV_dotproduct(vecK, an));
        eno = gdiv(RgV_dotproduct(vecKi, an), den);
        if (gexpo(gsubgs(gabs(eno, prec), 1)) < -bitprec / 2)
        {
          if (pole)
            for (i = 1; i < lB; i++)
            {
              GEN t = deg1pol_shallow(negi(powuu(BAD[i], k2)), gen_1, 0);
              gmael(PPOL, i, 2) = gmul(gmael(PPOL, i, 2), t);
            }
          for (i = 1; i < lB; i++) gmael(PPOL, i, 2) = ginv(gmael(PPOL, i, 2));
          eno = grndtoi(eno, &i);
          if (typ(eno) != t_INT) pari_err_BUG("lfunhgmwild");
          return mkvec3(N, mkvec2(t, PPOL), eno);
        }
      }
      set_avma(av0);
    }
  }
}

static GEN
BAD2small(GEN BAD)
{
  long i, l = lg(BAD);
  GEN v = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) v[i] = itou( gmael(BAD,i,1) );
  return v;
}

/* moments of motive */
static GEN
hgmmoments(GEN H, GEN t, GEN M, long nb)
{
  pari_sp av = avma, av2;
  GEN P, v, S, L = hgmlfuninfty(H, t), BAD = BAD2small(gel(L, 3));
  GEN k2 = gmul2n(gsubgs(gel(L,2), 1), -1);
  long ct = 0, i, j, lP, lm, tm = typ(M);

  if (!nb) nb = 1000;
  P = primes_zv(nb); lP = lg(P);
  v = hgmcoefs(H, t, P[lP - 1]);
  if (tm != t_VEC) M = gtovec(M);
  av2 = avma; lm = lg(M);
  S = const_vec(lm - 1, real_0(DEFAULTPREC));
  for (i = 1; i < lP; i++)
  {
    long p = P[i];
    if (!Q_lval(t, p) && !zv_search(BAD, p))
    {
      GEN T = gdiv(gel(v, p), gpow(utoipos(p), k2, DEFAULTPREC));
      ct++;
      for (j = 1; j < lm; j++)
        gel(S,j) = gadd(gel(S,j), gpow(T, gel(M,j), DEFAULTPREC));
    }
    if ((i & 0xf) == 0) S = gerepilecopy(av2, S);
  }
  if (tm != t_VEC && tm != t_COL && tm != t_VECSMALL) S = gel(S, 1);
  return gerepileupto(av, gdivgs(S, ct));
}

#if 0
/* Vector version: does not use parallelism since uses hgmTrace, useful
 * if vect long. */
static GEN
hgmmomentsvec(GEN H, GEN vect, GEN M, GEN P)
{
  pari_sp av = avma;
  GEN S, L = hgmlfuninfty(H, gen_m1), BAD = BAD2small(gel(L, 3)), C;
  GEN k2 = gmul2n(gsubgs(gel(L, 2), 1), -1);
  long ct = 0, i, k, lP, lm, tm = typ(M), lt = lg(vect);

  if (typ(vect) != t_VEC) { vect = mkvec(vect); lt = 2; }
  if (!P) P = primes_zv(1000);
  if (typ(P) != t_VECSMALL) P = gtovecsmall(P);
  lP = lg(P);
  if (tm != t_VEC) M = gtovec(M);
  lm = lg(M);
  S = cgetg(lt, t_VEC);
  for (k = 1; k < lt; k++) gel(S, k) = const_vec(lm - 1, real_0(DEFAULTPREC));
  C = zero_zv(lt - 1);
  for (i = 1; i < lP; i++)
  {
    long p = P[i], j;
    if (!zv_search(BAD, p))
    {
      GEN Call = hgmCall(H, p, 1, NULL);
      GEN T = gdiv(hgmtrace(H, Call, vect, C), gpow(utoipos(p), k2, DEFAULTPREC));
      ct++;
      for (j = 1; j < lm; j++)
        for (k = 1; k < lt; k++)
          gmael(S, k, j) = gadd(gmael(S, k, j),
                                gpow(gel(T, k), gel(M, j), DEFAULTPREC));
    }
  }
  if (tm != t_VEC && tm != t_COL && tm != t_VECSMALL)
    for (k = 1; k < lt; k++) gel(S, k) = gmael(S, k, 1);
  return gerepileupto(av, gdivgs(S, ct));
}
#endif

/* Heuristic guess: is there a pole ? */
static long
lfunhgmispole(GEN H, GEN t, long nb)
{
  pari_sp av = avma;
  GEN M;
  if (!nb) nb = 40;
  M = hgmmoments(H, t, gen_1, nb);
  return gc_bool(av, gexpo(M) > -2);
}

static GEN
tag(GEN x, long t) { return mkvec2(mkvecsmall(t), x); }

static GEN
lfunhgm_i(GEN hgm, GEN t, long limdeg, long bitprec)
{
  GEN L, vr, v = hgmlfuninfty(hgm, t), vga = zv_to_ZV(gel(v,1)), k = gel(v,2);
  GEN BAD = gel(v,3), COND = gel(v, 4);
  long pole = mpodd(k) && lfunhgmispole(hgm, t, 0), lB = lg(BAD);

  L = mkvecn(pole? 7: 6, tag(mkvec2(hgm,t), t_LFUN_HGM), gen_0, vga, k, COND,
             gen_0, mkvec(mkvec2(shifti(addiu(k,1),-1), gen_0)));
  if (pole && ldata_get_degree(L) == 1)
  { /* motive = zeta */
    long i;
    gel(L,5) = gel(L,6) = gel(L,7) = gen_1;
    if (lB != 1)
    {
      GEN R = mkrfrac(gen_1, deg1pol_shallow(gen_m1,gen_1,0));
      gmael3(L, 1, 2, 2) = mkvec2(t, BAD);
      for (i = 1; i < lB; i++) gmael(BAD, i, 2) = R;
    }
    return L;
  }
  if (lB == 1)
  {
    vr = lfunrootres(L, bitprec);
    gel(L, 6) = gel(vr, 3);
    if (pole) gel(L, 7) = gel(vr, 1);
    return L;
  }
  v = lfunhgmwild(L, hgm, t, BAD, pole, limdeg, bitprec);
  gel(L, 5) = gel(v, 1);
  gmael3(L, 1, 2, 2) = gel(v, 2);
  if (!pole) gel(L, 6) = gel(v, 3);
  else
  {
    vr = lfunrootres(L, bitprec);
    gel(L, 6) = gel(vr, 3); gel(L, 7) = gel(vr, 1);
  }
  return L;
}
GEN
lfunhgm(GEN hgm, GEN t, long lim, long bit)
{
  pari_sp av = avma;
  if (!checkhgm(hgm)) pari_err_TYPE("lfunhgm", hgm);
  return gerepilecopy(av, lfunhgm_i(hgm, t, lim, bit));
}

GEN
dirhgm_worker(GEN P, ulong X, GEN hgm, GEN t)
{
  pari_sp av = avma;
  long i, l = lg(P);
  GEN W = cgetg(l, t_VEC);
  for(i = 1; i < l; i++)
  {
    ulong p = uel(P,i);
    long d = ulogint(X, p) + 1; /* minimal d such that p^d > X */
    gel(W,i) = RgXn_inv(hgmeulerfactorlimit(hgm, t, p, d-1, NULL), d);
  }
  return gerepilecopy(av, mkvec2(P,W));
}

GEN
hgmcoefs(GEN hgm, GEN t, long n)
{
  GEN worker, bad = NULL;
  if (!checkhgm(hgm)) pari_err_TYPE("hgmcoefs", hgm);
  if (typ(t) == t_VEC && lg(t) == 3) { bad = gel(t,2); t = gel(t,1); }
  switch(typ(t))
  {
    case t_INT: case t_FRAC: break;
    case t_VEC: if (RgV_is_QV(t)) break;
    default: pari_err_TYPE("hgmcoefs",t);
  }
  worker = snm_closure(is_entry("_dirhgm_worker"), mkvec2(hgm, t));
  return pardireuler(worker, gen_2, stoi(n), NULL, bad);
}
