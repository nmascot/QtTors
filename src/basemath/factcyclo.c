/* Copyright (C) 2000, 2012  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* written by Takashi Fukuda
 *  2019.10.27 : Flx_factcyclo_gen, FpX_factcyclo_gen
 *  2019.10.28 : Flx_factcyclo_lift, FpX_factcyclo_lift
 *  2019.11.3  : Flx_factcyclo_newton, FpX_factcyclo_newton
 *  2019.11.12 : gausspol for prime
 *  2019.11.13 : gausspol for prime power
 *  2019.11.14 : ZpX_roots_nonsep with ZX_Zp_root
 *  2019.11.15 : test ZpX_roots_nonsep with polrootspadic
 *  2019.11.16 : accept variable number
 *  2019.11.17 : gen_ascent
 *  2019.11.20 : ZpX_roots_nonsep with FpX_roots
 *  2021.7.19  : Flx_factcyclo_newton_general
 *  2021.7.22  : Flx_conductor_lift */

#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_factcyclo

#define GENERAL            1
#define NEWTON_POWER       2
#define NEWTON_GENERAL     4
#define NEWTON_GENERAL_NEW 8
#define ASCENT            16

#define Flx_polcyclo(n, p) ZX_to_Flx(polcyclo(n, 0), p)
#define FpX_polcyclo(n, p) FpX_red(polcyclo(n, 0), p)

/* 0 <= z[i] <= ULONG_MAX */
static GEN
ZX_to_nx(GEN z)
{
  long i, r = lg(z);
  GEN x = cgetg(r, t_VECSMALL);
  for (i = 2; i < r; i++) x[i] = itou(gel(z, i));
  return x;
}

static long
QX_den_pval(GEN x, GEN p)
{
  long i, vmax = 0, l = lg(x);
  for (i = 2; i < l; i++)
  {
    GEN z = gel(x, i);
    long v;
    if (typ(z)==t_FRAC && (v = Z_pval(gel(z, 2), p)) > vmax) vmax = v;
  }
  return vmax;
}

static long
QXV_den_pval(GEN vT, GEN kT, GEN p)
{
  long k, vmax = 0, l = lg(kT);
  for (k = 1; k < l; k++)
  {
    long v = QX_den_pval(gel(vT, kT[k]), p);
    if (v > vmax) vmax = v;
  }
  return vmax;
}

/* n=el^e, p^d=1 (mod n), d is in [1,el-1], phi(n)=d*f.
 *  E[i] : 1 <= i <= n-1
 *  E[g^i*p^j mod n] = i+1  (0 <= i <= f-1, 0 <= j <= d-1)
 *  We use E[i] (1 <= i <= d). Namely i < el. */
static GEN
set_E(long pmodn, long n, long d, long f, long g)
{
  long i, j;
  GEN E = const_vecsmall(n-1, 0);
  pari_sp av = avma;
  GEN C = Fl_powers(g, f-1, n);
  for (i = 1; i <= f; i++)
  {
    ulong x = C[i];
    for (j = 1; j <= d; j++) { x = Fl_mul(x, pmodn, n); E[x] = i; }
  }
  return gc_const(av, E);
}

static GEN
ZX_chinese_center(GEN x1, GEN p1, GEN x2, GEN p2)
{
  long i, l = lg(x1);
  GEN x = cgetg(l, t_POL);
  GEN y1, y2, q1, q2, m = mulii(p1, p2), m2 = shifti(m, -1);
  x[1] = x1[1];
  bezout(p1, p2, &q1, &q2);
  y1 = Fp_mul(p2, q2, m); y2 = Fp_mul(p1, q1, m);
  for (i = 2; i < l; i++)
  {
    GEN y = Fp_add(mulii(gel(x1, i), y1), mulii(gel(x2, i), y2), m);
    if (cmpii(y, m2) > 0) y = subii(y, m);
    gel(x, i) = y;
  }
  return x;
}

/* find prime el s.t. el=1 (mod n) and el does not divide d(T) */
static ulong
next_el_n(ulong el, ulong n, GEN d1)
{
  forprime_t T;
  u_forprime_arith_init(&T, el+n, ULONG_MAX, 1, n);
  do el = u_forprime_next(&T); while (dvdiu(d1, el));
  return el;
}

/* return min el s.t. 2^63<el and el=1 (mod n). */
static ulong
start_el_n(ulong n)
{
  ulong MAXHLONG = 1L<<(BITS_IN_LONG-1), el = (MAXHLONG/n)*n + 1;
  if ((el&1)==0) el += n; /* if el is even, then n is odd */
  return el + n + n;
}

/* start probably catches d0*T_k(x). So small second is enough. */
static ulong
get_n_el(GEN d0, ulong *psec)
{
  ulong start = ((lgefint(d0)-2)*BITS_IN_LONG)/(BITS_IN_LONG-1)+1, second = 1;
  if (start>10) second++;
  if (start>100)  { start++; second++; }
  if (start>500)  { start++; second++; }
  if (start>1000) { start++; second++; }
  *psec = second; return start;
}

static long
FpX_degsub(GEN P, GEN Q, GEN p)
{
  pari_sp av = avma;
  long d = degpol(FpX_sub(P, Q, p));
  return gc_long(av, d);
}

/* n=odd prime power, F=Q(zeta_n), G=G(F/Q)=(Z/nZ)^*, H=<p>, K <--> H,
 * t_k=Tr_{F/K}(zeta_n^k), T=minimal pol. of t_1 over Q.
 * g is a given generator of G(K/Q).
 * There exists a unique G(x) in Q[x] s.t. t_g=G(t_1).
 * return G(x) mod el assuming that el does not divide d(T), in which case
 * T(x) is separable over F_el and so Vandermonde mod el is regular. */
static GEN
gausspol_el(GEN H, ulong n, ulong d, ulong f, ulong g, ulong el)
{
  ulong j, k, z_n = rootsof1_Fl(n, el);
  GEN vz_n, L = cgetg(1+f, t_VECSMALL), x = cgetg(1+f, t_VECSMALL), X;

  vz_n = Fl_powers(z_n, n-1, el)+1;
  for (k = 0; k < f; k++)
  {
    long gk = Fl_powu(g, k, n), t = 0;
    for(j = 1; j <= d; j++)
      t = Fl_add(t, vz_n[Fl_mul(H[j], gk, n)], el);
    L[1+k] = t;
    x[1+(k+f-1)%f] = t;
  }
  X = Flv_invVandermonde(L, 1, el);
  return Flv_to_Flx(Flm_Flc_mul(X, x, el), 0);
}

static GEN
get_G(GEN H, GEN d0, GEN d1, GEN N, ulong el, long  k)
{
  long n = N[1], d = N[2], f = N[3], g = N[4], i;
  GEN POL = cgetg(1+k, t_VEC), EL = cgetg(1+k, t_VECSMALL), G, M, x;
  pari_timer ti;

  if (DEBUGLEVEL >= 6) timer_start(&ti);
  for (i = 1; i <= k; i++)
  {
    el = next_el_n(el, n, d1);
    x = gausspol_el(H, n, d, f, g, el);
    gel(POL, i) = Flx_Fl_mul(x, umodiu(d0, el), el);
    EL[i] = el;
  }
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "get_G : make data k=%ld",k);
  G = nxV_chinese_center(POL, EL, &M);
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "get_G : nxV_chinese_center k=%ld",k);
  retmkvec3(G, M, utoi(el));
}

static long
Q_size(GEN z)
{
  if (typ(z)==t_INT) return lgefint(z) - 2;
  return maxss(lgefint(gel(z,1)), lgefint(gel(z,2))) - 2;
}
/* return max log_a(|x[i]|), a=2^(BITS_IN_LONG-1) */
static long
ZX_size(GEN x)
{
  long i, l = lg(x), max = 0;
  for (i = 2; i < l; i++)
  {
    long y = lgefint(gel(x,i)) - 2;
    if (y > max) max = y;
  }
  return max;
}

/* d0 is a multiple of (O_K:Z[t_1]). i.e. d0*T_k(x) is in Z[x].
 * d1 has the same prime factors as d(T); d0 d1 = d(T)^2 */
static GEN
get_d0_d1(GEN T, GEN P)
{
  long i, l = lg(P);
  GEN x, y, dT = ZX_disc(T);
  x = y = dT; setsigne(dT, 1);
  for (i = 1; i < l; i++)
    if (odd(Z_lvalrem(dT, P[i], &dT)))
    {
      x = diviuexact(x, P[i]);
      y = muliu(y, P[i]);
    }
  return mkvec2(sqrti(x), sqrti(y));  /* x and y are square */
}

static GEN
gausspol(GEN T, GEN H, GEN N, ulong d, ulong f, ulong g)
{
  long n = N[1], el0 = N[2];
  GEN F, G1, G2, M1, M2, G, d0, d1, Data, d0d1 = get_d0_d1(T, mkvecsmall(el0));
  ulong el, n_el, start, second;
  pari_timer ti;

  d0 = gel(d0d1,1); /* d0*F is in Z[X] */
  d1 = gel(d0d1,2); /* d1 has same prime factors as disc(T) */
  Data = mkvecsmall4(n, d, f, g);
  start = get_n_el(d0, &second);
  el = start_el_n(n);

  if (DEBUGLEVEL >= 6) timer_start(&ti);
  if (DEBUGLEVEL == 2) err_printf("gausspol:start=(%ld,%ld)\n",start,second);
  G = get_G(H, d0, d1, Data, el, start);
  G1 = gel(G, 1); M1 = gel(G, 2); el = itou(gel(G, 3));
  for(n_el=second; n_el; n_el++)
  {
    G = get_G(H, d0, d1, Data, el, n_el);
    G2 = gel(G, 1); M2 = gel(G, 2); el = itou(gel(G, 3));
    if (FpX_degsub(G1, G2, M2) < 0) break;  /* G1 = G2 (mod M2) */
    if (DEBUGLEVEL == 2)
      err_printf("G1:%ld, G2:%ld\n",ZX_size(G1), ZX_size(G2));
    if (DEBUGLEVEL >= 6) timer_start(&ti);
    G2 = ZX_chinese_center(G1, M1, G2, M2); M2 = mulii(M1, M2);
    if (DEBUGLEVEL >= 6) timer_printf(&ti, "ZX_chinese_center");
    G1 = G2; M1 = M2;
  }
  F = RgX_Rg_div(G1, d0);
  if (DEBUGLEVEL == 2)
    err_printf("G1:%ld, d0:%ld, M1:%ld, F:%ld\n",
               ZX_size(G1), Q_size(d0), Q_size(M1), ZX_size(F));
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "gausspol");
  return F;
}

/* Data = [H, GH, i_t, d0d1, kT, [n, d, f, n_T, mitk]]
 * v_t_el[k]=t_k mod el, 1<= k <= n-1 */
static GEN
mk_v_t_el(GEN vT, GEN Data, ulong el)
{
  pari_sp av = avma;
  GEN H = gel(Data, 1), GH = gel(Data,2), i_t = gel(Data, 3), N=gel(Data, 6);
  ulong n = N[1],  d = N[2], mitk = N[5], f = N[3], i, k;
  ulong z_n = rootsof1_Fl(n, el);
  GEN vz_n = Fl_powers(z_n, n-1, el)+1;
  GEN v_t_el = const_vecsmall(n-1, 0);

  for (k = 1; k <= mitk; k++)
  {
    if (k > 1 && !isintzero(gel(vT, k))) continue; /* k=1 is always handled */
    for (i=1; i<=f; i++)
    {
      ulong j, t = 0, x = Fl_mul(k, GH[i], n), y = i_t[x]; /* x!=0, y!=0 */
      if (v_t_el[y]) continue;
      for (j = 1; j <= d; j++) t = Fl_add(t, vz_n[Fl_mul(x, H[j], n)], el);
      v_t_el[y] = t;
    }
  }
  return gerepileuptoleaf(av, v_t_el);
}

/* G=[[G_1,...,G_d],M,el]
 * Data = [H, GH, i_t, d0d1, kT, [n, d, f, n_T, mitk]] */
static GEN
get_vG(GEN vT, GEN Data, ulong el, long n_el)
{
  GEN GH = gel(Data, 2), i_t = gel(Data, 3);
  GEN d0 = gmael(Data, 4, 1), d1 = gmael(Data, 4, 2);
  GEN kT = gel(Data, 5), N = gel(Data, 6);
  long n = N[1], f = N[3], n_T = N[4], mitk = N[5];
  GEN G = const_vec(mitk, gen_0), vPOL = cgetg(1+mitk, t_VEC);
  GEN EL = cgetg(1+n_el, t_VECSMALL), M, X, v_t_el;
  GEN L = cgetg(1+f, t_VECSMALL), x = cgetg(1+f, t_VECSMALL);
  long i, j, k;

  for (k=1; k<=mitk; k++) gel(vPOL, k) = cgetg(1+n_el, t_VEC);
  for (i=1; i<=n_el; i++)
  {
    long d0model;
    el = next_el_n(el, n, d1);
    d0model = umodiu(d0, el);
    EL[i] = el;
    v_t_el = mk_v_t_el(vT, Data, el);
    for (j = 1; j <= f; j++) L[j] = v_t_el[i_t[GH[j]]];
    X = Flv_invVandermonde(L, 1, el);
    for (k = 1; k <= n_T; k++)
    {
      GEN y;
      long itk = kT[k];
      if (!isintzero(gel(vT, itk))) continue;
      for (j = 1; j <= f; j++) x[j] = v_t_el[i_t[Fl_mul(itk, GH[j], n)]];
      y = Flv_to_Flx(Flm_Flc_mul(X, x, el), 0);
      gmael(vPOL, itk, i) = Flx_Fl_mul(y, d0model, el);
    }
  }
  for (k = 1; k <= n_T; k++)
  {
    long itk = kT[k];
    if (!isintzero(gel(vT, itk))) continue;
    gel(G, itk) = nxV_chinese_center(gel(vPOL, itk), EL, &M);
  }
  return mkvec3(G, M, utoi(el));
}

/* F=Q(zeta_n), H=<p> in (Z/nZ)^*, K<-->H, t_k=Tr_{F/K}(zeta_n^k).
 * i_t[i]==k ==> iH=kH, i.e. t_i==t_k. We use t_k instead of t_i.
 * the number of k << the number of i. */
static GEN
get_i_t(long n, long p)
{
  long a;
  GEN v_t = const_vecsmall(n-1, 0);
  GEN i_t = cgetg(n, t_VECSMALL);  /* access i_t[a] with 1 <= a <= n-1 */
  for (a = 1; a < n; a++)
  {
    long b;
    while (a < n && v_t[a]) a++;
    if (a==n) break;
    b = a;
    do { v_t[b] = 1; i_t[b] = a; b = Fl_mul(b, p, n); }
    while (b != a);
  }
  return i_t;
}

/* get T_k(x) 1<= k <= d. d0*T_k(x) is in Z[x].
 * T_0(x)=T_n(x)=f.
 * Data = [H, GH, i_t, d0d1, kT, [n, d, f, n_T, mitk]] */
static GEN
get_vT(GEN Data, int new)
{
  pari_sp av = avma;
  GEN d0 = gmael(Data, 4, 1), kT = gel(Data, 5), N=gel(Data, 6);
  ulong k, n = N[1], n_T = N[4], mitk = N[5];
  GEN vT = const_vec(mitk, gen_0); /* vT[k]!=NULL ==> vT[k]=T_k */
  ulong n_k = 0, el, n_el, start, second;
  GEN G, G1, G2, M1, M2;
  pari_timer ti;

  if (DEBUGLEVEL >= 6) timer_start(&ti);
  gel(vT, 1) = pol_x(0); n_k++;
  start = get_n_el(d0, &second);
  el = start_el_n(n);

  if (DEBUGLEVEL == 2) err_printf("get_vT: start=(%ld,%ld)\n",start,second);

  G = get_vG(vT, Data,  el, start);
  G1 = vecslice(gel(G,1), 1, mitk);
  M1 = gel(G, 2); el = itou(gel(G, 3));
  for (n_el=second; n_el; n_el++)
  {
    G = get_vG(vT, Data, el, n_el);
    G2 = vecslice(gel(G,1), 1, mitk);
    M2 = gel(G, 2); el = itou(gel(G, 3));
    for (k=1; k<=n_T; k++)
    {
      long itk = kT[k];
      if (!isintzero(gel(vT, itk))) continue;
      if (FpX_degsub(gel(G1, itk), gel(G2, itk), M2) < 0) /* G1=G2 (mod M2) */
      {
        gel(vT, itk) = RgX_Rg_div(gel(G1, itk), d0);
        n_k++;
        if (DEBUGLEVEL == 2)
          err_printf("G1:%ld, d0:%ld, M1:%ld, vT[%ld]:%ld words\n",
            ZX_size(gel(G1, itk)), Q_size(d0), Q_size(M1), itk, ZX_size(gel(vT, itk)));
      }
      else
      {
        if (DEBUGLEVEL == 2)
          err_printf("G1:%ld, G2:%ld\n",
                  ZX_size(gel(G1, itk)), ZX_size(gel(G2, itk)));
        gel(G1, itk) = ZX_chinese_center(gel(G1, itk), M1, gel(G2, itk), M2);
      }
    }
    if (n_k==n_T) break;
    M1 = mulii(M1, M2);
  }
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "get_vT");
  return gerepilecopy(av, vT);
}

/* return sorted kT={i_t[k] | 1<=k<=d}
 * {T_k(x) | k in kT} are all the different T_k(x) (1<=k<=d) */
static GEN
get_kT(GEN i_t, long d)
{
  return vecsmall_uniq(vecsmall_shorten(i_t, d));
}

static GEN
get_kT_all(GEN GH, GEN i_t, long n, long d, long m)
{
  long i, j, k = 0;
  GEN x = const_vecsmall(d*m, 0);
  for(i=1; i<=m; i++)
    for(j=1; j<=d; j++)
      x[++k] = i_t[Fl_mul(GH[i], j, n)];
  return vecsmall_uniq(x);
}

static GEN
kT_from_kt_new(GEN gGH, GEN kt, GEN i_t, long n)
{
  GEN EL = gel(gGH, 1);
  long i, k = 0, lEL = lg(EL), lkt = lg(kt);
  GEN x = cgetg(lEL+lkt, t_VECSMALL);

  for (i = 1; i < lEL; i++) x[++k] = i_t[EL[i]];
  for (i = 2; i < lkt; i++) if (n%kt[i]==0) x[++k] = kt[i];
  return vecsmall_uniq(vecsmall_shorten(x, k));
}

static GEN
get_kTdiv(GEN kT, long n)
{
  long i, k = 0, l = lg(kT);
  GEN div = cgetg(l, t_VECSMALL);
  for(i = 1; i < l; i++) if (n%kT[i]==0) div[++k] = kT[i];
  setlg(div, k+1);
  return div;
}

/* T is separable over Zp but not separable over Fp.
 * receive all roots mod p^s and return all roots mod p^(s+1) */
static GEN
ZpX_roots_nonsep(GEN T, GEN R0, GEN p, GEN ps, GEN ps1)
{
  long i, j, n = 0, lr = lg(R0);
  GEN v = cgetg(lr, t_VEC), R;
  for (i = 1; i < lr; i++)
  {
    GEN z, f = ZX_unscale_div(ZX_translate(T, gel(R0, i)), ps);
    (void)ZX_pvalrem(f, p, &f);
    gel(v, i) = z = FpX_roots(f, p);
    n += lg(z)-1;
  }
  R = cgetg(n+1, t_VEC); n = 0;
  for (i = 1; i < lr; i++)
  {
    GEN z = gel(v, i);
    long lz = lg(z);
    for (j=1; j<lz; j++)
      gel(R, ++n) = Fp_add(gel(R0, i), mulii(gel(z, j), ps), ps1);
  }
  return ZV_sort_uniq_shallow(R);
}
static GEN
ZpX_roots_all(GEN T, GEN p, long f, long *ptrs)
{
  pari_sp av = avma;
  pari_timer ti;
  GEN v, ps, ps1;
  long s;

  if (DEBUGLEVEL >= 6) timer_start(&ti);
  v = FpX_roots(T, p); /* FpX_roots returns sorted roots */
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "FpX_roots, deg=%ld", degpol(T));
  ps = NULL; ps1 = p;
  for (s = 1; lg(v) != f+1; s++)
  {
    ps = ps1; ps1 = mulii(ps1, p); /* p^s, p^(s+1) */
    v = ZpX_roots_nonsep(T, v, p, ps, ps1);
    if (gc_needed(av, 1)) gerepileall(av, 3, &v, &ps, &ps1);
  }
  *ptrs = s; return v;
}
/* x : roots of T in Zp. r < n.
 * receive vec of x mod p^r and return vec of x mod p^n.
 * under the assumtion lg(v)-1==degpol(T), x is uniquely determined by
 * x mod p^r. Namely, x mod p^n is unique. */
static GEN
ZX_Zp_liftroots(GEN T, GEN v, GEN p, long r, long n)
{
  long i, l = lg(v);
  GEN R = cgetg(l, t_VEC);
  GEN pr = powiu(p, r), pn = powiu(p, n);
  pari_timer ti;

  if (DEBUGLEVEL >= 6) timer_start(&ti);
  for (i=1; i<l; i++)
  {
    GEN x = gel(v, i), y, z;
    GEN f = ZX_unscale_div(ZX_translate(T, x), pr);
    (void)ZX_pvalrem(f, p, &f);
    y = FpX_roots(f, p);
    z = (n==r+1) ? y : ZX_Zp_root(f, gel(y, 1), p, n-r);
    if (lg(y)!=2 || lg(z)!=2)
      pari_err_BUG("ZX_Zp_liftroots, roots are not separable");
    gel(R, i) = Fp_add(x, mulii(gel(z, 1), pr), pn);
  }
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "ZX_Zp_liftroots");
  return R;
}

static GEN
set_R(GEN T, GEN F, GEN Rs, GEN p, long nf, long r, long s, long u)
{
  long i;
  GEN x, pr = powiu(p, r), prs = powiu(p, r+s), R = cgetg(1+nf, t_VEC), Rrs;
  Rrs = r ? ZX_Zp_liftroots(T, Rs, p, s, r+s) : Rs;
  x = gel(Rrs, 1);
  for (i = 1; i <= nf; i++)
  {
    x = FpX_eval(F, x, prs);
    if (r) x = gel(Rrs, ZV_search(Rs, diviiexact(x, pr)));
    gel(R, i) = x;  /* R[i]=t_1^(g^i), t_1=Rrs[1], mod p^(r+s) */
  }
  if (r+s < u) R = ZX_Zp_liftroots(T, R, p, r+s, u);
  else if (r+s > u) R = FpV_red(R, powiu(p, u));
  return R;  /* mod p^u, accuracy for pol_newton */
}

/* 1+y+ ... +y^(el-1), y=x^(el^(e-1)) */
static GEN
RgX_polcyclo_el_e(ulong el, ulong e)
{
  ulong i;
  GEN x = cgetg(el+2, t_POL);
  x[1] = evalsigne(1) | evalvarn(0);
  for (i = 0; i < el; i++) gel(x, 2+i) = gen_1;
  return e > 1 ? RgX_inflate(x, upowuu(el, e-1)): x;
}

static GEN
Flx_polcyclo_el_e(ulong el, ulong e)
{
  GEN x = const_vecsmall(el+1, 1);
  return e > 1 ? Flx_inflate(x, upowuu(el, e-1)): x;
}

/* Preparation for factoring polcyclo(el^e) mod p
 * f_0(x) : irred factor of polcyclo(el^e0) mod p
 * f_1(x)=f_0(x^(el^e1)) : irred factor of polcyclo(el^e) mod p
 *
 * p^d0 = 1 (mod el^e0), p^d = 1 (mod el^e)
 *
 * case el=2, 2^s || (p-1), s>=2
 * d=1 (1 <= e <= s), d=2^(e-s) (s < e)
 * e0=e, e1=0 if e <= s
 * e0=s, e1=e-s if s < e
 * d0=1
 *
 * case el=2, 2^s || (p+1), s>=2
 * d=1 (e == 1), d=2 (2 <= e <= s), d=2^(e-s) (s < e)
 * e0=e, e1=0 if e <= s+1
 * e0=s+1, e1=e-s-1 if s+1 < e
 * d0=1 if e==1,  d0=2 if e>1
 *
 * case el>2, el^s || (p^d0-1)
 * d=d0 (1 <= e <= s), d=d0*el^(e-s) (s < e)
 * e0=e, e1=0 if e <= s
 * e0=s, e1=e-s if s < e
 * d0 is min d s.t. p^d=1 (mod el)
 *
 * We do not need d. So d is not returned. */
static GEN
set_e0_e1(ulong el, ulong e, GEN p)
{
  ulong s, d0, e0, e1, f0, n, phin, g, up = (lgefint(p)==3)?p[2]:0;
#ifdef DEBUG
  ulong d;
#endif

  if (el == 2)
  {
    ulong pmod4 = up ? up&3 : p[2]&3;
    if (pmod4 == 3)  /* p+1 = 0 (mod 4) */
    {
      s = up ? vals(up+1) : vali(addiu(p, 1));
#ifdef DEBUG
      if (e == 1) d = 1;
      else if (e <= s) d = 2;
      else d = 1L<<(e-s);
#endif
      if (e <= s+1) { e0 = e; e1 = 0;}
      else { e0 = s+1; e1= e-s-1;}
      d0 = e == 1? 1: 2;
    }
    else  /* p-1 = 0 (mod 4) */
    {
      s = up ? vals(up-1) : vali(subiu(p, 1));
#ifdef DEBUG
      d = (e<=s)?1:1L<<(e-s);
#endif
      if (e <= s) { e0 = e; e1 = 0; }
      else { e0 = s; e1 = e-s; }
      d0 = 1;
    }
    phin = 1L<<(e0-1);
  }
  else  /* el is odd */
  {
    ulong pmodel = up ? up%el : umodiu(p, el);
    d0 = Fl_order(pmodel, el-1, el);
#ifdef DEBUG
    d = d0;
#endif
    s = Z_lval(subiu(powiu(p, d0), 1), el);
#ifdef DEBUG
    if (s < e) d *= upowuu(el, e-s);
#endif
    if (e <= s) { e0 = e; e1 = 0; }
    else {e0 = s; e1= e-s; }
    phin = (el-1)*upowuu(el, e0-1);
  }
  n = upowuu(el, e0); f0 = phin/d0;
  g = (el==2) ? 1 : pgener_Zl(el);
  return mkvecsmalln(7, n, e0, e1, phin, g, d0, f0);
}

/* return 1 if newton is fast, return 0 if gen is fast */
static long
use_newton(long d, long f)
{
  if (2*d <= f) return 0;
  else if (f <= d) return 1;
  else if (d <= 50) return 0;
  else if (f <= 60) return 1;
  else if (d <= 90) return 0;
  else if (f <= 150) return 1;
  else if (d <= 150) return 0;
  else if (f <= 200) return 1;
  else if (200*d <= f*f) return 0;
  else return 1;
}

/* return 1 if newton_general is fast, return 0 otherwise */
static long
use_newton_general(long d, long f, long max_deg)
{
  if (max_deg == 1) return 0;
  else if (f <= 40) return 1;
  else if (max_deg < 20) return 0;
  else if (f <= 50) return 1;
  else if (max_deg < 30) return 0;
  else if (f <= 60) return 1;
  else if (max_deg < 40) return 0;
  else if (f <= 70) return 1;
  else if (max_deg < 50) return 0;
  else if (f <= 80) return 1;
  else if (d < 200) return 0;
  else if (f <= 100) return 1;
  else if (d < 300) return 0;
  else if (f <= 120) return 1;
  else if (6*max_deg < f*f) return 0;
  else return 1;
}

static ulong
set_action(GEN fa, GEN p, long d, long f)
{
  GEN EL = gel(fa, 1), E = gel(fa, 2);
  long i, l = lg(EL), d0 = 1, f0 = 1, d1, f1, m0 = 0, m1 = 0;
  long maxdeg = 1, max = 1;
  GEN D = cgetg(l, t_VECSMALL), F = cgetg(l, t_VECSMALL);
  ulong action = 0;

  d += 10*(lgefint(p)-3);
  if (l == 2)
  { /* n is a prime power */
    action |= (EL[1]==2 || !use_newton(d, f))? GENERAL: NEWTON_POWER;
    return action;
  }
  if (f <= 2) action |= NEWTON_GENERAL;
  else if (d <= 10) action |= GENERAL;
  else if (f <= 10) action |= NEWTON_GENERAL;
  else if (d <= 20) action |= GENERAL;
  else if (f <= 20) action |= NEWTON_GENERAL_NEW;
  else if (d <= 30) action |= GENERAL;
  else if (f <= 30) action |= NEWTON_GENERAL_NEW;
  else if (d <= 40) action |= GENERAL;
  else if (f <= 40) action |= NEWTON_GENERAL_NEW;
  if (action) return action;

  for (i = 1; i < l; i++)
  {
    long x, el = EL[i], e = E[i], ni = upowuu(el, e);
    long phini = (el-1) * upowuu(el, e-1);
    long di = Fl_order(umodiu(p, ni), phini, ni), fi = phini/di;
    D[i] = di; F[i] = fi;
    d0 *= di; f0 *= fi;
    x = ugcd(max, di); max = max*di/x;
    if (x > 1) maxdeg = max*x;
    if (DEBUGLEVEL == 4) err_printf("(%ld,%ld), ",di,fi);
  }
  if (DEBUGLEVEL == 4) err_printf("(d0,f0)=(%ld,%ld)\n",d0,f0);
  if (maxdeg == 1) return action;
  if((p[2] != 2 && use_newton_general(d, f, maxdeg)) ||
     (p[2] == 2 && f <= 40))  /* does not decompose n */
  {
    action |= (20 < d)? NEWTON_GENERAL_NEW: NEWTON_GENERAL;
    return action;
  }

  if(d <= 20) action |= GENERAL;
  else if (p[2] == 2) action &= ~GENERAL;
  else if (d <= 50) action |= GENERAL;
  else if (maxdeg <= 3*d) action &= ~GENERAL;
  else if (d <= 200) action |= GENERAL;
  else if (maxdeg <= 10*d) action &= ~GENERAL;
  else if (d <= 500) action |= GENERAL;
  else if (maxdeg <= 20*d) action &= ~GENERAL;
  else if (d <= 1000) action |= GENERAL;
  else action &= ~GENERAL;
  if (l <= 3) return action;  /* n has two factors */

  d0 = f0 = 1;  /* decompose n */
  for (i = 1; i < l; i++)
  {
    long di = D[i], fi = F[i];
    long d = ulcm(d0, di), f = (d0*di*f0*fi)/d;
    d1 = d0*di; f1 = f0*fi;
    d0 = d; f0 = f;
    m0 += d1*d1*f1;
    if (DEBUGLEVEL == 4) err_printf("(%ld,%ld), ",d1,f1);
  }
  if (DEBUGLEVEL == 4) err_printf("(d0,f0)=(%ld,%ld)\n",d0,f0);
  d0 = f0 = 1;
  for (i=l-1; i>=1; i--)
  {
    long di = D[i], fi = F[i];
    long d = ulcm(d0, di), f = (d0*di*f0*fi)/d;
    d1 = d0*di; f1 = f0*fi;
    d0 = d; f0 = f;
    m1 += d1*d1*f1;
    if (DEBUGLEVEL == 4) err_printf("(%ld,%ld), ",d1,f1);
  }
  if (DEBUGLEVEL == 4) err_printf("(d0,f0)=(%ld,%ld)\n",d0,f0);
  if (DEBUGLEVEL == 4) err_printf("(m0,m1)=(%lu,%lu) %ld\n",m0,m1,m0<=m1);
  if (m0 <= m1) action |= ASCENT;
  return action;
}

/*  Data = [H, GH, i_t, d0, kT, [n, d, f, n_T, mitk]]
    Data2 = [vT, polcyclo_n, p, pr, pu, pru] */
static GEN
FpX_pol_newton_general(GEN Data, GEN Data2, GEN x)
{
  pari_sp av = avma;
  GEN i_t = gel(Data, 3), kT = gel(Data, 5), N = gel(Data, 6);
  long k, d = N[2], n_T = N[4], mitk = N[5];
  GEN vT = gel(Data2, 1), polcyclo_n = gel(Data2, 2), p = gel(Data2, 3);
  GEN pr = gel(Data2, 4), pu = gel(Data2, 5), pru = gel(Data2, 6);
  GEN S = cgetg(2+d, t_VEC), R = cgetg(1+mitk, t_VEC), P;

  for(k = 1; k<=n_T; k++)
   gel(R, kT[k]) = diviiexact(FpX_eval(gel(vT, kT[k]), x, pru), pr);
  gel(S, 1) = utoi(d);
  for(k = 1; k <= d; k++) gel(S, 1+k) = gel(R, i_t[k]);
  P = FpX_red(FpX_fromNewton(RgV_to_RgX(S, 0), pu), p);
  if (degpol(FpX_rem(polcyclo_n, P, p)) >= 0)
    pari_err_BUG("FpX_pol_newton_general");
  return gerepileupto(av,P);
}

/* n is any integer prime to p, but must be equal to the conductor
 * of the splitting field of p in Q(zeta_n).
 * GH=G/H={g_1, ... ,g_f}
 * Data = [GHgen, GH, fn, p, [n, d, f, m]] */
static GEN
FpX_factcyclo_newton_general(GEN Data)
{
  GEN GH = gel(Data, 2), fn = gel(Data, 3), p = gel(Data, 4);
  long n = mael(Data, 5, 1), d = mael(Data, 5, 2), f = mael(Data, 5, 3);
  long m = mael(Data, 5, 4), pmodn = umodiu(p, n);
  long i, k, n_T, mitk, r, s = 0, u = 1;
  GEN vT, kT, H, i_t, T, d0d1, Data2, Data3, R, Rs, pr, pu, pru, pols;
  GEN polcyclo_n;
  pari_timer ti;

  if (m != 1) m = f;
  pols = cgetg(1+m, t_VEC);
  for (pu = p; cmpiu(pu,d)<=0; u++) pu = mulii(pu, p);  /* d<pu, pu=p^n */

  H = Fl_powers(pmodn, d-1, n); /* H=<p> */
  i_t = get_i_t(n, pmodn); /* i_t[1+i]=k ==> t_i=t_k */
  kT = get_kT(i_t, d); n_T = lg(kT)-1; mitk = kT[n_T];
  if (DEBUGLEVEL == 2) err_printf("kT=%Ps %ld elements\n",kT,n_T);
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  T = galoissubcyclo(utoi(n), utoi(pmodn), 0, 0);
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "galoissubcyclo");
  d0d1 = get_d0_d1(T, gel(fn,1)); /* d0*T_k(x) is in Z[x] */
  Data2 = mkvecn(6, H, GH, i_t, d0d1, kT, mkvecsmalln(5, n, d, f, n_T, mitk));
  vT = get_vT(Data2, 0);
  if (DEBUGLEVEL == 4) err_printf("vT=%Ps\n",vT);
  r = QXV_den_pval(vT, kT, p);
  Rs = ZpX_roots_all(T, p, f, &s);
  if (DEBUGLEVEL >= 2) err_printf("(u,s,r)=(%ld,%ld,%ld)\n",u,s,r);
  if (r+u<s) pari_err_BUG("FpX_factcyclo_newton_general (T(x) is not separable mod p^(r+u))");
  /* R and vT are mod p^(r+u) */
  R = (r+u==s) ? Rs : ZX_Zp_liftroots(T, Rs, p, s, r+u);
  pr = powiu(p, r); pru = powiu(p, r+u); /* Usually, r=0, s=1, pr=1, pru=p */
  for (k = 1; k<=n_T; k++)
  {
    long itk = kT[k];
    gel(vT, itk) = r ? RgX_to_FpX(RgX_Rg_mul(gel(vT, itk), pr), pru):
                       RgX_to_FpX(gel(vT, itk), pru);
  }
  polcyclo_n = FpX_polcyclo(n, p);
  Data3 = mkvecn(6, vT, polcyclo_n, p, pr, pu, pru);
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  for (i=1; i<=m; i++)
    gel(pols, i) = FpX_pol_newton_general(Data2, Data3, gel(R, i));
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "FpX_pol_newton_general");
  return pols;
}

/* Data = [vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
          [n, r, s, n_t,mitk], div, polcyclo_n] */
static void
Fp_next_gen3(long x, long i, GEN v_t_p, GEN t, GEN Data)
{
  GEN vT = gel(Data, 1), gGH = gel(Data, 2), Rs = gel(Data, 3);
  GEN Rrs = gel(Data, 4), i_t = gel(Data, 5);
  GEN pu = gel(Data, 8), pr = gel(Data, 9), prs = gel(Data, 10);
  GEN EL = gel(gGH, 1), E = gel(gGH, 2), div = gel(Data, 12);
  long n = mael(Data, 11, 1), mitk = mael(Data, 11, 5);
  long r = mael(Data, 11, 2);
  long j, k, l = lg(EL), ld = lg(div);

  if (i >= l) return;
  for (j = 0; j<E[i]; j++)
  {
    if (j > 0)
    {
      long itx = i_t[x];
      t = FpX_eval(gel(vT, i_t[EL[i]]), t, prs); /* mod p^(r+s) */
      if (r) t = gel(Rrs, ZV_search(Rs, diviiexact(t, pr))); /* mod p^(r+s) */
      if (itx <= mitk) gel(v_t_p, itx) = Fp_red(t, pu); /* mod p^u */
      for (k = 1; k<ld; k++)
      {
        long y = Fl_mul(x, div[k], n), ity = i_t[y];
        GEN v;
        if (ity > mitk || !isintzero(gel(v_t_p, ity))) continue;
        v = FpX_eval(gel(vT, i_t[div[k]]), t, prs); /* mod p^(r+s) */
        if (r) v = diviiexact(v, pr); /* mod p^s */
        gel(v_t_p, ity) = Fp_red(v, pu);
      }
    }
    Fp_next_gen3(x, i+1, v_t_p, t, Data);
    x = Fl_mul(x, EL[i], n);
  }
}

/* Data = [vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
          [n, r, s, n_t, mitk], div, polcyclo_n] */
static GEN
Fp_mk_v_t_p3(GEN Data, long i)
{
  /* v_t_p[k]!=gen_0 ==> v_t_p[k]=t_k mod p^u */
  GEN Rs = gel(Data, 3), Rrs = gel(Data, 4);
  GEN pu = gel(Data, 8), pr = gel(Data, 9), prs = gel(Data, 10);
  GEN vT = gel(Data, 1), i_t = gel(Data, 5);
  GEN div = gel(Data, 12);
  long r = mael(Data, 11, 2), mitk = mael(Data, 11, 5);
  long k, ld = lg(div);
  GEN v_t_p = const_vec(mitk, gen_0);

  gel(v_t_p, 1) = Fp_red(gel(Rs, i), pu); /* mod p^u, guaranteed u<=s */
  Fp_next_gen3(1, 1, v_t_p, gel(Rrs, i), Data);
  for (k = 1; k<ld; k++)
  {
    GEN x;
    ulong itk = i_t[div[k]];
    x = FpX_eval(gel(vT, itk), gel(Rrs, i), prs);
    if (r) x = diviiexact(x, pr); /* mod p^s */
    gel(v_t_p, itk) = Fp_red(x, pu);
  }
  return v_t_p;
}

/* Data = [vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
          [n, r, s, n_t,mitk], div, polcyclo_n] */
static void
Fl_next_gen3(long x, long i, GEN v_t_p, ulong t, GEN Data)
{
  GEN vT = gel(Data, 1), gGH = gel(Data, 2), Rs = gel(Data, 3);
  GEN Rrs = gel(Data, 4), i_t = gel(Data, 5);
  long pu = mael(Data, 8, 2), pr = mael(Data, 9, 2), prs = mael(Data, 10, 2);
  GEN EL = gel(gGH, 1), E = gel(gGH, 2), div = gel(Data, 12);
  long n = mael(Data, 11, 1), mitk = mael(Data, 11, 5);
  long r = mael(Data, 11, 2);
  long j, k, l = lg(EL), ld = lg(div);
  if (i >= l) return;
  for (j = 0; j<E[i]; j++)
  {
    if (j > 0)
    {
      long itx = i_t[x];
      t = Flx_eval(gel(vT, i_t[EL[i]]), t, prs); /* mod p^(r+s) */
      if (r) t = Rrs[zv_search(Rs, t/pr)]; /* mod p^(r+s) */
      if (itx <= mitk) v_t_p[itx] = t%pu; /* mod p^u */
      for (k = 1; k < ld; k++)
      {
        long y = Fl_mul(x, div[k], n), ity = i_t[y], v;
        if (ity > mitk || v_t_p[ity]) continue;
        v = Flx_eval(gel(vT, i_t[div[k]]), t, prs); /* mod p^(r+s) */
        if (r) v /= pr; /* mod p^s */
        v_t_p[ity] = v%pu;
      }
    }
    Fl_next_gen3(x, i+1, v_t_p, t, Data);
    x = Fl_mul(x, EL[i], n);
  }
}

/* Data = [vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
          [n, r, s, n_t, mitk], div, polcyclo_n] */
static GEN
Fl_mk_v_t_p3(GEN Data, long i)
{
  /* v_t_p[k]!=NULL ==> v_t_p[k]=t_k mod p^u */
  GEN Rs = gel(Data, 3), Rrs = gel(Data, 4);
  ulong pu = mael(Data, 8, 2), pr = mael(Data, 9, 2), prs = mael(Data, 10, 2);
  GEN vT = gel(Data, 1), i_t = gel(Data, 5);
  GEN div = gel(Data, 12);
  long r = mael(Data, 11, 2), mitk = mael(Data, 11, 5);
  long k, ld = lg(div);
  GEN v_t_p = const_vecsmall(mitk, 0);

  v_t_p[1] = Rs[i]%pu; /* mod p^u, guaranteed u<=s */
  Fl_next_gen3(1, 1, v_t_p, Rrs[i], Data);
  for (k = 1; k < ld; k++)
  {
    ulong x, itk = i_t[div[k]];
    x = Flx_eval(gel(vT, itk), Rrs[i], prs);
    if (r) x /= pr; /* mod p^s */
    v_t_p[itk] = x%pu;
  }
  return v_t_p;
}

static GEN
/* Data = [GHgen, GH, fn, p, [n, d, f, m]] */
newton_general_new_pre3(GEN Data)
{
  GEN gGH = gel(Data, 1), GH = gel(Data, 2), fn = gel(Data, 3);
  GEN p = gel(Data, 4);
  long n = mael(Data, 5, 1), d = mael(Data, 5, 2), f = mael(Data, 5, 3);
  long pmodn = umodiu(p, n);
  long k, n_t, n_T, mitk, miTk, r, s = 0, u = 1;
  GEN vT, kt, kT, H, i_t, T, d0d1, Data2, Data3, Rs, Rrs, kTdiv;
  GEN pr, pu, prs;
  pari_timer ti;

  for (pu = p; cmpiu(pu,d)<=0; u++) pu = mulii(pu, p);  /* d<pu, pu=p^u */

  H = Fl_powers(pmodn, d-1, n); /* H=<p> */
  i_t = get_i_t(n, pmodn); /* i_t[1+i]=k ==> t_i=t_k */
  kt = get_kT_all(GH, i_t, n, d, 1); n_t = lg(kt)-1; mitk = kt[n_t];
  kT = kT_from_kt_new(gGH, kt, i_t, n); n_T = lg(kT)-1; miTk = kT[n_T];
  kTdiv = get_kTdiv(kT, n);
  if (DEBUGLEVEL == 2)
    err_printf("kt=%Ps %ld elements\nkT=%Ps %ld elements\n",kt,n_t,kT,n_T);
  if (DEBUGLEVEL == 2)
    err_printf("kTdiv=%Ps\n",kTdiv);

  if (DEBUGLEVEL >= 6) timer_start(&ti);
  T = galoissubcyclo(utoi(n), utoi(pmodn), 0, 0);
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "galoissubcyclo");
  d0d1 = get_d0_d1(T, gel(fn,1)); /* d0*T_k(x) is in Z[x] */
  Data2 = mkvecn(6, H, GH, i_t, d0d1, kT, mkvecsmalln(5, n, d, f, n_T, miTk));
  vT = get_vT(Data2, 1);
  if (DEBUGLEVEL == 4) err_printf("vT=%Ps\n",vT);
  r = QXV_den_pval(vT, kT, p);
  Rs = ZpX_roots_all(T, p, f, &s);
  if (DEBUGLEVEL >= 2) err_printf("(u,s,r)=(%ld,%ld,%ld)\n",u,s,r);
  if (s < u)
  {
    Rs = ZV_sort_shallow(ZX_Zp_liftroots(T, Rs, p, s, u));
    s = u;
  }
  /* Rs : mod p^s, Rrs : mod p^(r+s), vT : mod p^(r+s) */
  Rrs = r ? ZX_Zp_liftroots(T, Rs, p, s, r+s) : Rs;
  pr = powiu(p, r); prs = powiu(p, r+s); /* Usually, r=0, s=1, pr=1, pru=p */
  if (lgefint(prs)>3)  /* ULONG_MAX < p^(r+s), usually occur */
  {
    for(k = 1; k <= n_T; k++)
    {
      long itk = kT[k];
      gel(vT, itk) = r ? RgX_to_FpX(RgX_Rg_mul(gel(vT, itk), pr), prs):
                         RgX_to_FpX(gel(vT, itk), prs);
    }
    Data3 = mkvecn(12, vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
                   mkvecsmalln(6, n, r, s, n_t, mitk, d), kTdiv);
  }
  else  /* p^(r+s) < ULONG_MAX, frequently occur */
  {
    ulong upr = itou(pr), uprs = itou(prs);
    for (k = 1; k <= n_T; k++)
    {
      long itk = kT[k];
      gel(vT, itk) = r ? RgX_to_Flx(RgX_muls(gel(vT, itk), upr), uprs):
                         RgX_to_Flx(gel(vT, itk), uprs);
    }
    Rs = ZV_to_nv(Rs); Rrs = ZV_to_nv(Rrs);
    Data3 = mkvecn(12, vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
                   mkvecsmalln(6, n, r, s, n_t, mitk, d), kTdiv);
  }
  return Data3;
}

/* Data=[vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
 *      [n, r, s, n_t, mitk, d], div, polcyclo_n] */
static GEN
FpX_pol_newton_general_new3(GEN Data, long k)
{
  GEN i_t = gel(Data, 5), p = gel(Data, 7), pu = gel(Data, 8);
  GEN polcyclo_n = gel(Data, 13);
  long i, d = mael(Data, 11, 6);
  GEN S = cgetg(2+d, t_VECSMALL), v_t_p, P;

  v_t_p = Fp_mk_v_t_p3(Data, k);
  if (DEBUGLEVEL == 3) err_printf("v_t_p=%Ps\n",v_t_p);
  gel(S, 1) = utoi(d);
  for (i = 1; i <= d; i++) gel(S, 1+i) = gel(v_t_p, i_t[i]);
  P = FpX_red(FpX_fromNewton(RgV_to_RgX(S, 0), pu), p);
  if (degpol(FpX_rem(polcyclo_n, P, p)) >= 0)
    pari_err_BUG("FpX_pol_newton_general_new3");
  return P;
}

/* Data = [GHgen, GH, fn, p, [n, d, f, m]] */
static GEN
FpX_factcyclo_newton_general_new3(GEN Data)
{
  GEN p = gel(Data, 4), Data2, pols;
  long n = mael(Data, 5, 1), f = mael(Data, 5, 3), m = mael(Data, 5, 4);
  long i;
  pari_timer ti;

  if (m != 1) m = f;
  pols = cgetg(1+m, t_VEC);
  Data2 = newton_general_new_pre3(Data);
  /* Data2 = [vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
              [n, r, s, n_t, mitk, d], div] */

  Data2 = vec_append(Data2, FpX_polcyclo(n, p));
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  for (i = 1; i <= m; i++)
    gel(pols, i) = FpX_pol_newton_general_new3(Data2, i);
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "FpX_pol_newton_general_new3");
  return pols;
}

/* return normalized z(-x) */
static GEN
FpX_1st_lift_2(GEN z, GEN p)
{
  long i, r = lg(z);
  GEN x = cgetg(r, t_POL);
  x[1] = evalsigne(1) | evalvarn(0);
  for (i = 2; i < r; i++) gel(x, i) = (i&1) ? Fp_neg(gel(z, i), p) : gel(z, i);
  return (r&1) ? x : FpX_neg(x, p);
}

static GEN
FpX_1st_lift(GEN z, GEN p, ulong e, ulong el, GEN vP)
{
   GEN P, z2, z3;
   if (isintzero(gel(vP, e))) gel(vP, e) = FpX_polcyclo(e, p);
   P = gel(vP, e);
   z2 = RgX_inflate(z, el);
   z3 = FpX_normalize(FpX_gcd(P, z2, p), p);
   return FpX_div(z2, z3, p);
}

static GEN
FpX_lift(GEN z, GEN p, ulong e, ulong el, ulong r, ulong s, GEN vP)
{
  if (s == 0) z = (el==2) ? FpX_1st_lift_2(z, p) : FpX_1st_lift(z, p, e, el, vP);
  if (s > 0) z = RgX_inflate(z, upowuu(el, r-s));
  else if (r >= 2) z = RgX_inflate(z, upowuu(el, r-1));
  return z;
}

/* e is the conductor of the splitting field of p in Q(zeta_n) */
static GEN
FpX_conductor_lift(GEN z, GEN p, ulong n, ulong e, GEN vP)
{
  GEN fn = factoru(n), EL = gel(fn, 1), En = gel(fn, 2);
  long i, r = lg(EL), new_e = e;

  for(i = 1; i < r; i++)
  {
    long el = EL[i], en = En[i], ee = u_lval(e, el);
    if (ee < en)
    {
      z = FpX_lift(z, p, new_e, el, en, ee, vP);
      new_e *= upowuu(el, en-ee);
    }
  }
  return z;
}

/* R0 is mod p^u, d < p^u */
static GEN
FpX_pol_newton(long j, GEN Data, GEN N, long d, long f, GEN p)
{
  pari_sp av = avma;
  long el = N[2], e = N[3];
  GEN R0 = gel(Data, 1), E = gel(Data, 2), D3 = gel(Data, 3);
  long i, u = D3[3];
  GEN S = cgetg(2+d, t_VEC), R = cgetg(1+f, t_VEC), pu = powiu(p, u), P;

  for (i = 1; i <= f; i++) gel(R, i) = gel(R0, 1+(i+j)%f);
  gel(S, 1) = utoi(d);
  for (i = 1; i <= d; i++) gel(S, 1+i) = gel(R, E[i]);
  P = FpX_red(FpX_fromNewton(RgV_to_RgX(S, 0), pu), p);
  if (degpol(FpX_rem(RgX_polcyclo_el_e(el, e), P, p)) >= 0)
    pari_err_BUG("FpX_pol_newton: gausspol");
  return gerepilecopy(av, P);
}

/* Data = [T, F, Rs, [d, nf, g, r, s, u]], nf>1 */
static GEN
FpX_factcyclo_newton_pre(GEN Data, GEN N, GEN p, ulong m)
{
  pari_sp av = avma;
  GEN T = gel(Data, 1), F = gel(Data, 2), Rs = gel(Data, 3), D4 = gel(Data, 4);
  long d = D4[1], nf = D4[2], g = D4[3], r = D4[4], s = D4[5], u = D4[6];
  GEN pols, E, R, Data3;
  ulong i, n = N[1], pmodn = umodiu(p, n);
  pari_timer ti;

  if (m!=1) m = nf;
  pols = cgetg(1+m, t_VEC);
  E = set_E(pmodn, n, d, nf, g);
  R = set_R(T, F, Rs, p, nf, r, s, u);
  Data3 = mkvec3(R, E, mkvecsmall3(r, s, u));
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  for (i = 1; i <= m; i++) gel(pols, i) = FpX_pol_newton(i, Data3, N, d, nf, p);
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "FpX_pol_newton");
  return gerepilecopy(av, pols);
}

/* gcd(n1,n2)=1, e = gcd(d1,d2).
 * phi(n1) = d1*nf1, phi(n2) = d2*nf2.
 * d = lcm(d1,d2) = d1*d2/e, nf = phi(n1)*phi(n2)/d = nf1*nf2*e. */
static GEN
FpX_factcyclo_lift(long n1, GEN v1, long n2, GEN v2, GEN p, long m)
{
  pari_sp av = avma;
  long d1 = degpol(gel(v1, 1)), lv1 = lg(v1), nf1 = eulerphiu(n1)/d1;
  long d2 = degpol(gel(v2, 1)), lv2 = lg(v2), nf2 = eulerphiu(n2)/d2;
  long e = ugcd(d1, d2), nf = nf1*nf2*e, need_factor = (e!=1);
  long i, j, k = 0;
  GEN z = NULL, v;
  pari_timer ti;

  if (DEBUGLEVEL >= 6) timer_start(&ti);
  if (m != 1) m = nf;
  v = cgetg(1+m, t_VEC);
  if (m == 1)
  {
    GEN x1 = gel(v1, 1), x2 = gel(v2, 1);
    z = FpX_gcd(RgX_inflate(x1, n2), RgX_inflate(x2, n1), p);
    z = FpX_normalize(z, p);  /* FpX_gcd sometimes returns non-monic */
    gel(v, 1) = (!need_factor)? z : gmael(FpX_factor(z, p), 1, 1);
  }
  else
  {
    for (i = 1; i < lv1; i++)
      for (j = 1; j < lv2; j++)
      {
        GEN x1 = gel(v1, i), x2 = gel(v2, j);
        z = FpX_gcd(RgX_inflate(x1, n2), RgX_inflate(x2, n1), p);
        z = FpX_normalize(z, p);  /* needed */
        if (!need_factor) gel(v, ++k) = z;
        else
        {
          GEN z1 = gel(FpX_factor(z, p), 1);
          long i, l = lg(z1);
          for (i = 1; i < l; i++) gel(v, ++k) = gel(z1, i);
        }
      }
  }
  if (DEBUGLEVEL >= 6)
    timer_printf(&ti, "FpX_factcyclo_lift (%ld,%ld)*(%ld,%ld)-->(%ld,%ld)-->(%ld,%ld)",
        d1, nf1, d2, nf2, degpol(z), nf1*nf2, d1*d2/e, nf);
  return gerepilecopy(av, v);
}

/* n is any integer prime to p; d>1 and f>1 */
static GEN
FpX_factcyclo_gen(GEN GH, ulong n, GEN p, long m)
{
  GEN fn = factoru(n), fa = zm_to_ZM(fn);
  GEN A, T, X, pd_n, v, pols;
  long i, j, pmodn = umodiu(p, n), phin = eulerphiu_fact(fn);
  long d = Fl_order(pmodn, phin, n), f = phin/d;
  pari_timer ti;

  if (m != 1) m = f;
  if (m != 1 && GH==NULL) /* FpX_factcyclo_fact is used */
  {
    GEN H = znstar_generate(n, mkvecsmall(pmodn));
    GH = znstar_cosets(n, phin, H); /* representatives of G/H */
  }

  pols = cgetg(1+m, t_VEC);
  v = cgetg(1+d, t_VEC);
  pd_n = diviuexact(subis(powiu(p, d), 1), n); /* (p^d-1)/n */
  T = init_Fq(p, d, 1);
  A = pol_x(1);  /* A is a generator of F_q, q=p^d */
  if (d == 1) A = FpX_rem(A, T, p);
  random_FpX(degpol(T), varn(T), p); /* skip 1st one */
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  do X = FpXQ_pow(random_FpX(degpol(T), varn(T), p), pd_n, T, p);
  while(lg(X)<3 || equaliu(FpXQ_order(X, fa, T, p), n)==0); /* find zeta_n */
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "find X");

  if (m == 1)
  {
    for (j = 1; j <= d; j++)
    {
      gel(v, j) = pol_x(0);
      gmael(v, j, 2) = FpX_neg(X, p);
      if (j < d) X = FpXQ_pow(X, p, T, p);
    }
    gel(pols, 1) = ZXX_evalx0(FpXQXV_prod(v, T, p));
  }
  else
  {
    GEN vX, vp;
    if (DEBUGLEVEL >= 6) timer_start(&ti);
    vX = FpXQ_powers(X, n, T, p)+1;
    vp = Fl_powers(pmodn, d, n);
    for (i = 1; i <= m; i++)
    {
      for (j = 1; j <= d; j++)
      {
        gel(v, j) = pol_x(0);
        gmael(v, j, 2) = FpX_neg(gel(vX, Fl_mul(GH[i], vp[j], n)), p);
      }
      gel(pols, i) = ZXX_evalx0(FpXQXV_prod(v, T, p));
    }
    if (DEBUGLEVEL >= 6) timer_printf(&ti, "FpXQXV_prod");
  }
  return pols;
}

static GEN Flx_factcyclo_newton_pre(GEN Data, GEN N, ulong p, ulong m);
/* n is an odd prime power prime to p and equal to the conductor
 * of the splitting field of p in Q(zeta_n). d>1 and nf>1 */
static GEN
FpX_factcyclo_newton_power(GEN N, GEN p, ulong m, int small)
{
  GEN Rs, H, T, F, pr, prs, pu, Data;
  long n = N[1], el = N[2], phin = N[4], g = N[5];
  long pmodn = umodiu(p, n), pmodel = umodiu(p, el);
  long d = Fl_order(pmodel, el-1, el), nf = phin/d;
  long r, s = 0, u = 1;

  if (m != 1) m = nf;
  for (pu = p; cmpiu(pu,d) <= 0; u++) pu = mulii(pu,p);  /* d<p^u, pu=p^u */
  H = Fl_powers(pmodn, d, n);
  T = galoissubcyclo(utoi(n), utoi(pmodn), 0, 0);
  F = gausspol(T, H, N, d, nf, g);
  r = QX_den_pval(F, p);
  Rs = ZpX_roots_all(T, p, nf, &s);
  if (DEBUGLEVEL >= 2) err_printf("(u,s,r)=(%ld,%ld,%ld)\n",u,s,r);
  pr = powiu(p, r); prs = powiu(p, r+s); /* Usually, r=0, s=1, pr=1, prs=p */
  F = r ? RgX_to_FpX(RgX_Rg_mul(F, pr), prs) : RgX_to_FpX(F, prs);
  Data = mkvec4(T, F, Rs, mkvecsmalln(6, d, nf, g, r, s, u));
  if (small && lgefint(pu) == 3)
    return Flx_factcyclo_newton_pre(Data, N, uel(p,2), m);
  else
    return FpX_factcyclo_newton_pre(Data, N, p, m);
}

static GEN
FpX_split(ulong n, GEN p, ulong m)
{
  ulong i, j;
  GEN v, C, vx, z = rootsof1u_Fp(n, p);
  if (m == 1) return mkvec(deg1pol_shallow(gen_1, Fp_neg(z,p), 0));
  v = cgetg(m+1, t_VEC); C = coprimes_zv(n); vx = Fp_powers(z, n-1, p);
  for (i = j = 1; i <= n; i++)
    if (C[i]) gel(v, j++) = deg1pol_shallow(gen_1, Fp_neg(gel(vx,i+1), p), 0);
  return gen_sort(v, (void*)cmpii, &gen_cmp_RgX);
}

/* n is a prime power prime to p. n is not necessarily equal to the
 * conductor of the splitting field of p in Q(zeta_n). */
static GEN
FpX_factcyclo_prime_power_i(long el, long e, GEN p, long m)
{
  GEN z = set_e0_e1(el, e, p), v;
  long n = z[1], e0 = z[2], e1 = z[3], phin = z[4], g = z[5];
  long d = z[6], f = z[7]; /* d and f for n=el^e0 */

  if (f == 1) v = mkvec(FpX_polcyclo(n, p));
  else if (d == 1) v = FpX_split(n, p, (m==1)? 1: f);
  else if (el == 2) v = FpX_factcyclo_gen(NULL, n, p, m); /* d==2 in this case */
  else if (!use_newton(d,f)) v = FpX_factcyclo_gen(NULL, n, p, m);
  else
  {
    GEN N = mkvecsmall5(n, el, e0, phin, g);
    v = FpX_factcyclo_newton_power(N, p, m, 0);
  }
  if (e1)
  {
    long i, l = lg(v), ele1 = upowuu(el, e1);
    for (i = 1; i < l; i++) gel(v, i) = RgX_inflate(gel(v, i), ele1);
  }
  return v;
}
static GEN
FpX_factcyclo_prime_power(long el, long e, GEN p, long m)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_factcyclo_prime_power_i(el, e, p, m));
}

static GEN
FpX_factcyclo_fact(ulong n, GEN p, ulong m, long ascent)
{
  GEN fa = factoru(n), EL = gel(fa, 1), E = gel(fa, 2), v1, v2;
  long l = lg(EL), i, n1, n2;

  n1 = ascent ? upowuu(EL[1], E[1]):upowuu(EL[l-1], E[l-1]);
  v1 = ascent ? FpX_factcyclo_prime_power(EL[1], E[1], p, m)
              : FpX_factcyclo_prime_power(EL[l-1], E[l-1], p, m);
  for (i = 2; i < l; i++)
  {
    n2 = ascent ? upowuu(EL[i], E[i]):upowuu(EL[l-i], E[l-i]);
    v2 = ascent ? FpX_factcyclo_prime_power(EL[i], E[i], p, m)
                : FpX_factcyclo_prime_power(EL[l-i], E[l-i], p, m);
    v1 = FpX_factcyclo_lift(n1, v1, n2, v2, p, m);
    n1 *= n2;
  }
  return v1;
}

static GEN
Flv_FlvV_factorback(GEN g, GEN x, ulong q)
{ pari_APPLY_ulong(Flv_factorback(g, gel(x,i), q)) }

/* return the structure and the generators of G/H. G=(Z/nZ)^, H=<p> */
static GEN
get_GH_gen(long n, long pmodn)
{
  GEN H = znstar_generate(n, mkvecsmall(pmodn)), gH = gel(H, 1);
  GEN G = znstar0(utoipos(n), 1), cycG = znstar_get_cyc(G);
  long i, lgH = lg(gH);
  GEN cycGH, gG, gGH, U, Ui;
  ulong expG;
  GEN P = cgetg(lgH, t_MAT);
  for (i = 1; i < lgH; i++) gel(P, i) = Zideallog(G, utoi(gH[i]));
  cycGH = ZV_to_nv(ZM_snf_group(hnfmodid(P, cycG), &U, &Ui));
  expG = itou(gel(cycG, 1));
  gG = ZV_to_Flv(znstar_get_gen(G), n);
  gGH = Flv_FlvV_factorback(gG, ZM_to_Flm(Ui, expG), n);
  return mkvec2(gGH, cycGH);
}

/* 1st output */
static void
header(GEN fn, long n, long d, long f, GEN p)
{
  GEN EL = gel(fn, 1), E = gel(fn, 2);
  long i, l = lg(EL)-1;
  err_printf("n=%lu=", n);
  for(i = 1; i <= l; i++)
  {
    long el = EL[i], e = E[i];
    err_printf("%ld", el);
    if (e > 1) err_printf("^%ld", e);
    if (i < l) err_printf("*");
  }
  err_printf(", p=%Ps, phi(%lu)=%lu*%lu\n", p, n, d, f);
  err_printf("(n,d,f) : (%ld,%ld,%ld) --> ",n,d,f);
}

static ulong
FpX_factcyclo_just_conductor_init(GEN *pData, ulong n, GEN p, ulong m)
{
  GEN fn = factoru(n), GH = NULL, GHgen = NULL;
  long phin = eulerphiu_fact(fn), pmodn = umodiu(p, n);
  long d = Fl_order(pmodn, phin, n), f = phin/d; /* d > 1 */
  ulong action = set_action(fn, p, d, f);
  if (action & GENERAL)
  {
    GEN H = znstar_generate(n, mkvecsmall(pmodn));
    GH = znstar_cosets(n, phin, H); /* representatives of G/H */
    if (action & (NEWTON_GENERAL_NEW | NEWTON_GENERAL))
      GHgen = get_GH_gen(n, pmodn);  /* gen and order of G/H */
  }
  else if (action & NEWTON_POWER);
  else if (action & (NEWTON_GENERAL_NEW | NEWTON_GENERAL))
  {
    GEN H = znstar_generate(n, mkvecsmall(pmodn));
    GH = znstar_cosets(n, phin, H); /* representatives of G/H */
    GHgen = get_GH_gen(n, pmodn);  /* gen and order of G/H */
  }
  *pData = mkvec5(GHgen, GH, fn, p, mkvecsmall4(n, d, f, m));
  if (DEBUGLEVEL >= 1)
  {
    err_printf("(%ld,%ld,%ld)  action=%ld\n", n, d, f, action);
    if (GHgen)
    {
      GEN cycGH = gel(GHgen,2), gGH = gel(GHgen,1);
      err_printf("G(K/Q)=%Ps gen=%Ps\n", zv_to_ZV(cycGH), zv_to_ZV(gGH));
    }
  }
  return action;
}

static GEN
FpX_factcyclo_just_conductor(ulong n, GEN p, ulong m)
{
  GEN Data;
  ulong action = FpX_factcyclo_just_conductor_init(&Data, n, p, m);
  if (action & GENERAL)
    return FpX_factcyclo_gen(gel(Data,2), n, p, m);
  else if (action & NEWTON_POWER)
  {
    GEN fn = gel(Data,3);
    return FpX_factcyclo_prime_power_i(ucoeff(fn,1,1), ucoeff(fn,1,2), p, m);
  }
  else if (action & NEWTON_GENERAL)
    return FpX_factcyclo_newton_general(Data);
  else if (action & NEWTON_GENERAL_NEW)
    return FpX_factcyclo_newton_general_new3(Data);
  else
    return FpX_factcyclo_fact(n, p, m, action & ASCENT);
}

static GEN
FpX_factcyclo_i(ulong n, GEN p, long fl)
{
  GEN fn = factoru(n), z;
  long phin = eulerphiu_fact(fn), pmodn = umodiu(p, n);
  ulong d = Fl_order(pmodn, phin, n), f = phin/d, fK;

  if (DEBUGLEVEL >= 1) header(fn, n, d, f, p);
  if (f == 1) { z = FpX_polcyclo(n, p); return fl? z: mkvec(z); }
  else if (d == 1) /* p=1 (mod n), zeta_n in Z_p */
  { z = FpX_split(n, p, fl? 1: f); return fl? gel(z,1): z; }
  fK = znstar_conductor(znstar_generate(n, mkvecsmall(pmodn)));
  if (fK != n && umodiu(p, fK) == 1)
    z = FpX_split(fK, p, fl? 1: f);
  else
    z = FpX_factcyclo_just_conductor(fK, p, fl? 1: f);
  if (n > fK)
  {
    ulong i, l = lg(z);
    GEN vP = const_vec(n, gen_0);
    for (i = 1; i < l; i++)
      gel(z, i) = FpX_conductor_lift(gel(z, i), p, n, fK, vP);
  }
  return fl? gel(z,1): gen_sort(z,(void*)cmpii, &gen_cmp_RgX);
}

GEN
FpX_factcyclo(ulong n, GEN p, ulong m)
{ pari_sp av = avma; return gerepilecopy(av, FpX_factcyclo_i(n, p, m)); }

/*  Data = [H, GH, i_t, d0, kT, [n, d, f, n_T, mitk]]
 *  Data2 = [vT, polcyclo_n, [p, pr, pu, pru]] */
static GEN
Flx_pol_newton_general(GEN Data, GEN Data2, ulong x)
{
  GEN i_t = gel(Data, 3), kT = gel(Data, 5);
  GEN N = gel(Data, 6), N2 = gel(Data2, 3);
  long k, d = N[2], n_T = N[4], mitk = N[5];
  GEN vT = gel(Data2, 1), polcyclo_n = gel(Data2, 2);
  long p = N2[1], pr = N2[2], pu = N2[3], pru = N2[4];
  GEN S = cgetg(2+d, t_VECSMALL), R = cgetg(1+mitk, t_VECSMALL), P;

  for (k = 1; k <= n_T; k++) R[kT[k]] = Flx_eval(gel(vT, kT[k]), x, pru)/pr;
  S[1] = d;
  for (k = 1; k <= d; k++) S[1+k] = R[i_t[k]];
  P = Flx_red(Flx_fromNewton(Flv_to_Flx(S, 0), pu), p);
  if (degpol(Flx_rem(polcyclo_n, P, p)) >= 0)
    pari_err_BUG("Flx_pol_newton_general");
  return P;
}

/* n is any integer prime to p, but must be equal to the conductor
 * of the splitting field of p in Q(zeta_n).
 * GH=G/H={g_1, ... ,g_f}
 * Data = [GHgen, GH, fn, p, [n, d, f, m]] */
static GEN
Flx_factcyclo_newton_general(GEN Data)
{
  GEN GH = gel(Data, 2), fn = gel(Data, 3), p = gel(Data, 4);
  ulong up = p[2], n = mael(Data, 5, 1), pmodn = up%n;
  long d = mael(Data, 5, 2), f = mael(Data, 5, 3), m = mael(Data, 5, 4);
  long i, k, n_T, mitk, r, s = 0, u = 1;
  GEN vT, kT, H, i_t, T, d0d1, Data2, Data3, R, Rs, pr, pu, pru, pols;
  pari_timer ti;

  if (m != 1) m = f;
  pols = cgetg(1+m, t_VEC);
  for (pu = p; cmpiu(pu,d) <= 0; u++) pu = muliu(pu, up);  /* d<pu, pu=p^u */

  H = Fl_powers(pmodn, d-1, n); /* H=<p> */
  i_t = get_i_t(n, pmodn); /* i_t[1+i]=k ==> t_i=t_k */
  kT = get_kT(i_t, d); n_T = lg(kT)-1; mitk = kT[n_T];
  if (DEBUGLEVEL == 2) err_printf("kT=%Ps %ld elements\n",kT,n_T);
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  T = galoissubcyclo(utoi(n), utoi(pmodn), 0, 0);
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "galoissubcyclo");
  d0d1 = get_d0_d1(T, gel(fn,1)); /* d0*T_k(x) is in Z[x] */
  Data2 = mkvecn(6, H, GH, i_t, d0d1, kT, mkvecsmalln(5, n, d, f, n_T, mitk));
  vT = get_vT(Data2, 0);
  if (DEBUGLEVEL == 4) err_printf("vT=%Ps\n",vT);
  r = QXV_den_pval(vT, kT, p);
  Rs = ZpX_roots_all(T, p, f, &s);
  if (DEBUGLEVEL >= 2) err_printf("(u,s,r)=(%ld,%ld,%ld)\n",u,s,r);
  if (r+u < s) pari_err_BUG("Flx_factcyclo_newton_general, T(x) is not separable mod p^(r+u)");
  /* R and vT are mod p^(r+u) */
  R = (r+u==s) ? Rs : ZV_sort_shallow(ZX_Zp_liftroots(T, Rs, p, s, r+u));
  pr = powiu(p, r); pru = powiu(p, r+u); /* Usually, r=0, s=1, pr=1, pru=p */
  if (lgefint(pru) > 3)  /* ULONG_MAX < p^(r+u), probably not occur */
  {
    GEN polcyclo_n;
    for (k = 1; k <= n_T; k++)
    {
      long itk = kT[k];
      gel(vT, itk) = r ? RgX_to_FpX(RgX_Rg_mul(gel(vT, itk), pr), pru):
                         RgX_to_FpX(gel(vT, itk), pru);
    }
    polcyclo_n = FpX_polcyclo(n, p);
    Data3 = mkvecn(6, vT, polcyclo_n, p, pr, pu, pru);
    for (i = 1; i <= m; i++)
      gel(pols, i) = ZX_to_nx(FpX_pol_newton_general(Data2, Data3, gel(R, i)));
    return pols;
  }
  else
  {
    ulong upr = itou(pr), upru = itou(pru), upu = itou(pu);
    GEN polcyclo_n;
    for (k = 1; k <= n_T; k++)
    {
      long itk = kT[k];
      gel(vT, itk) = r ? RgX_to_Flx(RgX_muls(gel(vT, itk), upr), upru):
                         RgX_to_Flx(gel(vT, itk), upru);
    }
    polcyclo_n = Flx_polcyclo(n, up);
    Data3 = mkvec3(vT, polcyclo_n, mkvecsmall4(up, upr, upu, upru));
    R = ZV_to_nv(R);
    if (DEBUGLEVEL >= 6) timer_start(&ti);
    for (i = 1; i <= m; i++)
      gel(pols, i) = Flx_pol_newton_general(Data2, Data3, R[i]);
    if (DEBUGLEVEL >= 6) timer_printf(&ti, "Flx_pol_newton_general");
    return pols;
  }
}

/*  Data=[vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
 *       [n, r, s, n_t, mitk, d], div, polcyclo_n] */
static GEN
Flx_pol_newton_general_new3(GEN Data, long k)
{
  GEN i_t = gel(Data, 5), p = gel(Data, 7), pu = gel(Data, 8);
  GEN prs = gel(Data, 10), polcyclo_n = gel(Data, 13);
  long i, d = mael(Data, 11, 6);
  GEN S = cgetg(2+d, t_VECSMALL), v_t_p, P;

  v_t_p = (lgefint(prs)>3) ? ZV_to_nv(Fp_mk_v_t_p3(Data, k))
                           : Fl_mk_v_t_p3(Data, k);
  if (DEBUGLEVEL == 3) err_printf("v_t_p=%Ps\n",v_t_p);
  S[1] = d;
  for (i = 1; i <= d; i++) S[1+i] = v_t_p[i_t[i]];
  P = Flx_red(Flx_fromNewton(Flv_to_Flx(S, 0), pu[2]), p[2]);
  if (degpol(Flx_rem(polcyclo_n, P, p[2])) >= 0)
    pari_err_BUG("Flx_pol_newton_general_new3 failed");
  return P;
}

/* Data = [GHgen, GH, fn, p, [n, d, f, m]] */
static GEN
Flx_factcyclo_newton_general_new3(GEN Data)
{
  GEN p = gel(Data, 4), Data2, pu, pols;
  long i, n = mael(Data, 5, 1), f = mael(Data, 5, 3), m = mael(Data, 5, 4);
  ulong up = p[2];
  pari_timer ti;

  if (m != 1) m = f;
  pols = cgetg(1+m, t_VEC);
  Data2 = newton_general_new_pre3(Data); pu = gel(Data2, 8);
  /* Data2 = [vT, gGH, Rs, Rrs, i_t, kt, p, pu, pr, prs,
              [n, r, s, n_t, mitk, d], div] */

  if (lgefint(pu) > 3)  /* ULONG_MAX < p^u, probably not occur */
  {
    Data2 = vec_append(Data2, FpX_polcyclo(n, p));
    for (i = 1; i <= m; i++)
      gel(pols, i) = ZX_to_nx(FpX_pol_newton_general_new3(Data2, i));
    return pols;
  }
  else
  {
    Data2 = vec_append(Data2, Flx_polcyclo(n, up));
    if (DEBUGLEVEL >= 6) timer_start(&ti);
    for (i = 1; i <= m; i++)
      gel(pols, i) = Flx_pol_newton_general_new3(Data2, i);
    if (DEBUGLEVEL >= 6) timer_printf(&ti, "Flx_pol_newton_general_new3");
    return pols;
  }
}

/* return normalized z(-x) */
static GEN
Flx_1st_lift_2(GEN z, ulong p)
{
  long i, r = lg(z);
  GEN x = cgetg(r, t_VECSMALL);
  for (i = 2; i<r; i++) x[i] = (i&1) ? Fl_neg(z[i], p) : z[i];
  return (r&1) ? x : Flx_neg(x, p);
}

/* el does not divides e.
 * construct Phi_{e*el}(x) from Phi_e(x). */
static GEN
Flx_1st_lift(GEN z, ulong p, ulong e, ulong el, GEN vP)
{
   GEN P, z2, z3;
   if (isintzero(gel(vP, e))) gel(vP, e) = Flx_polcyclo(e, p);
   P = gel(vP, e);
   z2 = Flx_inflate(z, el);
   z3 = Flx_normalize(Flx_gcd(P, z2, p), p);
   return Flx_div(z2, z3, p);
}

static GEN
Flx_lift(GEN z, ulong p, ulong e, ulong el, ulong r, ulong s, GEN vP)
{
  if (s == 0) z = (el==2) ? Flx_1st_lift_2(z, p) : Flx_1st_lift(z, p, e, el, vP);
  if (s > 0) z = Flx_inflate(z, upowuu(el, r-s));
  else if (r >= 2) z = Flx_inflate(z, upowuu(el, r-1));
  return z;
}

/* e is the conductor of the splitting field of p in Q(zeta_n) */
static GEN
Flx_conductor_lift(GEN z, ulong p, ulong n, ulong e, GEN vP)
{
  GEN fn = factoru(n), EL = gel(fn, 1), En = gel(fn, 2);
  long i, r = lg(EL), new_e = e;

  for (i = 1; i < r; i++)
  {
    long el = EL[i], en = En[i], ee = u_lval(e, el);
    if (ee < en)
    {
      z = Flx_lift(z, p, new_e, el, en, ee, vP);
      new_e *= upowuu(el, en-ee);
    }
  }
  return z;
}

/* R0 is mod p^u, d < p^u */
static GEN
Flx_pol_newton(long j, GEN Data, GEN N, long d, long f, ulong p)
{
  pari_sp av = avma;
  long el = N[2], e = N[3], i;
  GEN R0 = gel(Data, 1), E = gel(Data, 2), D3 = gel(Data, 3);
  ulong u = D3[3], pu = upowuu(p, u);
  GEN S = cgetg(2+d, t_VECSMALL), R = cgetg(1+f, t_VECSMALL), P;

  for (i = 1; i <= f; i++) R[i] = R0[1+(i+j)%f];
  S[1] = d;
  for (i = 1; i <= d; i++) S[1+i] = R[E[i]];
  P = Flx_red(Flx_fromNewton(Flv_to_Flx(S, 0), pu), p);
  if (degpol(Flx_rem(Flx_polcyclo_el_e(el, e), P, p)) >= 0)
    pari_err_BUG("Flx_pol_newton");
  return gerepilecopy(av, P);
}

/* Data = [T, F, Rs, [d, nf, g, r, s, u]], nf>1 */
static GEN
Flx_factcyclo_newton_pre(GEN Data, GEN N, ulong p, ulong m)
{
  GEN T = gel(Data, 1), F = gel(Data, 2), Rs = gel(Data, 3), D4 = gel(Data, 4);
  long d = D4[1], nf = D4[2], g = D4[3], r = D4[4], s = D4[5], u = D4[6];
  GEN pols, E, R, p0 = utoi(p), Data3;
  ulong i, n = N[1], pmodn = p%n;
  pari_timer ti;

  if (m != 1) m = nf;
  pols = cgetg(1+m, t_VEC);
  E = set_E(pmodn, n, d, nf, g);
  R = set_R(T, F, Rs, p0, nf, r, s, u);
  R = ZV_to_nv(R);
  Data3 = mkvec3(R, E, mkvecsmall3(r, s, u));
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  for (i = 1; i <= m; i++) gel(pols, i) = Flx_pol_newton(i, Data3, N, d, nf, p);
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "Flx_pol_newton");
  return pols;
}

/* gcd(n1,n2)=1, e = gcd(d1,d2).
 * phi(n1) = d1*nf1, phi(n2) = d2*nf2.
 * d = lcm(d1,d2) = d1*d2/e, nf = phi(n1)*phi(n2)/d = nf1*nf2*e. */
static GEN
Flx_factcyclo_lift(long n1, GEN v1, long n2, GEN v2, long p, long m)
{
  pari_sp av = avma;
  long d1 = degpol(gel(v1, 1)), lv1 = lg(v1), nf1 = eulerphiu(n1)/d1;
  long d2 = degpol(gel(v2, 1)), lv2 = lg(v2), nf2 = eulerphiu(n2)/d2;
  long e = ugcd(d1, d2), nf = nf1*nf2*e, need_factor = (e!=1);
  long i, j, k = 0;
  GEN v, z = NULL;
  pari_timer ti;

  if (DEBUGLEVEL >= 6) timer_start(&ti);
  if (m != 1) m = nf;
  v = cgetg(1+m, t_VEC);
  if (m == 1)
  {
    GEN x1 = gel(v1, 1), x2 = gel(v2, 1);
    z = Flx_gcd(Flx_inflate(x1, n2), Flx_inflate(x2, n1), p);
    z = Flx_normalize(z, p);  /* Flx_gcd sometimes returns non-monic */
    gel(v, 1) = (!need_factor)? z : gmael(Flx_factor(z, p), 1, 1);
  }
  else
    for (i = 1; i < lv1; i++)
      for (j = 1; j < lv2; j++)
      {
        GEN x1 = gel(v1, i), x2 = gel(v2, j);
        z = Flx_gcd(Flx_inflate(x1, n2), Flx_inflate(x2, n1), p);
        z = Flx_normalize(z, p);  /* needed */
        if (!need_factor) gel(v, ++k) = z;
        else
        {
          GEN z1 = gel(Flx_factor(z, p), 1);
          long i, l = lg(z1);
          for (i = 1; i < l; i++) gel(v, ++k) = gel(z1, i);
        }
      }
  if (DEBUGLEVEL >= 6)
    timer_printf(&ti, "Flx_factcyclo_lift (%ld,%ld)*(%ld,%ld)-->(%ld,%ld)-->(%ld,%ld)",
        d1, nf1, d2, nf2, degpol(z), nf1*nf2, d1*d2/e, nf);
  return gerepilecopy(av, v);
}

/* factor polcyclo(n) mod p based on an idea of Bill Allombert; d>1 and nf>1 */
static GEN
Flx_factcyclo_gen(GEN GH, ulong n, ulong p, ulong m)
{
  GEN fu = factoru(n), fa = zm_to_ZM(fu), p0 = utoi(p);
  GEN T, X, pd_n, v, pols;
  ulong i, j, pmodn = p%n, phin = eulerphiu_fact(fu);
  ulong d = Fl_order(pmodn, phin, n), nf = phin/d;
  pari_timer ti;

  if (m != 1) m = nf;
  if (m != 1 && !GH) /* Flx_factcyclo_fact is used */
  {
    GEN H = znstar_generate(n, mkvecsmall(pmodn));
    GH = znstar_cosets(n, phin, H); /* representatives of G/H */
  }

  pols = cgetg(1+m, t_VEC);
  v = cgetg(1+d, t_VEC);
  pd_n = diviuexact(subis(powiu(p0, d), 1), n); /* (p^d-1)/n */
  T = ZX_to_Flx(init_Fq(p0, d, evalvarn(1)), p);
  random_Flx(degpol(T), T[1], p);  /* skip 1st one */
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  do X = Flxq_pow(random_Flx(degpol(T), T[1], p), pd_n, T, p);
  while (lg(X)<3 || equaliu(Flxq_order(X, fa, T, p), n)==0); /* find zeta_n */
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "find X");

  if (m == 1)
  {
    for (j = 1; j <= d; j++)
    {
      gel(v, j) = polx_FlxX(0, 1);
      gmael(v, j, 2) = Flx_neg(X, p);
      if (j < d) X = Flxq_powu(X, p, T, p);
    }
    gel(pols, 1) = FlxX_to_Flx(FlxqXV_prod(v, T, p));
  }
  else
  {
    GEN vX, vp;
    if (DEBUGLEVEL >= 6) timer_start(&ti);
    vX = Flxq_powers(X, n, T, p)+1;
    vp = Fl_powers(pmodn, d, n);
    for (i = 1; i <= m; i++)
    {
      for (j = 1; j <= d; j++)
      {
        gel(v, j) = polx_FlxX(0, 1);
        gmael(v, j, 2) = Flx_neg(gel(vX, Fl_mul(GH[i], vp[j], n)), p);
      }
      gel(pols, i) = FlxX_to_Flx(FlxqXV_prod(v, T, p));
    }
    if (DEBUGLEVEL >= 6) timer_printf(&ti, "FlxqXV_prod");
  }
  return pols;
}

static int
cmpGuGu(GEN a, GEN b) { return (ulong)a < (ulong)b? -1: (a == b? 0: 1); }

/* p=1 (mod n). If m!=1, then m=phi(n) */
static GEN
Flx_split(ulong n, ulong p, ulong m)
{
  ulong i, j, z = rootsof1_Fl(n, p);
  GEN v, C, vx;
  if (m == 1) return mkvec(mkvecsmall3(0, Fl_neg(z,p), 1));
  v = cgetg(m+1, t_VEC); C = coprimes_zv(n); vx = Fl_powers(z, n-1, p);
  for (i = j = 1; i <= n; i++)
    if (C[i]) gel(v, j++) = mkvecsmall3(0, Fl_neg(vx[i+1], p), 1);
  return gen_sort(v, (void*)cmpGuGu, &gen_cmp_RgX);
}

/* d==1 or f==1 occurs */
static GEN
Flx_factcyclo_prime_power_i(long el, long e, long p, long m)
{
  GEN p0 = utoipos(p), z = set_e0_e1(el, e, p0), v;
  long n = z[1], e0 = z[2], e1 = z[3], phin = z[4], g = z[5];
  long d = z[6], f = z[7]; /* d and f for n=el^e0 */

  if (f == 1) v = mkvec(Flx_polcyclo(n, p));
  else if (d == 1) v = Flx_split(n, p, (m==1)?1:f);
  else if (el == 2) v = Flx_factcyclo_gen(NULL, n, p, m);/* d==2 in this case */
  else if (!use_newton(d, f)) v = Flx_factcyclo_gen(NULL, n, p, m);
  else
  {
    GEN N = mkvecsmall5(n, el, e0, phin, g);
    v = FpX_factcyclo_newton_power(N, p0, m, 1);
    if (typ(gel(v,1)) == t_POL)
    { /* ZX: convert to Flx */
      long i, l = lg(v);
      for (i = 1; i < l; i++) gel(v,i) = ZX_to_nx(gel(v,i));
    }
  }
  if (e1)
  {
    long i, l = lg(v), ele1 = upowuu(el, e1);
    for (i = 1; i < l; i++) gel(v, i) = Flx_inflate(gel(v, i), ele1);
  }
  return v;
}
static GEN
Flx_factcyclo_prime_power(long el, long e, long p, long m)
{
  pari_sp av = avma;
  return gerepilecopy(av, Flx_factcyclo_prime_power_i(el, e, p, m));
}

static GEN
Flx_factcyclo_fact(ulong n, ulong p, ulong m, long ascent)
{
  GEN fa = factoru(n), EL = gel(fa, 1), E = gel(fa, 2), v1, v2;
  long l = lg(EL), i, n1, n2;

  n1 = ascent ? upowuu(EL[1], E[1]):upowuu(EL[l-1], E[l-1]);
  v1 = ascent ? Flx_factcyclo_prime_power(EL[1], E[1], p, m)
              : Flx_factcyclo_prime_power(EL[l-1], E[l-1], p, m);
  for (i = 2; i < l; i++)
  {
    n2 = ascent ? upowuu(EL[i], E[i]):upowuu(EL[l-i], E[l-i]);
    v2 = ascent ? Flx_factcyclo_prime_power(EL[i], E[i], p, m)
                : Flx_factcyclo_prime_power(EL[l-i], E[l-i], p, m);
    v1 = Flx_factcyclo_lift(n1, v1, n2, v2, p, m);
    n1 *= n2;
  }
  return v1;
}

static GEN
Flx_factcyclo_just_conductor(ulong n, ulong p, ulong m)
{
  GEN Data;
  ulong action = FpX_factcyclo_just_conductor_init(&Data, n, utoipos(p), m);
  if (action & GENERAL)
    return Flx_factcyclo_gen(gel(Data,2), n, p, m);
  else if (action & NEWTON_POWER)
  {
    GEN fn = gel(Data,3);
    return Flx_factcyclo_prime_power_i(ucoeff(fn,1,1), ucoeff(fn,1,2), p, m);
  }
  else if (action & NEWTON_GENERAL)
    return Flx_factcyclo_newton_general(Data);
  else if (action & NEWTON_GENERAL_NEW)
    return Flx_factcyclo_newton_general_new3(Data);
  else
    return Flx_factcyclo_fact(n, p, m, action & ASCENT);
}

static GEN
Flx_factcyclo_i(ulong n, ulong p, ulong fl)
{
  GEN fn = factoru(n), z;
  ulong phin = eulerphiu_fact(fn), pmodn = p%n;
  ulong d = Fl_order(pmodn, phin, n), f = phin/d, fK;

  if (DEBUGLEVEL >= 1) header(fn, n, d, f, utoi(p));
  if (f == 1) { z = Flx_polcyclo(n, p); return fl? z: mkvec(z); }
  if (d == 1) /* p=1 (mod n), zeta_n in Z_p */
  { z = Flx_split(n, p, fl? 1: f); return fl? gel(z,1): z; }
  fK = znstar_conductor(znstar_generate(n, mkvecsmall(pmodn)));
  if (fK != n && p % fK == 1)
    z = Flx_split(fK, p, fl? 1: f);
  else
    z = Flx_factcyclo_just_conductor(fK, p, fl? 1: f);
  if (n > fK)
  {
    long i, l = lg(z);
    GEN vP = const_vec(n, gen_0);
    for (i = 1; i < l; i++)
      gel(z, i) = Flx_conductor_lift(gel(z, i), p, n, fK, vP);
  }
  return fl? gel(z,1): gen_sort(z,(void*)cmpGuGu, &gen_cmp_RgX);
}

GEN
Flx_factcyclo(ulong n, ulong p, ulong m)
{ pari_sp av = avma; return gerepilecopy(av, Flx_factcyclo_i(n, p, m)); }

GEN
factormodcyclo(long n, GEN p, long fl, long v)
{
  const char *fun = "factormodcyclo";
  pari_sp av = avma;
  long i, l;
  GEN z;
  if (v < 0) v = 0;
  if (fl < 0 || fl > 1) pari_err_FLAG(fun);
  if (n <= 0) pari_err_DOMAIN(fun, "n", "<=", gen_0, stoi(n));
  if (typ(p) != t_INT) pari_err_TYPE(fun, p);
  if (dvdui(n, p)) pari_err_COPRIME(fun, stoi(n), p);
  if (fl)
  {
    if (lgefint(p) == 3)
      z = Flx_to_ZX(Flx_factcyclo_i(n, p[2], 1));
    else
      z = FpX_factcyclo_i(n, p, 1);
    setvarn(z, v);
    return gerepileupto(av, FpX_to_mod(z, p));
  }
  else
  {
    if (lgefint(p) == 3)
      z = FlxC_to_ZXC(Flx_factcyclo_i(n, p[2], 0));
    else
      z = FpX_factcyclo_i(n, p, 0);
    l = lg(z); for (i = 1; i < l; i++) setvarn(gel(z, i), v);
    return gerepileupto(av, FpXC_to_mod(z, p));
  }
}
