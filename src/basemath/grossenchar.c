/* Copyright (C) 2000  The PARI group.

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

#define DEBUGLEVEL DEBUGLEVEL_gchar

static GEN gchari_eval(GEN gc, GEN chi, GEN x, long flag, GEN logchi, GEN logx, GEN s0, long prec);

/*********************************************************************/
/**                                                                 **/
/**                    HECKE GROSSENCHARACTERS                      **/
/**         contributed by Pascal Molin and Aurel Page (2022)       **/
/**                                                                 **/
/*********************************************************************/

/*
  characters can be represented by:
   - t_COL of coordinates on the snf basis (mostly for gp use): prefix gchar_
   - t_VEC of coordinates on the internal basis: prefix gchari_
   - t_VEC of R/Z components (logs): prefix gcharlog_

   see gchar_internal for SNF -> internal
   and gchari_log for internal -> R/Z components
*/

/*
localstar: represent (Z_F/m)^* . {+-1}^r + generators of U_{i-1}(p)/U_i
structure:
- [ sprk for p^k | m ] , size np
- [ Ufil_p for p | m ], size np
- m_oo, t_VECSMALL of size nci <= r1 (indices of real places)

where Ufil_p = [ Mat([gen[j], t_COL of size ncp]_j) ]_{1<=i<=k}
*/

#define GC_LENGTH   11
#define LOCS_LENGTH 4

static GEN
compute_Lcyc(GEN Lsprk, GEN moo)
{
  long i, l = lg(Lsprk), len = l+lg(moo)-1;
  GEN Lcyc = cgetg(len,t_VEC);
  for (i = 1; i < l; i++)   gel(Lcyc,i) = sprk_get_cyc(gel(Lsprk,i));
  for (     ; i < len; i++) gel(Lcyc,i) = mkvec(gen_2);
  return Lcyc;
}

/* true nf; modulus = [ factor(m_f), m_oo ] */
static GEN
localstar(GEN nf, GEN famod, GEN moo)
{
  GEN Lcyc, cyc, Lsprk, Lgenfil, P = gel(famod,1), E = gel(famod,2);
  long i, l = lg(P);

  Lsprk = cgetg(l, t_VEC);
  Lgenfil = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    long n, e, k = itos(gel(E,i));
    GEN v, sprk = log_prk_init(nf, gel(P,i), k, NULL);
    gel(Lsprk,i) = sprk; n = lg(sprk_get_cyc(sprk))-1;
    gel(Lgenfil,i) = v = cgetg(k+1, t_VEC);
    /* log on sprk of generators of U_{e-1}/U_e(pr) */
    gel(v, 1) = col_ei(n, 1);
    for (e = 2; e <= k; e++) gel(v, e) = sprk_log_gen_pr2(nf, sprk, e);
  }
  Lcyc = compute_Lcyc(Lsprk, moo);
  if (lg(Lcyc) > 1)
    cyc = shallowconcat1(Lcyc);
  else
    cyc = cgetg(1, t_VEC);
  return mkvec4(cyc, Lsprk, Lgenfil, mkvec2(famod,moo));
}

/* (nv * log|x^sigma|/norm, arg(x^sigma))/2*Pi
 * substract norm so that we project to the hyperplane
 * H : sum n_s x_s = 0 */
GEN
nfembedlog(GEN bnf, GEN x, long prec)
{
  pari_sp av = avma;
  GEN logs, nf, cxlogs;
  long k, r1, r2, n;

  nf = bnf_get_nf(bnf);
  nf_get_sign(nf, &r1, &r2);
  cxlogs = nf_cxlog(nf, x, prec);
  if (!cxlogs) return NULL;
  cxlogs = nf_cxlog_normalize(nf, cxlogs, prec);
  if (!cxlogs) return NULL;
  n = r1 + 2*r2; logs = cgetg(n+1,t_COL);
  for (k = 1; k <= r1+r2; k++) gel(logs,k) = real_i(gel(cxlogs,k));
  for (     ; k <= n; k++) gel(logs,k) = gmul2n(imag_i(gel(cxlogs,k-r2)), -1);
  return gerepileupto(av, gdiv(logs, Pi2n(1,prec)));
}

static GEN
gchar_Sval(GEN nf, GEN S, GEN x)
{
  GEN res = cgetg(lg(S),t_COL);
  long i;
  if (typ(x)==t_MAT)
    for (i=1; i<lg(S); i++)
      gel(res, i) = famat_nfvalrem(nf, x, gel(S,i), NULL);
  else
    for (i=1; i<lg(S); i++)
      gel(res, i) = stoi(nfval(nf, x, gel(S,i)));
  return res;
}

/* log_prk(x*pi_pr^{-v_pr(x)}), sign(sigma(x)) */
GEN
gchar_logm(GEN nf, GEN locs, GEN x)
{
  pari_sp av = avma;
  GEN moo, loga, Lsprk = locs_get_Lsprk(locs);
  long i, l = lg(Lsprk);

  nf = checknf(nf);
  moo = locs_get_m_infty(locs);
  if (typ(x) != t_MAT) x = to_famat_shallow(x, gen_1);
  loga = cgetg(l+1, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN sprk = gel(Lsprk, i), pr = sprk_get_pr(sprk);
    GEN g = vec_append(gel(x,1), pr_get_gen(pr));
    GEN v = famat_nfvalrem(nf, x, pr, NULL);
    GEN e = vec_append(gel(x,2), gneg(v));
    gel(loga, i) = famat_zlog_pr(nf, g, e, sprk, NULL);
  }
  gel(loga, i) = zc_to_ZC( nfsign_arch(nf, x, moo) );
  return gerepilecopy(av, shallowconcat1(loga));
}

static GEN
gchar_nflog(GEN bnf, GEN zm, GEN S, GEN x, long prec)
{
  GEN emb = nfembedlog(bnf,x,prec);
  if (!emb) return NULL;
  return shallowconcat1(mkvec3(gchar_Sval(bnf,S,x),gchar_logm(bnf,zm,x),emb));
}

static GEN
matvaluations(GEN bnf, GEN S, GEN g)
{
  long i, j, li = lg(S), lj = lg(g);
  GEN m = cgetg(lj, t_MAT);
  for (j = 1; j < lj; j++)
  {
    GEN c = cgetg(li, t_COL); gel(m,j) = c;
    for (i = 1; i < li; i++)
      gel(c,i) = stoi(idealval(bnf, gel(g,j), gel(S,i)));
  }
  return m;
}

/*******************************************************************/
/*                                                                 */
/*                        CHARACTER GROUP                          */
/*                                                                 */
/*******************************************************************/

/* embed v in vector of length size, shifted to the right */
static GEN
embedcol(GEN v, long size, long shift)
{
  long k;
  GEN w = zerocol(size);
  for (k = 1; k < lg(v); k++) gel(w, shift+k) = gel(v,k);
  return w;
}

/* write exact rationals from real approximation, in place. */
static void
shallow_clean_rat(GEN v, long k0, long k1, GEN den, long prec)
{
  long k, e;
  for (k = k0; k <= k1; k++)
  {
    GEN t = gel(v,k);
    if (den) t = gmul(t, den);
    t = grndtoi(t, &e);
    if (DEBUGLEVEL>1) err_printf("[%Ps*%Ps=%Ps..e=%ld|prec=%ld]\n",
                                 gel(v,k), den? den: gen_1, t, e, prec);
    if (e > -10)
      pari_err_BUG("gcharinit, non rational entry"); /*LCOV_EXCL_LINE*/
    gel(v, k) = den? gdiv(t, den): t;
  }
}

/* FIXME: export ? */
static GEN
rowreverse(GEN m)
{
  long i, l;
  GEN v;
  if (lg(m) == 1) return m;
  l = lgcols(m); v = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) v[i] = l - i;
  return rowpermute(m, v);
}

/* lower-left hnf on subblock m[r0+1..r0+nr, c0+1..c0+nc]
 * return base change matrix U */
static GEN
hnf_block(GEN m, long r0, long nr, long c0, long nc)
{
  GEN block, u, uu;
  long nm = lg(m)-1, k;
  pari_sp av = avma;

  block = matslice(m, r0+1, r0+nr, c0+1, c0+nc);
  block = Q_remove_denom(block, NULL);
  block = rowreverse(block);

  (void)ZM_hnfall(block, &u, 1);
  vecreverse_inplace(u);
  uu = matid(nm);
  /* embed in matid */
  for (k = 1; k <= nc; k++)
    gel(uu,c0+k) = embedcol(gel(u,k),nm,c0);
  return gerepilecopy(av, uu);
}

static GEN
lll_block(GEN m, long r0, long nr, long c0, long nc)
{
  GEN block, u, uu;
  long nm = lg(m)-1, k;
  pari_sp av = avma;

  block = matslice(m, r0+1, r0+nr, c0+1, c0+nc);
  u = lll(block); vecreverse_inplace(u);
  if (lg(u) <= nc) return NULL;
  uu = matid(nm); /* embed in matid */
  for (k = 1; k <= nc; k++) gel(uu,c0+k) = embedcol(gel(u,k),nm,c0);
  return gerepilecopy(av, uu);
}

/* insert a column at index i, no copy */
static GEN
shallowmatinsert(GEN m, GEN x, long i)
{
  long k, n = lg(m);
  GEN mm = cgetg(n+1,t_MAT);
  for (k=1; k < i; k++) gel(mm, k) = gel(m, k);
  gel(mm, i) = x;
  for (k=i; k < n; k++) gel(mm, k+1) = gel(m, k);
  return mm;
}

static GEN
vec_v0(long n, long n0, long r1, long r2)
{
  long k;
  GEN C = zerocol(n);
  for (k = 1; k <= r1; k++) gel(C, n0++) = gen_1;
  for (k = 1; k <= r2; k++) gel(C, n0++) = gen_2;
  return C;
}

/* select cm embeddings; return a matrix */
static GEN
cm_select(GEN nf, GEN cm, long prec)
{
  GEN emb, keys, v, m_sel, imag_emb;
  long nc, d_cm, r_cm, c, i, j, r2 = nf_get_r2(nf);
  pari_sp av;

  d_cm = degpol(gel(cm, 1)); /* degree of the cm field; even */
  nc = d_cm / 2; /* nb of clusters */
  r_cm = nf_get_degree(nf) / d_cm; /* nb by cluster; nc * r_cm = r2 */
  m_sel = zeromatcopy(nc, r2); /* selection matrix */
  av = avma;
  /* group complex embeddings */
  emb = nfeltembed(nf, gel(cm, 2), NULL, prec);
  /* sort */
  imag_emb = imag_i(emb);
  keys = gadd(gmul(mppi(prec), real_i(emb)), gabs(imag_emb, prec));
  v = indexsort(keys);

  for (j = c = 1; c <= nc; c++)
  {
    int ref = gsigne(gel(imag_emb, v[j]));
    gcoeff(m_sel, c, v[j]) = gen_1;
    j++;
    for (i = 2; i <= r_cm; i++)
    {
      int s = gsigne(gel(imag_emb, v[j]));
      gcoeff(m_sel, c, v[j]) = (s == ref) ? gen_1 : gen_m1;
      j++;
    }
  }
  return gc_const(av, m_sel);
}

static GEN gchar_hnfreduce_shallow(GEN gc, GEN cm, long prec);
static void gchar_snfbasis_shallow(GEN gc, GEN rel);
static void gcharmat_tinverse(GEN gc, GEN m, long prec);
static GEN gcharmatnewprec_shallow(GEN gc, long *precptr);

static GEN
bnf_nfnewprec_shallow(GEN bnf, long prec)
{
  GEN bnf2;
  bnf2 = shallowcopy(bnf);
  gel(bnf2,7) = nfnewprec(bnf_get_nf(bnf2), prec);
  return bnf2;
}

/* compute basis of characters; gc[1] generating family, as rows */
GEN
gcharinit(GEN bnf, GEN mod, long prec)
{
  pari_sp av = avma;
  GEN nf, zm, zmcyc, clgen, S, valS, sfu, logx;
  GEN fa2, archp, z, C, gc, cm, cyc, rel, U, Ui, m, m_inv, m0, u0;
  long n, k, r1, r2, ns, nc, nu, nm, lsfu, order;
  long nfprec, evalprec = prec, extraprec = 1;

  prec = evalprec + extraprec; /* default 1 extra word*/
  nfprec = prec + extraprec;

  /* note on precision:

     - evalprec = precision requested for evaluation

     - prec = precision available
            = (relative) precision of parameters = m_inv
            = (relative) precision of evaluation of small chars
              if no cancellation

     - nfprec = internal bnf precision used for
       the embedding matrix m
       nfprec = prec + log(h*reg) + log( |u0|_1 ) + invprec
              = prec + extraprec

     In the structure we store [evalprec,prec,nfprec]

     When evaluating chi(x) at evalprec,
     we need prec >= max(evalprec + exponent(chi), nfprec+exponent(x))
     where exponent(x) is the exponent of the number field element alpha
     obtained after principalisation of x.

     If prec is not sufficient, we call gcharnewprec.

     To mitigate precision increase, we always initialize the structure
     with one extra word.

     Final remark: a gchar struct may have inconsistent values
     for prec and nfprec, for example if it has been saved and loaded at
     default prec : one should call gcharnewprec then.
  */

  if (!checkbnf_i(bnf))
    bnf = bnfinit0(bnf, 1, NULL, nfprec);
  else
  {
    GEN fu = bnf_get_sunits(bnf);
    if (!fu) fu = bnf_get_fu(bnf); /* impose fundamental units */
    if (lg(fu) != 1) extraprec = nbits2extraprec(gexpo(fu)); /*compact or not*/
    nfprec = prec + extraprec;
    if (nf_get_prec(bnf_get_nf(bnf)) < nfprec)
      bnf = bnf_nfnewprec_shallow(bnf, nfprec);
  }
  nf = bnf_get_nf(bnf);

  /* Dirichlet group + make sure mod contains archimedean places */
  mod = check_mod_factored(nf,mod,NULL,&fa2,&archp,NULL);
  zm = localstar(nf, fa2, archp);
  zmcyc = locs_get_cyc(zm);

  /* set of primes S */
  /* FIXME: use gen_mat format instead [KB] */
  clgen = bnf_get_gen(bnf);
  S = gel(idealfactor(bnf, idealfactorback(bnf,clgen,NULL,0)),1);

  /* valuations of generators */
  valS = matvaluations(bnf, S, clgen);

  nf_get_sign(nf, &r1, &r2);
  n = r1+2*r2;
  ns = lg(S) - 1;
  nu = r1+r2-1;
  nc = lg(zmcyc) - 1;
  nm = ns+nc+n; /* number of parameters = ns + nc + r1 + r2 + r2 */

  /* units and S-units */
  sfu = gel(bnfunits(bnf,S), 1); lsfu = lg(sfu)-1; /* remove torsion */
  sfu = vecslice(sfu, 1, lsfu-1);

  /* root of unity */
  order = bnf_get_tuN(bnf);
  z = bnf_get_tuU(bnf);

  /* maximal cm subfield */
  cm = nfsubfieldscm(bnf, 0);

  /*
   Now compute matrix of parameters,
   until we obtain the right precision
   FIXME: make sure generators, units, and discrete logs
          do not depend on precision.

   m0 is the matrix of units embeddings
   u  is the HNF base change, m = m0*u

   subsequent steps may lead to precision increase, we put everything in gc
   struct and modify it in place.

     A) sets m0
     B) sets U, cyc, rel, U and Ui
     C) sets m_inv
  */

  /* A) make big matrix m0 of embeddings of units */

  if (DEBUGLEVEL>2) err_printf("start matrix m\n");
  m = cgetg(nm + 1, t_MAT);
  for(;;)
  {
    for (k = 1; k < lsfu; k++)
    { /* Lambda_S (S-units) then Lambda_f, fund. units */
      logx = gchar_nflog(bnf,zm,S,gel(sfu,k), nfprec);
      if (!logx) break;
      gel(m, k) = logx;
    }
    if (k == lsfu) break;
    extraprec *= 2;
    nfprec = prec + extraprec;
    bnf = bnf_nfnewprec_shallow(bnf, nfprec);
  }
  for (k = 1; k <= nc; k++) /* Gamma, structure of (Z/m)* */
  {
    C = zerocol(nm);
    gel(C, ns+k) = gel(zmcyc, k);
    gel(m, ns+nu+k) = C;
  }
  /* zeta, root of unity */
  gel(m, ns+nu+nc+1) = gchar_nflog(bnf,zm,S,z,nfprec);
  shallow_clean_rat(gel(m, ns+nu+nc+1), 1, nm, stoi(order), prec);
  for (k = 1; k <= r2; k++) /* embed Z^r_2 */
  {
    C = zerocol(nm);
    gel(C, ns+nc+r1+r2+k) = gen_1;
    gel(m, ns+nu+nc+1+k) = C;
  }
  if (DEBUGLEVEL>1) err_printf("matrix m = %Ps\n", m);

  m0 = m;
  u0 = gen_0;
  rel = U = Ui = gen_0;
  cyc = gen_0;
  m_inv = gen_0;

  /* only m and m_inv depend on precision and are recomputed under gcharnewprec. */
  gc = mkvecn(GC_LENGTH,
              m_inv, /* internal basis, characters as rows */
              bnf,
              zm,    /* Zk/mod, nc components */
              S,     /* generators of clgp, ns components */
              valS,
              mkvec2(vecslice(sfu,1,ns), vecslice(sfu,ns+1,ns+nu)),
              mkvec3(mkvecsmall3(evalprec,prec,nfprec),
                     mkvecsmall4(0,0,0,0), /* ntors, nfree, nalg */
                     mkvecsmall4(ns,nc,r1+r2,r2)),
              cyc, /* reduced components */
              mkvec3(rel, U, Ui), /* internal / SNF base change */
              m0,                 /* embeddings of units */
              u0);                /* m_inv = (m0 u0)~^-1 */

  /* B) do HNF reductions + LLL (may increase precision) */
  m = gchar_hnfreduce_shallow(gc, cm, nfprec);

  /* C) compute snf basis of torsion subgroup */
  rel = shallowtrans(matslice(m, 1, ns+nc, 1, ns+nc));
  gchar_snfbasis_shallow(gc, rel);

  /* D) transpose inverse m_inv = (m0*u)~^-1 (may increase precision) */
  gcharmat_tinverse(gc, m, prec);
  return gerepilecopy(av, gc);

}

/* b) do HNF reductions + LLL + SNF form, keep base change u0 */
static GEN
gchar_hnfreduce_shallow(GEN gc, GEN cm, long nfprec)
{
  GEN bnf = gchar_get_bnf(gc), nf = bnf_get_nf(bnf), u, u0, m;
  long order, r1, r2, ns, nc, n, nu, nm, ncm = 0;

  nf_get_sign(nf, &r1, &r2);
  n = r1 + 2*r2;
  nu = r1 + r2 - 1;
  ns = gchar_get_ns(gc);
  nc = gchar_get_nc(gc);
  nm = ns+nc+n; /* ns + nc + r1 + r2 + r2 */
  order = 2*bnf_get_tuN(bnf);
  u0 = matid(nm);
  m = shallowcopy(gchar_get_m0(gc)); /* keep m0 unchanged */
  if (DEBUGLEVEL>1) err_printf("matrix m = %Ps\n", m);
  if (nc)
  { /* keep steps 1&2 to make sure we have zeta_m */
    u = hnf_block(m, ns,nc, ns+nu,nc+1);
    u0 = ZM_mul(u0, u); m = RgM_ZM_mul(m, u);
    if (DEBUGLEVEL>2) err_printf("step 1 -> %Ps\n", m);
    u = hnf_block(m, ns,nc, ns,nu+nc);
    u0 = ZM_mul(u0, u); m = RgM_ZM_mul(m, u);
    if (DEBUGLEVEL>2) err_printf("step 2 -> %Ps\n", m);
  }
  if (r2)
  {
    u = hnf_block(m, nm-r2,r2, nm-r2-1,r2+1);
    u0 = ZM_mul(u0, u); m = RgM_ZM_mul(m, u);
    if (DEBUGLEVEL>2) err_printf("step 3 -> %Ps\n", m);
  }
  /* remove last column */
  setlg(u0, nm); setlg(m, nm);
  if (DEBUGLEVEL>2) err_printf("remove last col -> %Ps\n", m);

  if (!gequal0(cm))
  {
    GEN v, Nargs;
    long bit = - prec2nbits(nfprec) + 16 + expu(order);
    /* reduce on Norm arguments */
    v = cm_select(nf, cm, nfprec);
    if (DEBUGLEVEL>2) err_printf("cm_select -> %Ps\n", v);
    ncm = nbrows(v);
    gchar_set_u0(gc, u0);
    for(;;)
    {
      long e, emax, i;
      Nargs = gmul(v, rowslice(m, nm-r2+1, nm));
      if (DEBUGLEVEL>2) err_printf("Nargs -> %Ps\n", Nargs);
      emax = bit-1;
      for (i = ns+nc+1; i < lg(Nargs); i++)
      {
        gel(Nargs,i) = grndtoi(gmulgs(gel(Nargs,i), order), &e);
        emax = maxss(emax,e);
      }
      if (emax < bit) break;
      if (DEBUGLEVEL>1) err_printf("cm select: doubling prec\n");
      nfprec = precdbl(nfprec);
      m = gcharmatnewprec_shallow(gc, &nfprec);
    }
    if (DEBUGLEVEL>2) err_printf("rounded Nargs -> %Ps\n", Nargs);
    u = hnf_block(Nargs, 0, ncm, ns+nc, n-1);
    u0 = ZM_mul(u0, u); m = RgM_ZM_mul(m, u);
    if (DEBUGLEVEL>2) err_printf("after cm reduction -> %Ps\n", m);
  }

  /* apply LLL on Lambda_m, may need to increase prec */
  gchar_set_nalg(gc, ncm);
  gchar_set_u0(gc, u0);

  if (nu > 0)
  {
    GEN u = NULL;
    while (1)
    {
      u = lll_block(m, ns+nc, n, ns+nc, nu); if (u) break;
      nfprec = precdbl(nfprec);
      /* recompute m0 * u0 to higher prec */
      m = gcharmatnewprec_shallow(gc, &nfprec);
    }
    u0 = gmul(u0, u); m = gmul(m, u);
  }
  if (DEBUGLEVEL>1) err_printf("after LLL reduction -> %Ps\n", m);
  gchar_set_u0(gc, u0); return m;
}

/* convert to snf basis of torsion + Z^(r1+2*r2-1) */
static void
gchar_snfbasis_shallow(GEN gc, GEN rel)
{
  long n, r1, r2;
  GEN nf, cyc, U, Ui;

  nf = bnf_get_nf(gchar_get_bnf(gc));
  nf_get_sign(nf, &r1, &r2);
  n = r1+2*r2;

  rel = ZM_hnf(rel);
  if (DEBUGLEVEL>1) err_printf("relations after hnf: %Ps\n", rel);
  cyc = ZM_snf_group(rel, &U, &Ui);
  if (lg(cyc)==1)
  {
    cyc = zerovec(n-1);
    U = shallowconcat(zeromat(n-1,lg(rel)-1),matid(n-1));
    Ui = shallowtrans(U);
  }
  else if (n!=1)
  {
    cyc = shallowconcat(cyc, zerovec(n-1));
    U = shallowmatconcat(mkmat22(U,gen_0,gen_0,matid(n-1)));
    Ui = shallowmatconcat(mkmat22(Ui,gen_0,gen_0,matid(n-1)));
  }

  rel = shallowtrans(rel);
  U = shallowtrans(U);
  Ui = shallowtrans(Ui);

  gchar_set_nfree(gc, n-1);
  gchar_set_ntors(gc, (lg(cyc)-1) - (n-1));
  gchar_set_cyc(gc, shallowconcat(cyc, real_0(gchar_get_prec(gc))));
  gchar_set_HUUi(gc, rel, U, Ui);
}


/* c) transpose inverse + clean rationals.
   prec = target prec,
   internal prec = nfprec */
static void
gcharmat_tinverse(GEN gc, GEN m, long prec)
{
  GEN bnf, m_inv;
  long k, n, r1, r2, ns, nc, ncm, nm, nfprec, bitprec;
  bitprec = prec2nbits(prec);
  nfprec = gchar_get_nfprec(gc);

  bnf = gchar_get_bnf(gc);
  nf_get_sign(bnf_get_nf(bnf), &r1, &r2);
  n = r1+2*r2;
  ns = gchar_get_ns(gc);
  nc = gchar_get_nc(gc);
  ncm = gchar_get_nalg(gc);
  nm = ns+nc+n; /* ns + nc + r1 + r2 + r2 */

  while (1)
  {
    GEN v0, mm;
    /* insert at column ns+nc+r1+r2, or last column if cm */
    v0 = vec_v0(nm, ns+nc+1, r1, r2);
    mm = shallowmatinsert(m, v0, ncm? nm: nm-r2);
    if (DEBUGLEVEL>1) err_printf("add v0 -> %Ps\n", mm);
    mm = shallowtrans(mm);
    if (DEBUGLEVEL>2) err_printf("transposed -> %Ps\n", mm);
    m_inv = RgM_inv(mm); /* invert matrix, may need to increase prec */
    if (m_inv)
    {
      if (DEBUGLEVEL>1) err_printf("inverse: %Ps\n",m_inv);
      m_inv = vecsplice(m_inv, ncm? nm: nm-r2); /* remove v0 */
      if (DEBUGLEVEL>1) err_printf("v0 removed: %Ps\n", m_inv);
      m_inv = shallowtrans(m_inv);
      /* enough precision? */
      /* |B - A^(-1)| << |B|.|Id-B*A| */
      if (gexpo(m_inv) + gexpo(gsub(RgM_mul(m_inv, m), gen_1))
          + expu(lg(m)) <= -bitprec) break;
    }
    nfprec = precdbl(nfprec);
    m = gcharmatnewprec_shallow(gc, &nfprec); /* m0 * u0 to higher prec */
  }
  /* clean rationals */
  if (nc)
  { /* reduce mod exponent of the group, TODO reduce on each component */
    GEN zmcyc = locs_get_cyc(gchar_get_zm(gc));
    GEN e = ZV_lcm(zmcyc);
    long k;
    for (k = 1; k <= nc; k++)
      shallow_clean_rat(gel(m_inv, ns+k), 1, nm - 1, /*zmcyc[k]*/e, prec);
  }
  if (ncm)
  {
    long i, j, k;
    for (k = 1; k <= r2; k++)
      shallow_clean_rat(gel(m_inv,nm-k+1), 1, nm-1, NULL, prec);
    for (i = 1; i<=r1+r2; i++)
      for (j = 1; j <= ncm; j++) gcoeff(m_inv, ns+nc+j, ns+nc+i) = gen_0;
  }
  if (DEBUGLEVEL>1) err_printf("cyc/cm cleaned: %Ps", shallowtrans(m_inv));
  /* normalize characters, parameters mod Z */
  for (k = 1; k <= ns+nc; k++) gel(m_inv, k) = gfrac(gel(m_inv, k));
  /* increase relative prec of real values */
  gchar_set_basis(gc, gprec_w(m_inv, prec));
}

/* recompute matrix with precision increased */
static void
vaffect_shallow(GEN x, long i0, GEN y)
{
  long i;
  for (i = 1; i < lg(y); i++)
    gel(x, i+i0) = gel(y, i);
}

/* u0 the base change, returns m0 * u0 */
static GEN
gcharmatnewprec_shallow(GEN gc, long *nfprecptr)
{
  GEN bnf, m0, u0, sunits, fu, c, emb;
  long k, ns, nc, nu, incrprec=0;
  ns = gchar_get_ns(gc);
  nc = gchar_get_nc(gc);
  nu = gchar_get_r1(gc) + gchar_get_r2(gc) - 1;
  bnf = gchar_get_bnf(gc);
  sunits = gchar_get_Sunits(gc);
  fu = gchar_get_fu(gc);

  m0 = gchar_get_m0(gc);
  u0 = gchar_get_u0(gc);

  /* TODO: see how to return bnf */
  /*if (DEBUGLEVEL) pari_warn(warnprec,"gcharinit",*nfprecptr);*/
  c = getrand();
  bnf = bnf_nfnewprec_shallow(bnf,*nfprecptr);
  setrand(c);

  /* recompute the nfembedlogs of s-units and fundamental units */
  for (k = 1; k <= ns; k++) /* Lambda_S, s-units */
  {
    emb = nfembedlog(bnf,gel(sunits,k), *nfprecptr);
    if (!emb) { incrprec = 1; break; }
    vaffect_shallow(gel(m0, k), ns+nc, emb);
  }
  for (k = 1; k <= nu && !incrprec; k++) /* Lambda_f, fundamental units */
  {
    emb = nfembedlog(bnf,gel(fu,k), *nfprecptr);
    if (!emb) { incrprec = 1; break; }
    vaffect_shallow(gel(m0,ns+k), ns+nc, emb);
  }

  if (incrprec)
  {
    *nfprecptr = precdbl(*nfprecptr);
    return  gcharmatnewprec_shallow(gc, nfprecptr);
  }

  gchar_set_bnf(gc, bnf);
  gchar_set_nfprec(gc, *nfprecptr);
  gchar_set_m0(gc, m0); /* no need, shallow */

  return gmul(m0, u0);
}

static void _check_gchar_group(GEN gc, long flag);
static void
check_gchar_group(GEN gc) { _check_gchar_group(gc, 0); }

/* increase prec if needed. FIXME: hardcodes gc[7] and gc[10] */
GEN
gcharnewprec(GEN gc, long newprec)
{
  long prec, prec0, nfprec, nfprec0;
  pari_sp av = avma;
  GEN gc2 = shallowcopy(gc);

  _check_gchar_group(gc2, 1); /* ignore illegal prec */
  prec = gchar_get_prec(gc2);
  nfprec = gchar_get_nfprec(gc2);

  if (newprec > prec)
  { /* increase precision */
    long incrprec = newprec - prec + 1;
    if (DEBUGLEVEL) pari_warn(warnprec,"gcharnewprec",newprec);
    prec += incrprec;
    nfprec += incrprec;
    gel(gc2, 7) = shallowcopy(gel(gc,7));
    gmael(gc2, 7, 1) = mkvecsmall3(newprec, prec, nfprec);
  }
  prec0 = gprecision(gchar_get_basis(gc2));
  nfprec0 = nf_get_prec(gchar_get_bnf(gc2));

  if ((prec0 && prec > prec0) || (nfprec0 && nfprec > nfprec0))
  {
    GEN m, cyc;
    if (DEBUGLEVEL) pari_warn(warnprec,"gcharnewprec",nfprec);
    gel(gc2, 10) = shallowcopy(gel(gc2, 10));
    m = gcharmatnewprec_shallow(gc2, &nfprec);
    if (DEBUGLEVEL>2) err_printf("m0*u0 recomputed -> %Ps\n", m);
    gcharmat_tinverse(gc2, m, prec);
    cyc = shallowcopy(gchar_get_cyc(gc2));
    gel(cyc, lg(cyc)-1) = real_0(prec);
    gchar_set_cyc(gc2, cyc);
  }
  return gerepilecopy(av, gc2);
}

static void
check_localstar(GEN x)
{
  if (typ(x) != t_VEC || lg(x) != LOCS_LENGTH + 1)
    pari_err_TYPE("char group", x);
  /* FIXME: check components once settled */
}

int
is_gchar_group(GEN gc)
{
  return (typ(gc) == t_VEC
      &&  lg(gc) == GC_LENGTH + 1
      &&  typ(gel(gc, 7)) == t_VEC
      &&  lg(gel(gc, 7)) == 4
      &&  typ(gmael(gc, 7, 1))  == t_VECSMALL
      &&  typ(gmael(gc, 7, 2))  == t_VECSMALL
      &&  typ(gmael(gc, 7, 3))  == t_VECSMALL
      &&  (checkbnf_i(gchar_get_bnf(gc))  != NULL));
}

/* validates the structure format.
 * Raise error if inconsistent precision, unless flag=1.
 */
static void
_check_gchar_group(GEN gc, long flag)
{
  GEN b, bnf;
  if (typ(gc) != t_VEC || lg(gc) != GC_LENGTH + 1)
    pari_err_TYPE("char group", gc);
  check_localstar(gchar_get_zm(gc));
  if (typ(gchar_get_loccyc(gc)) != t_VEC)
    pari_err_TYPE("gchar group (loccyc)", gc);
  b = gchar_get_basis(gc);
  if (typ(b) != t_MAT) pari_err_TYPE("gchar group (basis)", gc);
  bnf = gchar_get_bnf(gc); checkbnf(bnf);
  if (typ(gel(gc,7)) != t_VEC ||typ(gmael(gc,7,1)) != t_VECSMALL)
    pari_err_TYPE("gchar group (gc[7])", gc);
  if (!flag)
  { /* modify prec inplace if incoherent */
    long prec0, nfprec0;
    prec0 = gprecision(b);
    nfprec0 = nf_get_prec(bnf);
    if ((prec0 && gchar_get_prec(gc) > prec0)
        || (nfprec0 && gchar_get_nfprec(gc) > nfprec0))
      pari_err_PREC("gchar group, please call gcharnewprec");
  }
}

/* basis of algebraic characters + cyc vector */
static GEN
gchar_algebraic_basis(GEN gc)
{
  long ntors, nfree, nc, nm, r2, nalg, n0, k;
  GEN basis, args, m, w, normchar, alg_basis, tors_basis;

  /* in snf basis */
  ntors = gchar_get_ntors(gc); /* number of torsion generators */
  nfree = gchar_get_nfree(gc);
  nc = ntors + nfree;
  /* in internal basis */
  n0 = gchar_get_ns(gc) + gchar_get_nc(gc); /* last index of torsion chars, internal basis */
  r2 = gchar_get_r2(gc);
  nm = gchar_get_nm(gc);
  /* in both */
  nalg = gchar_get_nalg(gc); /* number of generators of free algebraic chars */

  /* finite order characters have weight 0 */
  tors_basis = matid(ntors);

  /* the norm is an algebraic character */
  normchar = gneg(col_ei(nc+1,nc+1));

  /* add sublattice of algebraic */

  if (!nalg)
  {
    if (DEBUGLEVEL>2) err_printf("nalg=0\n");
    return shallowmatconcat(mkvec2(tors_basis,normchar));
  }

  /* block of k_s parameters of free algebraic */
  args = matslice(gchar_get_basis(gc),n0+1,n0+nalg,nm-r2+1,nm);

  if (r2 == 1)
  {
    /* no parity condition */
    if (DEBUGLEVEL>2) err_printf("r2 = 1 -> args = %Ps\n", args);
    alg_basis = matid(nalg);
    w = gel(args,1);
  }
  else
  {
    /* parity condition: w + k_s = 0 mod 2 for all s,
       ie solve x.K constant mod 2, ie solve
       x.K' = 0 mod 2 where K' = [ C-C0 ] (substract first column)
     */
    /* select block k_s in char parameters and */
    if (DEBUGLEVEL>2) err_printf("block ks -> %Ps\n", args);
    m = cgetg(r2, t_MAT);
    for (k = 1; k < r2; k++)
      gel(m,k) = gsub(gel(args,k+1),gel(args,1));
    if (DEBUGLEVEL>2) err_printf("block ks' -> %Ps", m);
    alg_basis = shallowtrans(gel(matsolvemod(shallowtrans(m),gen_2,gen_0,1),2));
    if (DEBUGLEVEL>2) err_printf("alg_basis -> %Ps\n", alg_basis);
    w = gmul(alg_basis, gel(args,1));
    if (DEBUGLEVEL>2) err_printf("w -> %Ps\n", w);
  }
  /* add weight to infinite order characters, at position nc+1 */
  w = gneg(gdivgs(gmodgs(w, 2), 2));
  alg_basis = shallowmatconcat(mkvec3(alg_basis, zerovec(nfree-nalg), w));

  if (lg(tors_basis)>1)
    basis = shallowmatconcat(mkmat22(tors_basis, gen_0, gen_0, alg_basis));
  else
    basis = alg_basis;
  return shallowmatconcat(mkvec2(shallowtrans(basis),normchar));
}
static GEN
gchar_algebraicnormtype(GEN gc, GEN type)
{
  GEN w = NULL, w1, v;
  long i, r1, r2, n;
  r1 = gchar_get_r1(gc);
  r2 = gchar_get_r2(gc);
  for (i=1; i<=r1; i++)
  {
    w1 = addii(gmael(type,i,1),gmael(type,i,2));
    if (!w) w = w1;
    else if (!equalii(w,w1)) return NULL;
  }
  for (i=r1+1; i<=r1+r2; i++)
  {
    w1 = gmael(type,i,1);
    if (!w) w = w1;
    else if (!equalii(w,w1)) return NULL;
    if (!equalii(w,gmael(type,i,2))) return NULL;
  }
  n = lg(gchar_get_cyc(gc))-1;
  v = zerocol(n);
  gel(v,n) = negi(w);
  return mkvec(v);
}
static GEN
gchar_algebraicoftype(GEN gc, GEN type)
{
  long i, r1, r2, nalg, n0, nm;
  GEN p, q, w, k, matk, chi;
  /* in internal basis */
  n0 = gchar_get_ns(gc) + gchar_get_nc(gc); /* last index of torsion chars, internal basis */
  r1 = gchar_get_r1(gc);
  r2 = gchar_get_r2(gc);
  nm = gchar_get_nm(gc);
  /* in both */
  nalg = gchar_get_nalg(gc); /* number of generators of free algebraic chars */

  if (typ(type)!=t_VEC || lg(type) != r1+r2+1)
    pari_err_TYPE("gcharalgebraic (1)", type);
  for (i = 1; i<=r1+r2; i++)
    if (typ(gel(type,i)) != t_VEC
        ||lg(gel(type,i)) != 3
        ||typ(gmael(type,i,1)) != t_INT
        ||typ(gmael(type,i,2)) != t_INT)
      pari_err_TYPE("gcharalgebraic (2)", type);

  chi = gchar_algebraicnormtype(gc, type);
  if (chi) return chi;

  if (!nalg) return NULL;
  k = cgetg(r2+1,t_VEC);
  p = gmael(type, 1, 1);
  q = gmael(type, 1, 2); w = addii(p, q);
  gel(k, 1) = subii(q, p);
  for (i = 2; i <= r2; i++)
  {
    p = gmael(type, i, 1);
    q = gmael(type, i, 2);
    if (!equalii(w, addii(p, q))) return NULL;
    gel(k, i) = subii(q, p);
  }
  /* block of k_s parameters of free algebraic */
  matk = matslice(gchar_get_basis(gc),n0+1,n0+nalg,nm-r2+1,nm);
  chi = inverseimage(shallowtrans(matk),shallowtrans(k));
  if (lg(chi) == 1) return NULL;
  for (i=1; i<lg(chi); i++) if (typ(gel(chi,i)) != t_INT) return NULL;
  chi = mkvec4(zerocol(gchar_get_ntors(gc)), chi,
               zerocol(gchar_get_nfree(gc) - nalg), gmul2n(negi(w),-1));
  return mkvec(shallowconcat1(chi));
}

GEN
gcharalgebraic(GEN gc, GEN type)
{
  pari_sp av = avma;
  GEN b;
  check_gchar_group(gc);
  b = type? gchar_algebraicoftype(gc, type): gchar_algebraic_basis(gc);
  if (!b) { set_avma(av); return cgetg(1, t_VEC); }
  return gerepilecopy(av, b);
}

/*********************************************************************/
/*                                                                   */
/*                          CHARACTERS                               */
/*                                                                   */
/*********************************************************************/

static GEN
check_gchar_i(GEN chi, long l, GEN *s)
{
  long i, lchi=lg(chi)-1;
  if (lchi!=l && lchi!=l-1) /* allow missing norm component */
    pari_err_DIM("check_gchar_i [chi]");
  if (lchi==l)
  {
    if (s)
    {
      *s = gel(chi,l);
      switch(typ(*s))
      {
        case t_INT:
        case t_FRAC:
        case t_REAL:
        case t_COMPLEX: break;
        default: pari_err_TYPE("check_gchar_i [s]", *s);
      }
    }
    chi = vecslice(chi,1,l-1);
  }
  else if (s) *s = gen_0;
  for (i=1; i<l; i++) if (typ(gel(chi,i))!=t_INT)
    pari_err_TYPE("check_gchar_i [coefficient]", gel(chi,i));
  return chi;
}

static GEN
check_gchar(GEN gc, GEN chi, GEN *s)
{
  if (typ(chi)!=t_COL) pari_err_TYPE("check_gchar [chi]", chi);
  return check_gchar_i(chi, lg(gchar_get_cyc(gc))-1, s);
}

static GEN
check_gchari(GEN gc, GEN chi, GEN *s)
{
  if (typ(chi)!=t_VEC) pari_err_TYPE("check_gchari [chi]", chi);
  return check_gchar_i(chi, lg(gel(gchar_get_basis(gc),1)), s);
}

/* from coordinates on snf basis, return coordinates on internal basis, set
 * s to the norm component */
static GEN
gchar_internal(GEN gc, GEN chi, GEN *s)
{
  chi = check_gchar(gc, chi, s);
  return ZV_ZM_mul(shallowtrans(chi), gchar_get_Ui(gc));
}

/* from internal basis form, return the R/Z components and set s to the R
 * component */
static GEN
gchari_log(GEN gc, GEN chi, GEN *s)
{
  long i, n;
  chi = check_gchari(gc, chi, s);
  chi = RgV_RgM_mul(shallowtrans(chi), gchar_get_basis(gc));
  n = gchar_get_ns(gc) + gchar_get_nc(gc); /* take exponents mod Z */
  for (i = 1; i <= n; i++) gel(chi,i) = gfrac(gel(chi,i));
  return chi;
}

static GEN
gchari_shift(GEN gc, GEN chi, GEN s0)
{
  GEN s;
  check_gchar_group(gc);
  chi = check_gchari(gc, chi, &s);
  return shallowconcat(chi, gadd(s0,s));
}

/* chip has ncp = #zm[1][i].cyc components */
static GEN
conductor_expo_pr(GEN gens_fil, GEN chip)
{
  long i;
  for (i = lg(gens_fil) - 1; i > 0; i--)
  {
    long j;
    GEN gens = gel(gens_fil, i);
    for (j = 1; j < lg(gens); j++)
    {
      GEN v = gmul(chip, gel(gens, j));
      if (denom_i(v) != gen_1)
        return stoi(i);
    }
  }
  return gen_0;
}

/* assume chi in log form */
static GEN
gcharlog_conductor_f(GEN gc, GEN chi)
{
  GEN nf, zm, expo, Lsprk, ufil, famod;
  long i, np, ns, ic;
  pari_sp av = avma;
  if (gchar_get_nc(gc) == 0)
    return gen_1;
  zm = gchar_get_zm(gc);
  ns = gchar_get_ns(gc);
  Lsprk = locs_get_Lsprk(zm);
  ufil = locs_get_Lgenfil(zm);
  famod = locs_get_famod(zm);
  np = lg(Lsprk) - 1;
  expo = cgetg(np + 1, t_VEC);
  for (i = 1, ic = ns; i <= np ; i++)
  {
    long ncp;
    GEN sprk, gens, chip;
    sprk = gel(Lsprk, i);
    gens = gel(ufil, i);
    ncp = lg(sprk_get_cyc(sprk)) - 1;
    chip = vecslice(chi, ic + 1, ic + ncp);
    gel(expo, i) = conductor_expo_pr(gens, chip);
    ic += ncp;
  }
  famod = mkmat2(gel(famod,1),expo);
  nf = bnf_get_nf(gchar_get_bnf(gc));
  return gerepilecopy(av, idealfactorback(nf, famod, NULL, 0)); /* red = 0 */
}

/* ={sigma} s.t. k_sigma = 1 */
static GEN
gcharlog_conductor_oo(GEN gc, GEN chi)
{
  long ns, nc, noo, i;
  GEN k_real, chi_oo, moo, den;
  ns = gchar_get_ns(gc);
  nc = gchar_get_nc(gc);
  moo = locs_get_m_infty(gchar_get_zm(gc));
  noo = lg(moo)-1;
  k_real = vecslice(chi, ns+nc-noo+1, ns+nc);
  chi_oo = zerovec(gchar_get_r1(gc));
  for (i=1; i<=noo; i++)
  {
    den = Q_denom(gel(k_real,i));
    if (den && !equali1(den)) gel(chi_oo, moo[i]) = gen_1;
  }
  return chi_oo;
}

static GEN
gchari_conductor(GEN gc, GEN chi)
{
  pari_sp av = avma;
  chi = gchari_log(gc, chi, NULL);
  return gerepilecopy(av, mkvec2(gcharlog_conductor_f(gc, chi), gcharlog_conductor_oo(gc, chi)));
}

GEN
gchar_conductor(GEN gc, GEN chi)
{
  pari_sp av = avma;
  check_gchar_group(gc);
  return gerepilecopy(av, gchari_conductor(gc, gchar_internal(gc, chi, NULL)));
}

int
gcharisalgebraic(GEN gc, GEN chi, GEN *pq)
{
  long i, ntors, nfree, n0, nalg, r1, r2;
  GEN w, chii, v;
  pari_sp av = avma;
  check_gchar_group(gc);
  /* in snf basis */
  ntors = gchar_get_ntors(gc);
  nfree = gchar_get_nfree(gc);
  /* in internal basis */
  r1 = gchar_get_r1(gc);
  r2 = gchar_get_r2(gc);
  n0 = gchar_get_nm(gc) - r2; /* last index before k_s */
  /* in both */
  nalg = gchar_get_nalg(gc); /* number of generators of free algebraic chars */

  check_gchar(gc, chi, &w);
  /* check component are on algebraic generators */
  for (i=ntors+nalg+1;i<=ntors+nfree;i++)
    if (!gequal0(gel(chi,i))) return gc_bool(av, 0);
  chii = gchar_duallog(gc, chi);

  if (r1) /* not totally complex: finite order * integral power of norm */
  {
    if (typ(w) != t_INT) return gc_bool(av, 0);
    w = gneg(w);
    if (pq)
    {
      /* set the infinity type */
      v = cgetg(r1+r2+1, t_VEC);
      for (i = 1; i <= r1; i++)
        gel(v, i) = mkvec2(w, gen_0);
      for (i = r1+1; i <= r1+r2; i++)
        gel(v, i) = mkvec2(w, w);
    }
  }
  else /* totally complex */
  {
    /* condition is k_s + w = 0 mod 2 for all s */
    w = gneg(gmul2n(w, 1));
    if (typ(w) != t_INT) return gc_bool(av, 0);
    for (i = 1; i <= r2; i++)
      if (smodis(addii(gel(chii, n0 + i), w), 2))
        return gc_bool(av, 0);
    if (pq)
    {
      /* set the infinity type */
      v = cgetg(r2+1, t_VEC);
      for (i = 1; i <= r2; i++)
      {
        GEN p, q;
        q = gmul2n(addii(w, gel(chii, n0+i)), -1);
        p = gmul2n(subii(w, gel(chii, n0+i)), -1);
        gel(v, i) = mkvec2(p, q);
      }
    }
  }
  if (pq)
  {
    *pq = gerepilecopy(av, v);
    av = avma;
  }
  return gc_bool(av, 1);
}

GEN
gcharlocal(GEN gc, GEN chi, GEN v, long prec)
{
  pari_sp av = avma;
  GEN s, chiv, k, phi, logchi, nf, moo, famod;
  long tau, r1, r2, i;
  check_gchar_group(gc);
  chi = gchar_internal(gc, chi, &s);
  logchi = gchari_log(gc, chi, NULL);
  if (typ(v) == t_INT) /* v infinite */
  {
    tau = itos(v);
    r1 = gchar_get_r1(gc);
    r2 = gchar_get_r2(gc);
    if (tau<=0) pari_err_DOMAIN("gcharlocal [index of an infinite place]", "v", "<=", gen_0, v);
    if (tau>r1+r2) pari_err_DOMAIN("gcharlocal [index of an infinite place]", "v", ">", stoi(r1+r2), v);
    phi = gel(logchi, gchar_get_ns(gc)+gchar_get_nc(gc)+tau);
    if (tau<=r1) /* v real */
    {
      moo = gel(gchar_get_mod(gc),2);
      i = zv_search(moo,tau);
      if (i==0) k = gen_0;
      else
      {
        k = gel(logchi, gchar_get_ns(gc)+gchar_get_nc(gc)-lg(moo)+1+i);
        /* k == 0 or 1/2 */
        if (!gequal0(k)) k = gen_1;
      }
    }
    else /* v complex */
      k = gel(logchi, gchar_get_ns(gc)+gchar_get_nc(gc)+r2+tau);
    if (s) phi = gsub(phi,gmul(gen_I(),s));
    chiv = mkvec2(k,phi);
  }
  else /* v finite */
  {
    checkprid(v);
    nf = bnf_get_nf(gchar_get_bnf(gc));
    famod = gel(gchar_get_mod(gc),1);
    if (gen_search(gel(famod,1), v, (void*)cmp_prime_ideal, cmp_nodata))
    {
      if (idealval(nf, gcharlog_conductor_f(gc,logchi), v) > 0)
        /* FIXME: only compute conductor at v */
        pari_err_IMPL("local component of a Grossencharacter at a ramified prime");
    }
    chiv = mkvec(gchari_eval(gc, chi, v, 0, logchi, NULL, s, prec));
  }
  return gerepilecopy(av, chiv);
}


/*******************************************************************/
/*                                                                 */
/*                EVALUATION OF CHARACTERS                         */
/*                                                                 */
/*******************************************************************/

/* logarithm of a character */
/* TODO document the fact that matrices are accepted as input? */
GEN
gchar_duallog(GEN gc, GEN chi)
{
  if (typ(chi) == t_MAT)
  {
    long k;
    GEN r;
    pari_sp av = avma;
    r = cgetg(lg(chi), t_MAT);
    for (k = 1; k < lg(chi); k++)
      gel(r, k) = gchar_duallog(gc, gel(chi, k));
    return gerepilecopy(av, shallowtrans(r));
  }
  else
    return gchari_log(gc, gchar_internal(gc, chi, NULL), NULL);
}

/* gp version, with norm component */
GEN
gcharduallog(GEN gc, GEN chi)
{
  pari_sp av = avma;
  GEN logchi, s;
  check_gchar_group(gc);
  check_gchar(gc, chi, &s);
  logchi = gchar_duallog(gc, chi);
  return gerepilecopy(av, shallowconcat1(mkcol2(logchi,s)));
}

/* complete log of ideal */
/* TODO handle nfembedlog()==NULL loss of precision */
GEN
gchar_log(GEN gc, GEN x, long prec)
{
  GEN bnf, zm, val_S, v, vp, alpha, t, arch_log, zm_log;
  pari_sp av = avma;
  check_gchar_group(gc);

  bnf = gchar_get_bnf(gc);
  zm = gchar_get_zm(gc);
  val_S = gchar_get_valS(gc);
  t = bnfisprincipal0(bnf, x, nf_GENMAT);
  v = gel(t, 1); alpha = gel(t, 2);
  /* TODO: increase prec if alpha is large? */
  /* exponents on primes in S */
  vp = gmul(val_S, v);
  if (DEBUGLEVEL>2) err_printf("vp %Ps\n", vp);
  arch_log = nfembedlog(bnf,alpha,prec);
  if (DEBUGLEVEL>2) err_printf("arch log %Ps\n", arch_log);
  zm_log = gchar_logm(bnf,zm,alpha);
  if (DEBUGLEVEL>2) err_printf("zm_log(alpha) %Ps\n", zm_log);
  return gerepilecopy(av, shallowconcat1(mkvec3(vp,gneg(zm_log),gneg(arch_log))));
}

/* gp version, with norm component */
GEN
gcharlog(GEN gc, GEN x, long prec)
{
  pari_sp av = avma;
  GEN logx, norm;
  logx = gchar_log(gc,x,prec);
  norm = idealnorm(gchar_get_bnf(gc), x);
  norm = mkcomplex(gen_0,gdiv(glog(norm,prec),Pi2n(1,prec)));
  return gerepilecopy(av, shallowconcat1(mkvec2(logx,norm)));
}

static GEN
gcharlog_eval_raw(GEN logchi, GEN logx)
{ GEN val = gmul(logchi, logx); return gsub(val, ground(val)); }

/* if flag = 1 -> value in C, flag = 0 -> value in R/Z
 * assume gc (and logchi) has enough internal precision,
 * but increase precision if log is large */
static GEN
gchari_eval(GEN gc, GEN chi, GEN x, long flag, GEN logchi, GEN logx, GEN s0, long prec)
{
  GEN val, s = gen_0, norm = NULL;
  long prec0, extraprec;
  pari_sp av = avma;

  prec0 = gchar_get_prec(gc);

  if (!logx) logx = gchar_log(gc, x, prec0);
  if (!logchi) logchi = gchari_log(gc, chi, &s);

  /* check if precision is sufficient, take care of gexpo = -infty */
  extraprec = gexpo(logx) + gexpo(logchi);
  extraprec = extraprec > 0 ? nbits2extraprec(extraprec) : 0;
  if (prec + extraprec > prec0)
  {
    prec0 = prec + extraprec;
    gc = gcharnewprec(gc, prec0);
    logx = gchar_log(gc, x, prec0);
    logchi = gchari_log(gc, chi, &s);
  }

  s = gadd(s0,s);

  /* this row  must be computed at prec0 */
  val = gcharlog_eval_raw(logchi, logx);

  if (!gequal0(s)) norm = idealnorm(gchar_get_bnf(gc), x);

  if (flag)
  {
    val = gexp(mkcomplex(gen_0, gmul(Pi2n(1,prec), val)), prec);
    if (norm) val = gmul(val, gpow(norm, gneg(s), prec));
  }
  else if (norm)
  {
    GEN expo = gdiv(gneg(s), PiI2(prec));
    val = gadd(val, gmul(expo, glog(norm, prec)));
  }
  if (DEBUGLEVEL>1) err_printf("char value %Ps\n", val);
  return gerepilecopy(av, val);
}

GEN
gchareval(GEN gc, GEN chi, GEN x, long flag, GEN logx)
{
  GEN s;
  long prec;
  pari_sp av = avma;
  check_gchar_group(gc);
  prec = gchar_get_evalprec(gc);
  chi = gchar_internal(gc, chi, &s);
  return gerepilecopy(av, gchari_eval(gc, chi, x, flag, NULL, logx, s, prec));
}

/*******************************************************************/
/*                                                                 */
/*                         IDENTIFICATION                          */
/*                                                                 */
/*******************************************************************/

static GEN
gchar_identify_init(GEN gc, GEN Lv, long prec)
{
  pari_sp av = avma;
  GEN M, cyc, mult, pr, Lpr, Lk1, Lphi1, Lk2, Llog, C, logchi, chi_oo, eps, U;
  GEN uni, famod1, bnf;
  long r1, r2, npr, nk1, nchi, s, i, j, v, dim, ns, nc, ncol;
  check_gchar_group(gc);
  ns = gchar_get_ns(gc);
  nc = gchar_get_nc(gc);
  r1 = gchar_get_r1(gc);
  r2 = gchar_get_r2(gc);
  cyc = gchar_get_cyc(gc);
  famod1 = gmael(gchar_get_mod(gc),1,1);
  bnf = gchar_get_bnf(gc);
  nchi = lg(cyc)-2; /* ignore norm */
  if (nchi>=r1+2*r2)    mult = gel(cyc,1);
  else                  mult = gen_1;
  s = (8*prec2nbits(prec))/10;
  mult = shifti(mult,s);
  npr = 0;
  nk1 = 0;
  uni = gen_sort_uniq(Lv, (void*)cmp_universal, cmp_nodata);
  if (lg(uni) < lg(Lv)) pari_err(e_MISC, "components of Lv must be distinct");
  for (i = 1; i < lg(Lv); i++)
  {
    if (typ(gel(Lv,i)) == t_INT)
    {
      v = itos(gel(Lv,i));
      if (v <= 0) pari_err_DOMAIN("gchar_identify_init", "v", "<=", gen_0, stoi(v));
      if (v > r1+r2) pari_err_DOMAIN("gchar_identify_init", "v", ">", stoi(r1+r2), stoi(v));
      if (v <= r1) nk1++;
    }
    else
    {
      pr = gel(Lv,i);
      if (idealtyp(&pr, NULL) == id_PRINCIPAL)
        pari_err_TYPE("gchar_identify_init [ideal]", gel(Lv,i));
      for (j=1; j<lg(famod1); j++)
        if (idealval(bnf, pr, gel(famod1,j))>0)
          pari_err_DOMAIN("gchar_identify_init", "valuation at prime dividing the modulus", ">", gen_0, gpidealval(bnf, pr, gel(famod1,j)));
      npr++;
    }
  }
  /* log of prime ideals */
  Llog = cgetg(npr+1, t_VEC);
  /* index in Lchiv corresponding to the places */
  Lpr = cgetg(npr+1, t_VECSMALL); npr = 0;
  Lk1 = cgetg(nk1+1, t_VECSMALL); nk1 = 0;
  Lphi1 = zero_zv(r1); Lk2 = zero_zv(r2);
  for (i=1; i<lg(Lv); i++)
  {
    if (typ(gel(Lv,i)) == t_INT)
    {
      v = itos(gel(Lv,i));
      if (v <= r1)
      { /* TODO don't put in k1 if not in conductor (but keep as phi) */
        nk1++;
        Lk1[nk1] = i;
        Lphi1[v] = i;
      }
      else Lk2[v-r1] = i;
    }
    else
    {
      pr = gel(Lv,i);
      npr++;
      Lpr[npr] = i;
      gel(Llog,npr) = gchar_log(gc, pr, prec);
    }
  }

  /* build matrix M */
  dim = npr+nk1+r1+2*r2;
  ncol = npr+nk1+1+nchi;
  M = cgetg(npr+nk1+1+nchi+1, t_MAT);
  for (j=1; j<=npr; j++)
    gel(M,j) = col_ei(dim, j);
  for (j=npr+1; j<=npr+nk1; j++)
  {
    gel(M,j) = zerocol(dim);
    gcoeff(M,j,j) = gen_2;
  }
  j = npr+nk1+1;
  gel(M,j) = zerocol(dim);
  eps = real2n(-(7*s)/16, prec);
  for (i=npr+nk1+1; i<=npr+nk1+r1+r2; i++) gcoeff(M,i,j) = eps;
  for (j=1; j<=nchi; j++)
  {
    C = cgetg(dim+1, t_COL);
    logchi = gchar_duallog(gc, col_ei(nchi,j));
    for (i=1; i<=npr; i++)
      gel(C,i) = gcharlog_eval_raw(logchi, gel(Llog,i));
    chi_oo = gcharlog_conductor_oo(gc, logchi);
    for (i=1; i<=nk1; i++)
      gel(C,npr+i) = gel(chi_oo, itos(gel(Lv,Lk1[i])));
    for (i=1; i<=r1+2*r2; i++)
      gel(C,npr+nk1+i) = gel(logchi,ns+nc+i);
    gel(M,npr+nk1+1+j) = C;
  }
  for (i=1; i<=r1; i++)
    if (!Lphi1[i])
      for (j=1; j<=ncol; j++)
        gcoeff(M,npr+nk1+i,j) = gmul(gcoeff(M,npr+nk1+i,j),eps);
  for (i=1; i<=r2; i++)
    if (!Lk2[i])
      for (j=1; j<=ncol; j++)
      {
        gcoeff(M,npr+nk1+r1+i,j) = gmul(gcoeff(M,npr+nk1+r1+i,j),eps);
        gcoeff(M,npr+nk1+r1+r2+i,j) = gmul(gcoeff(M,npr+nk1+r1+r2+i,j),eps);
      }

  /* multiply and truncate M */
  M = gtrunc(RgM_Rg_mul(M,mult));

  /* LLL-reduce M */
  U = ZM_lll(M, 0.99, LLL_IM);
  M = ZM_mul(M,U);
  U = rowslice(U, npr+nk1+2, npr+nk1+1+nchi);

  return gerepilecopy(av, mkvecn(10,M,U,Lpr,Lk1,Lphi1,Lk2,mult,eps,Lv,mkvecsmall(prec)));
}

/* TODO return the distance between the character found and the conditions? */
static GEN
gchar_identify_i(GEN gc, GEN idinit, GEN Lchiv)
{
  GEN M, U, Lpr, Lk1, Lphi1, Lk2, mult, eps, cyc, y, x, sumphi, Lv, normcompo, bnf;
  long i, r1, r2, npr, nk1, nmiss, nnormcompo, prec;
  M = gel(idinit,1);
  U = gel(idinit,2);
  Lpr = gel(idinit,3);
  Lk1 = gel(idinit,4);
  Lphi1 = gel(idinit,5);
  Lk2 = gel(idinit,6);
  mult = gel(idinit,7);
  eps = gel(idinit,8);
  Lv = gel(idinit,9);
  prec = gel(idinit,10)[1];
  npr = lg(Lpr)-1;
  nk1 = lg(Lk1)-1;
  r1 = gchar_get_r1(gc);
  r2 = gchar_get_r2(gc);
  cyc = gchar_get_cyc(gc);
  bnf = gchar_get_bnf(gc);
  nnormcompo = 0;
  normcompo = gen_0;

  if (lg(Lv) != lg(Lchiv)) pari_err_DIM("gchar_identify_i [lg(Lv) != lg(Lchiv)]");
  for (i=1; i<lg(Lchiv); i++)
  {
    if (typ(gel(Lv,i)) != t_INT)
    {
      x = gel(Lchiv,i);
      if (typ(x) == t_COMPLEX)
      {
        nnormcompo++;
        /* 2 Pi Im(theta) / log N(pr) */
        normcompo = gadd(normcompo,
              gdiv(gmul(Pi2n(1,prec),imag_i(x)),
              glog(idealnorm(bnf,gel(Lv,i)),prec)));
        x = real_i(x);
        gel(Lchiv,i) = x;
      }
      if (!is_real_t(typ(x)))
        pari_err_TYPE("gchar_identify_i [character value: should be real or complex]", x);
    }
    else
    {
      if (typ(gel(Lchiv,i)) != t_VEC)
        pari_err_TYPE("gchar_identify_i [character at infinite place: should be a t_VEC]", gel(Lchiv,i));
      if (lg(gel(Lchiv,i)) != 3)
        pari_err_DIM("gchar_identify_i [character at infinite place: should have two components]");
      if (typ(gmael(Lchiv,i,1)) != t_INT)
        pari_err_TYPE("gchar_identify_i [k parameter at infinite place: should be a t_INT]", gmael(Lchiv,i,1));
      x = gmael(Lchiv,i,2);
      if (typ(x) == t_COMPLEX)
      {
        nnormcompo++;
        normcompo = gsub(normcompo,imag_i(x));
        x = real_i(x);
        gmael(Lchiv,i,2) = x;
      }
      if (!is_real_t(typ(x)))
        pari_err_TYPE("gchar_identify_i [phi parameter at infinite place: should be real or complex]", x);
    }
  }

  /* construct vector */
  y = zerocol(npr+nk1+r1+2*r2);
  sumphi = gen_0;
  nmiss = 0;
  for (i=1; i<=npr; i++)
    gel(y,i) = gel(Lchiv,Lpr[i]);
  for (i=1; i<=nk1; i++)
    gel(y,npr+i) = gmael(Lchiv,Lk1[i],1);
  for (i=1; i<=r1; i++)
    if (Lphi1[i])
    {
      x =  gmael(Lchiv,Lphi1[i],2);
      gel(y,npr+nk1+i) = x;
      sumphi = gadd(sumphi, x);
    }
    else nmiss++;
  for (i=1; i<=r2; i++)
    if (Lk2[i])
    {
      gel(y,npr+nk1+r1+r2+i) = gmael(Lchiv,Lk2[i],1);
      x =  gmael(Lchiv,Lk2[i],2);
      gel(y,npr+nk1+r1+i) = x;
      sumphi = gadd(sumphi, gshift(x,1));
    }
    else nmiss+=2;
  if (nmiss)
  {
    sumphi = gneg(gdiv(sumphi,stoi(nmiss)));
    sumphi = gmul(sumphi,eps);
    for (i=1; i<=r1; i++) if (!Lphi1[i]) gel(y,npr+nk1+i) = sumphi;
    for (i=1; i<=r2; i++) if (!Lk2[i])   gel(y,npr+nk1+r1+i) = sumphi;
  }
  y = gtrunc(RgC_Rg_mul(y,mult));

  /* find approximation */
  x = RgM_Babai(M, y);
  x = ZM_ZC_mul(U, x);
  for (i=1; i<lg(cyc)-1; i++) /* ignore norm */
    if (signe(gel(cyc,i))) gel(x,i) = modii(gel(x,i), gel(cyc,i));
  if (nnormcompo>0)
  {
    normcompo = gdivgu(normcompo,lg(Lv)-1);
    x = shallowconcat(x,normcompo);
  }
  return x;
}

/* TODO export the init interface */
GEN
gchar_identify(GEN gc, GEN Lv, GEN Lchiv, long prec)
{
  pari_sp av = avma;
  GEN idinit = gchar_identify_init(gc, Lv, prec);
  return gerepilecopy(av, gchar_identify_i(gc,idinit,Lchiv));
}

/*******************************************************************/
/*                                                                 */
/*                          L FUNCTION                             */
/*                                                                 */
/*******************************************************************/

/* TODO: could merge with vecan_chigen */

/* return x + yz; y != 0; z = 0,1 "often"; x = 0 "often" */
static GEN
gaddmul(GEN x, GEN y, GEN z)
{
  pari_sp av;
  if (typ(z) == t_INT)
  {
    if (!signe(z)) return x;
    if (equali1(z)) return gadd(x,y);
  }
  if (isintzero(x)) return gmul(y,z);
  av = avma;
  return gerepileupto(av, gadd(x, gmul(y,z)));
}

GEN
vecan_gchar(GEN an, long n, long prec)
{
  forprime_t iter;
  pari_sp av = avma;
  GEN gc = gel(an,1), chi = gel(an,2), BOUND = stoi(n), v = vec_ei(n, 1);
  GEN gp = cgetipos(3), NZ = NULL, nf, N, chilog, s;
  ulong p;

  /* prec increase: 1/n*log(N(pmax)) < log(pmax) */
  if (DEBUGLEVEL > 1)
    err_printf("vecan_gchar: need extra prec %ld\n", nbits2extraprec(expu(n)));
  gc = gcharnewprec(gc, prec + nbits2extraprec(expu(n)));
  chilog = gchari_log(gc, chi, &s);

  nf = bnf_get_nf(gchar_get_bnf(gc));
  N = gcharlog_conductor_f(gc,chilog);
  if (typ(N) == t_INT)
    NZ = N;
  else if (typ(N) == t_VEC)
    NZ = gel(N,1);
  else if (typ(N) == t_MAT)
    NZ = gcoeff(N,1,1);
  else
    pari_err_BUG("gchar conductor not an ideal"); /*LCOV_EXCL_LINE*/

  /* FIXME: when many log of many primes are computed:
     - bnfisprincipal may not be improved
     - however we can precompute the logs of generators
       for principal part
     - when galois, should compute one ideal by orbit.
     - when real, clear imaginary part
   */

  u_forprime_init(&iter, 2, n);
  while ((p = u_forprime_next(&iter)))
  {
    GEN L;
    long j;
    int check = !umodiu(NZ,p);
    gp[2] = p;
    L = idealprimedec_limit_norm(nf, gp, BOUND);
    for (j = 1; j < lg(L); j++)
    {
      GEN pr = gel(L, j), ch;
      ulong k, q;
      if (check && idealval(nf, N, pr)) continue;
      /* TODO: extract code and use precom sprk? */
      ch = gchari_eval(gc, chi, pr, 1, chilog, NULL, gen_0, prec);
      q = upr_norm(pr);
      gel(v, q) = gadd(gel(v, q), ch);
      for (k = 2*q; k <= (ulong)n; k += q)
        gel(v, k) = gaddmul(gel(v, k), ch, gel(v, k/q));
    }
  }
  /* weight, could consider shifting s at eval instead */
  if (!gequal0(s))
  {
    GEN ns = dirpowers(n, gneg(s), prec);
    long j;
    for (j = 1; j <= n; j++)
      if (gel(v,j) != gen_0) gel(v, j) = gmul(gel(v,j),gel(ns,j));
  }
  return gerepilecopy(av, v);
}

static GEN
cleanup_vga(GEN vga, long prec)
{
  GEN ind;
  long bitprec, i, l;
  if (!prec) return vga; /* already exact */
  bitprec = bit_accuracy(prec);
  vga = shallowcopy(vga); l = lg(vga);
  for (i = 1; i < l; i++)
  {
    GEN z = gel(vga,i);
    if (typ(z) != t_COMPLEX) continue;
    if (gexpo(gel(z,2)) < -bitprec+20) gel(vga,i) = gel(z,1);
  }
  ind = indexsort(imag_i(vga));
  for (i = 2; i < l; i++)
  {
    GEN z = gel(vga,ind[i]), t;
    if (typ(z) != t_COMPLEX) continue;
    t = imag_i(gel(vga, ind[i-1]));
    if (gexpo(gsub(gel(z,2), t)) < -bitprec+20)
      gel(vga, ind[i]) = mkcomplex(gel(z,1), t);
   }
  for (i = 1; i < l; i++)
  {
    GEN z = gel(vga,i);
    if (typ(z) != t_COMPLEX) continue;
    gel(vga, i) = mkcomplex(gel(z,1), bestappr(gel(z,2), int2n(bitprec/2)));
  }
  return vga;
}

/* TODO: move to lfunutils, use lfunzeta and lfunzetak */
GEN
gchari_lfun(GEN gc, GEN chi, GEN s0)
{
  pari_sp av = avma;
  GEN nf, chilog, s, cond_f, cond_oo, vga_r, vga_c, chiw;
  GEN v_phi, v_arg, sig, k, NN, L;
  long ns, nc, nm, r1, r2;
  nf = bnf_get_nf(gchar_get_bnf(gc));
  ns = gchar_get_ns(gc);
  nc = gchar_get_nc(gc);
  nm = gchar_get_nm(gc);
  nf_get_sign(nf, &r1, &r2);
  chilog = gchari_log(gc, chi, &s);
  s = gadd(s0,s);
  if (!gequal0(gimag(s))) pari_err_IMPL("lfun for gchar with imaginary norm component");
  cond_f =  gcharlog_conductor_f(gc, chilog);
  cond_oo =  gcharlog_conductor_oo(gc, chilog);
  chiw = gchari_shift(gc,chi,s0);

  NN = mulii(idealnorm(nf, cond_f), absi_shallow(nf_get_disc(nf)));
  /* FIXME: shift by s */
  if (equali1(NN)) return gerepileupto(av, lfuncreate(gen_1));
  if (ZV_equal0(chi)) return gerepilecopy(av, lfuncreate(nf));

  /* vga_r = vector(r1,k,I*c[ns+nc+k]-s + cond_oo[k]);
   * vga_c = vector(r2,k,I*c[ns+nc+r1+k]+abs(c[ns+nc+r1+r2+k])/2-s) */
  v_phi = gmul(vecslice(chilog, ns+nc+1, ns+nc+r1+r2), gen_I());
  v_arg = gdivgs(gabs(vecslice(chilog,ns+nc+r1+r2+1,nm),BITS_IN_LONG), 2);
  vga_r = gadd(vecslice(v_phi, 1, r1), cond_oo);
  vga_c = gadd(vecslice(v_phi, r1+1, r1+r2), v_arg);
  sig = shallowconcat1(mkvec3(vga_r,vga_c,gadd(vga_c,const_vec(r2,gen_1))));
  /* TODO: remove cleanup when gammamellinv takes ldata*/
  sig = cleanup_vga(sig, gchar_get_prec(gc));
  k = gen_1;

  if (!gequal0(s))
  {
    long j;
    for (j = 1; j < lg(sig); j++)
      gel(sig, j) = gadd(gel(sig, j), s);
    k = gsub(k, gmulgs(s,2));
  }

#define tag(x,t)  mkvec2(mkvecsmall(t),x)
  L = mkvecn(6, tag(mkvec2(gc,chiw), t_LFUN_HECKE), gen_1, sig, k, NN, gen_0);
  return gerepilecopy(av, L);
}

GEN
lfungchar(GEN gc, GEN chi)
{
  pari_sp av = avma;
  GEN s;
  check_gchar_group(gc);
  chi = gchar_internal(gc, chi, &s);
  return gerepilecopy(av, gchari_lfun(gc, chi, s));
}
