#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_pic
#define lgtJ 18

/* Arithmetic in Zq[t]/(p^e,t^h), Zq=Zp[a]/T(a) TODO optimise!!! */

GEN ZqXn_0(ulong h, long vt, long va)
{
  GEN A,Fq0;
  ulong i;
  A = cgetg(h+2,t_POL);
  A[1] = 0;
  setsigne(A,0);
  setvarn(A,vt);
  Fq0 = pol_0(va);
  for(i=0;i<h;i++)
    gel(A,i+2) = Fq0;
  return A;
}

GEN ZqXn_from_Zq(GEN x, ulong h, long vt)
{
  GEN A,Fq0;
  ulong i;
  long va = varn(x);
  A = cgetg(h+2,t_POL);
  A[1] = 0;
  setsigne(A,1);
  setvarn(A,vt);
  gel(A,2) = gcopy(x);
  if(h==1) return A;
  Fq0 = pol_0(va);
  for(i=1;i<h;i++)
    gel(A,i+2) = Fq0;
  return A;
}

GEN ZqXn_from_Z(GEN x, ulong h, long vt, long va)
{
  return ZqXn_from_Zq(scalarpol(x,va),h,vt);
}

GEN ZqXn_1(ulong h, long vt, long va)
{
  return ZqXn_from_Zq(pol_1(va),h,vt);
}

GEN ZqXn_setprec(GEN A, ulong h2, long vT)
{
  ulong m1,h1,i;
  GEN B;
  m1 = lg(A);
  h1 = m1-2;
  B = cgetg(h2+2,t_POL);
  B[1] = 0;
  setsigne(B,signe(A));
  setvarn(B,varn(A));
  for(i=0;i<h2;i++)
    gel(B,i+2) = i<h1 ? gcopy(gel(A,i+2)) : pol_0(vT);
  return B;
}

GEN ZqXn_redprec(GEN A, ulong h)
{ /* Same as above, but only for h < h_current */
  ulong i;
  GEN B;
  B = cgetg(h+2,t_POL);
  B[1] = 0;
  setsigne(B,signe(A));
  setvarn(B,varn(A));
  for(i=0;i<h;i++)
    gel(B,i+2) = gcopy(gel(A,i+2));
  return B;
}

GEN ZqXn_dropdiv(GEN A, ulong k)
{
  long m,i;
  GEN B;
  m = lg(A)-k;
  B = cgetg(m,t_POL);
  B[1] = 0;
  setsigne(B,signe(A));
  setvarn(B,varn(A));
  for(i=2;i<m;i++)
    gel(B,i) = gcopy(gel(A,i+k));
  return B;
}

GEN ZqXn_red_shallow(GEN A, GEN T, GEN pe)
{
  ulong m,i;
  m = lg(A);
  for(i=2;i<m;i++)
    gel(A,i) = T ? Fq_red(gel(A,i),T,pe) : FpX_red(gel(A,i),pe);
  return A;
}

GEN ZqXn_red(GEN A, GEN T, GEN pe)
{
  GEN B;
  ulong m,i;
  m = lg(A);
  B = cgetg(m,t_POL);
  B[1] = 0;
  setsigne(B,signe(A));
  setvarn(B,varn(A));
  for(i=2;i<m;i++)
    gel(B,i) = T ? Fq_red(gel(A,i),T,pe) : FpX_red(gel(A,i),pe);
  return B;
}

GEN ZqXn_negred(GEN A, GEN pe)
{
  GEN B;
  ulong m,i;
  m = lg(A);
  B = cgetg(m,t_POL);
  B[1] = 0;
  setsigne(B,signe(A));
  setvarn(B,varn(A));
  for(i=2;i<m;i++)
    gel(B,i) = FpX_neg(gel(A,i),pe);
  return B;
}

GEN ZqXn_add(GEN A, GEN B)
{
  GEN C;
  ulong m,i;

  m = lg(A);
  C = cgetg(m,t_POL);
  C[1] = 0;
  setsigne(C,1);
  setvarn(C,varn(A));
  for(i=2;i<m;i++)
    gel(C,i) = ZX_add(gel(A,i),gel(B,i));
  return C;
}

GEN ZqXn_addred(GEN A, GEN B, GEN pe)
{
  GEN C;
  ulong m,i;

  m = lg(A);
  C = cgetg(m,t_POL);
  C[1] = 0;
  setsigne(C,1);
  setvarn(C,varn(A));
  for(i=2;i<m;i++)
    gel(C,i) = FpX_add(gel(A,i),gel(B,i),pe);
  return C;
}

GEN ZqXn_sub(GEN A, GEN B)
{
  GEN C;
  ulong m,i;

  m = lg(A);
  C = cgetg(m,t_POL);
  C[1] = 0;
  setsigne(C,1);
  setvarn(C,varn(A));
  for(i=2;i<m;i++)
    gel(C,i) = ZX_sub(gel(A,i),gel(B,i));
  return C;
}

GEN Zq_ZqXn_mul(GEN A, GEN B, GEN T, GEN pe)
{
  ulong m,j;
  GEN C;

  m = lg(B);
  C = cgetg(m,t_POL);
  C[1] = 0;
  setsigne(C,1);
  setvarn(C,varn(B));
  for(j=2;j<m;j++)
    gel(C,j) = Fq_mul(A,gel(B,j),T,pe);
  return C;
}

GEN ZqXn_mul(GEN A, GEN B, GEN T, GEN pe)
{ // TODO try Karatsuba
  pari_sp av = avma;
  ulong m,h,i,j;
  GEN C,c;

  m = lg(A);
  h = m-2;
  C = cgetg(m,t_POL);
  C[1] = 0;
  setsigne(C,1);
  setvarn(C,varn(A));
  for(j=0;j<h;j++)
  {
    c = ZX_mul(gel(A,2),gel(B,j+2));
    for(i=1;i<=j;i++)
      c = ZX_add(c,ZX_mul(gel(A,i+2),gel(B,j+2-i)));
    gel(C,j+2) = Fq_red(c,T,pe);
  }
  return gerepilecopy(av,C);
}

GEN ZqXn_inv(GEN A, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma;
  GEN Fq0,B,AB,C,c;
  ulong m,h,k,k2,i,j;

  //printf("Into inv\n");
  Fq0 = pol_0(varn(T));
  m = lg(A);
  h = m-2;
  B = cgetg(m,t_POL);
  B[1] = 0;
  setsigne(B,1);
  setvarn(B,varn(A));
  gel(B,2) = ZpXQ_inv(gel(A,2),T,p,e);
  for(j=3;j<m;j++) gel(B,j) = Fq0;
  k = 1; // Inverse correct up to O(t^k)
  // TODO better steps
  while(k<h)
  {
    k2 = k*2;
    if(k2>h) k2=h;
    //printf("k=%lu, k2=%lu\n",k,k2);
    // -A*B mod t^k
    AB = cgetg(k2+2,t_POL);
    AB[1] = 0;
    setsigne(AB,1);
    setvarn(AB,varn(A));
    for(j=0;j<k2;j++)
    {
      c = ZX_mul(gel(B,2),gel(A,j+2));
      for(i=1;i<=j && i<k;i++)
        c = ZX_add(c,ZX_mul(gel(B,i+2),gel(A,j+2-i)));
      c = Fq_red(c,T,pe);
      gel(AB,j+2) = ZX_neg(c);
    }
    // 2-A*B
    gmael(AB,2,2) = addii(gmael(AB,2,2),gen_2);
    // B*(2-A*B)
    C = cgetg(k2+2,t_POL);
    C[1] = 0;
    setsigne(C,1);
    setvarn(C,varn(A));
    for(j=0;j<k2;j++)
    {
      c = ZX_mul(gel(B,2),gel(AB,j+2));
      for(i=1;i<=j && i<k;i++)
        c = ZX_add(c,ZX_mul(gel(B,i+2),gel(AB,j+2-i)));
      gel(C,j+2) = Fq_red(c,T,pe);
    }
    for(j=0;j<k2;j++) gel(B,j+2) = gel(C,j+2);
    k = k2;
  }
  //B = gerepilecopy(av,B);
  //printf("Done inv\n");
  //return B;
  return gerepilecopy(av,B);
}

GEN ZqXn_div(GEN A, GEN B, GEN T, GEN pe, GEN p, long e)
{
  // TODO can do better
  return ZqXn_mul(A,ZqXn_inv(B,T,pe,p,e),T,pe);
}

int
ZqXn_is0mod(GEN x, GEN p)
{
  pari_sp av = avma;
  GEN red;
  if(typ(x)==t_POL)
  {
    if(typ(gel(x,2))==t_POL)
      x = gel(x,2); // Constant coef of series
    red = FpX_red(x,p);
  }
  else
    red = Fp_red(x,p);
  return gc_bool(av,gequal0(red));
}

GEN ZqXn_relFrob(GEN A, GEN FrobMat, GEN T, GEN pe)
{ /* Relative Frob, acts on Zq but not on t */
  GEN B;
  ulong n,i;
  n = lg(A);
  B = cgetg(n,t_POL);
  B[1] = A[1];
  for(i=2;i<n;i++)
    gel(B,i) = ZpXQ_Frob(gel(A,i),FrobMat,T,pe);
  return B;
}

/* Linear algebra over Zq[t]/(p^e,t^h) */

GEN
ZqXnC_setprec(GEN C, ulong h, long vT)
{
  GEN D;
  ulong n,i;
  n = lg(C);
  D = cgetg(n,t_COL);
  for(i=1;i<n;i++)
    gel(D,i) = ZqXn_setprec(gel(C,i),h,vT);
  return D;
}

GEN
ZqXnC_redprec(GEN C, ulong h)
{
  GEN D;
  ulong n,i;
  n = lg(C);
  D = cgetg(n,t_COL);
  for(i=1;i<n;i++)
    gel(D,i) = ZqXn_redprec(gel(C,i),h);
  return D;
}


GEN
ZqXnC_add(GEN A, GEN B)
{
  GEN C;
  ulong n,i;
  n = lg(A);
  C = cgetg(n,t_COL);
  for(i=1;i<n;i++)
    gel(C,i) = ZqXn_add(gel(A,i),gel(B,i));
  return C;
}

GEN
ZqXnC_sub(GEN A, GEN B)
{
  GEN C;
  ulong n,i;
  n = lg(A);
  C = cgetg(n,t_COL);
  for(i=1;i<n;i++)
    gel(C,i) = ZqXn_sub(gel(A,i),gel(B,i));
  return C;
}

GEN
ZqXnC_Zq_mul(GEN C, GEN s, GEN T, GEN pe)
{
  GEN D;
  ulong n,i;
  n = lg(C);
  D = cgetg(n,t_COL);
  for(i=1;i<n;i++)
    gel(D,i) = Zq_ZqXn_mul(s,gel(C,i),T,pe);
  return D;
}

GEN
ZqXn_ZqXnC_mul(GEN s, GEN C, GEN T, GEN pe)
{
  GEN D;
  ulong n,i;
  n = lg(C);
  D = cgetg(n,t_COL);
  for(i=1;i<n;i++)
    gel(D,i) = ZqXn_mul(s,gel(C,i),T,pe);
  return D;
}

GEN
ZqXn_RandVec_1(GEN A, GEN pe)
{
  pari_sp av = avma;
  ulong n,j;
  GEN v;
  n = lg(A);
  v = NULL;
  do{
    for(j=1;j<n;j++)
    {
      if(random_Fl(2))
      {
        if(v==NULL)
        {
          v = gcopy(gel(A,j));
        }
        else
        {
          if(random_Fl(2)) v = ZqXnC_sub(v,gel(A,j));
          else v = ZqXnC_add(v,gel(A,j));
        }
      }
    }
  } while(v==NULL);
  return gerepileupto(av,v);
}

GEN
ZqXn_RandVec(GEN A, GEN T, GEN p, GEN pe)
{
  pari_sp av = avma;
  unsigned long m,n,i,j;
  long dT,vT;
  GEN v,b,c;

  dT = lg(T);
  vT = varn(T);
  n = lg(A);
  m = lg(gel(A,1));
  v = cgetg(m,t_COL);
  for(j=1;j<n;j++)
  {
    b = random_FpX(dT-1,vT,p);
    for(i=1;i<m;i++)
    {
      c = Zq_ZqXn_mul(b,gcoeff(A,i,j),T,pe);
      if(j==1) gel(v,i) = c;
      else gel(v,i) = ZqXn_addred(gel(v,i),c,pe);
    }
    v = gerepilecopy(av,v);
  }
  return v;
}

GEN ZqXnM_to_ZqM_shallow(GEN A)
{
  long m,n,i,j;
  GEN a;
  RgM_dimensions(A,&m,&n);
  a = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(a,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(a,i,j) = gmael3(A,j,i,2);
  }
  return a;
}

GEN ZqXnM_to_ZqM(GEN A)
{
  long m,n,i,j;
  GEN B;
  RgM_dimensions(A,&m,&n);
  B = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(B,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(B,i,j) = gcopy(gmael3(A,j,i,2));
  }
  return B;
}

GEN ZqXnM_setprec(GEN A, ulong h, long vT)
{
  long m,n,i,j;
  GEN B;
  RgM_dimensions(A,&m,&n);
  B = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(B,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(B,i,j) = ZqXn_setprec(gcoeff(A,i,j),h,vT);
  }
  return B;
}

GEN ZqXnM_redprec(GEN A, ulong h)
{ /* Same as above, but only for h< h_current */
  long m,n,i,j;
  GEN B;
  RgM_dimensions(A,&m,&n);
  B = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(B,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(B,i,j) = ZqXn_redprec(gcoeff(A,i,j),h);
  }
  return B;
}

GEN ZqXnM_from_ZqM(GEN A, ulong h, long vT)
{
  long m,n,i,j;
  GEN B;
  RgM_dimensions(A,&m,&n);
  B = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(B,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(B,i,j) = ZqXn_from_Zq(gcoeff(A,i,j),h,vT);
  }
  return B;
}

GEN ZqXnM_add(GEN A, GEN B)
{
  GEN C;
  long m,n,i,j;
  RgM_dimensions(A,&m,&n);
  C = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(C,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(C,i,j) = ZqXn_add(gcoeff(A,i,j),gcoeff(B,i,j));
  }
  return C;
}

GEN ZqXnM_sub(GEN A, GEN B)
{
  GEN C;
  long m,n,i,j;
  RgM_dimensions(A,&m,&n);
  C = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(C,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(C,i,j) = ZqXn_sub(gcoeff(A,i,j),gcoeff(B,i,j));
  }
  return C;
}

GEN ZqXnM_mul(GEN A, GEN B, GEN T, GEN pe)
{ // TODO Strassen?
  pari_sp av = avma;
  long m,n,r,s,i,j,k;
  GEN C,c;

  RgM_dimensions(A,&m,&r);
  RgM_dimensions(B,&s,&n);
  if(n==0) return cgetg(1,t_MAT);
  if(r!=s) pari_err(e_DIM,"ZqXnM_mul");
  if(r==0) return gcopy(B);
  C = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(C,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
    {
      c = ZqXn_mul(gcoeff(A,i,1),gcoeff(B,1,j),T,pe);
      for(k=2;k<=r;k++)
        c = ZqXn_add(c,ZqXn_mul(gcoeff(A,i,k),gcoeff(B,k,j),T,pe));
      s = lg(c);
      for(k=2;k<s;k++)
        gel(c,k) = FpX_red(gel(c,k),pe);
      gcoeff(C,i,j) = c;
    }
  }
  return gerepilecopy(av,C);
}

GEN ZqXnM_ZqXnC_mul(GEN A, GEN B, GEN T, GEN pe)
{ // TODO Strassen?
  pari_sp av = avma;
  long m,n,s,i,k;
  GEN C,c;

  RgM_dimensions(A,&m,&n);
  s = lg(B)-1;
  if(n!=s) pari_err(e_DIM,"ZqXnM_ZqXnC_mul");
  if(n==0) return gcopy(B);
  C = cgetg(m+1,t_COL);
  for(i=1;i<=m;i++)
  {
    c = ZqXn_mul(gcoeff(A,i,1),gel(B,1),T,pe);
    for(k=2;k<=n;k++)
      c = ZqXn_add(c,ZqXn_mul(gcoeff(A,i,k),gel(B,k),T,pe));
    s = lg(c);
    for(k=2;k<s;k++)
      gel(c,k) = FpX_red(gel(c,k),pe);
    gel(C,i) = c;
  }
  return gerepilecopy(av,C);
}

GEN ZqXnM_ZqXn_mul(GEN A, GEN b, GEN T, GEN pe)
{
  GEN C;
  long m,n,i,j;
  RgM_dimensions(A,&m,&n);
  C = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(C,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(C,i,j) = ZqXn_mul(gcoeff(A,i,j),b,T,pe);
  }
  return C;
}

GEN
ZqXnM_inv(GEN A, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma, avk;
  ulong n,i,j,k;
  ulong h,vt,va;
  GEN B,col,l,col2,C;
  GEN I;
  GEN R0,R1;

  n = lg(A)-1;
  if(n==0) return cgetg(1,t_MAT);
  I = cgetg(n+1,t_VECSMALL); /* Vector of permutation of rows */
  for(i=1;i<=n;i++) I[i] = i;
  B = gcoeff(A,1,1);
  h = lg(B)-2;
  vt = varn(B);
  va = varn(gel(B,2));
  R0 = ZqXn_0(h,vt,va);
  R1 = ZqXn_1(h,vt,va);
  B = cgetg(n+1,t_MAT);
  /* Phase 1: to U1 form */
  for(k=n;k;k--)
  {
    avk = avma;
    col = cgetg(2*n+1,t_COL);
    /* Cols n to k+1 processed, now do col k */
    for(i=1;i<=n;i++)
    {
      gel(col,i) = gcoeff(A,i,k);
      gel(col,i+n) = i==k? R1 : R0;
    }
    /* Col is now vcat Ak,Ik */
    /* The last k cols of B are known */
    /* Upper part of B is UT1, lower part is LT */
    /* Reduce Ck using Cj for j=n..k+1 */
    /* Actually only need coeffs for i<k and i>=n+k */
    for(j=n;j>k;j--)
    {
      l = ZqXn_negred((gel(col,I[j])),pe);
      /* Ck += l*Cj */
      for(i=1;i<=j;i++)
        gel(col,I[i]) = ZqXn_add(gel(col,I[i]),ZqXn_mul(l,gcoeff(B,I[i],j),T,pe));
      for(i=n+j;i<=2*n;i++)
        gel(col,i) = ZqXn_add(gel(col,i),ZqXn_mul(l,gcoeff(B,i,j),T,pe));
      col = gerepileupto(avk,col);
    }
    for(i=1;i<=k;i++) gel(col,I[i]) = ZqXn_red(gel(col,I[i]),NULL,pe);
    for(i=n+k+1;i<=2*n;i++) gel(col,i) = ZqXn_red_shallow(gel(col,i),NULL,pe);
    /* Now coefs k+1..n of col are 0 */
    /* Find pivot above k (hopefully k) */
    for(i=k;i;i--)
    {
      l = gel(col,I[i]);
      if(ZqXn_is0mod(l,p)==0) break;
    }
    if(i!=k)
    {
      j = I[k]; I[k] = I[i]; I[i] = j;
    }
    /* Divide by pivot */
    l = ZqXn_inv(l,T,pe,p,e);
    col2 = cgetg(2*n+1,t_COL);
    for(i=1;i<k;i++) gel(col2,I[i]) = ZqXn_mul(gel(col,I[i]),l,T,pe);
    gel(col2,I[k]) = R1;
    for(i=k+1;i<=n;i++) gel(col2,I[i]) = R0;
    for(i=n+1;i<n+k;i++) gel(col2,i) = R0;
    for(i=n+k;i<=2*n;i++) gel(col2,i) = ZqXn_mul(gel(col,i),l,T,pe);
    gel(B,k) = gerepileupto(avk,col2);
  }
  /* Phase 2 : to 1 form */
  /* Upper B is UT1, imagine we reduce it to 1 but do not actually do it */
  /* Then the inverse is lower B with cols permuted by I */
  C = cgetg(n+1,t_MAT);
  gel(C,I[1]) = cgetg(n+1,t_COL);
  for(i=1;i<=n;i++)
    gcoeff(C,i,I[1]) = gcoeff(B,i+n,1);
  for(k=2;k<=n;k++)
  {
    avk = avma;
    col = cgetg(n+1,t_COL);
    for(i=1;i<=n;i++)
      gel(col,i) = gcoeff(B,i+n,k);
    for(j=1;j<k;j++)
    {
      l = ZqXn_negred(gcoeff(B,I[j],k),pe);
      /* Ck += l*Cj */
      for(i=(k==2?j:1);i<=n;i++) gel(col,i) = ZqXn_add(gel(col,i),ZqXn_mul(l,gcoeff(C,i,I[j]),T,pe));
      col = gerepileupto(avk,col);
    }
    col2 = cgetg(n+1,t_COL);
    for(i=1;i<=n;i++) gel(col2,i) = ZqXn_red(gel(col,i),NULL,pe);
    gel(C,I[k]) = gerepileupto(avk,col2);
  }
  /* Ensure C is suitable for gerepile */
  for(i=1;i<=n;i++)
    gcoeff(C,i,I[1]) = gcopy(gcoeff(C,i,I[1]));
  return gerepileupto(av,C);
}

GEN ZqXnM_image(GEN A, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN Ared,I,B;
  ulong r,i;
  Ared = ZqXnM_to_ZqM(A);
  I = gel(FqM_indexrank(Ared,T,p),2);
  r = lg(I);
  B = cgetg(r,t_MAT);
  for(i=1;i<r;i++)
    gel(B,i) = gcopy(gel(A,I[i]));
  return gerepileupto(av,B);
}

GEN
ZqXnM_ker(GEN A, GEN T, GEN pe, GEN p, long e)
{ /* Assumes good red, i.e. the rank does not decrease mod p */
  pari_sp av = avma, av1;
  GEN Ared,IJ,I,J,J1,P,A1,A2,B,K;
  ulong h,r,i,j;
  long m,n,vt,va;
  GEN R0,Rm1;
  RgM_dimensions(A,&m,&n);
  if(m*n==0)
    pari_err(e_IMPL,"Size zero case");
  vt = varn(gcoeff(A,1,1));
  va = varn(T);
  h = lg(gcoeff(A,1,1))-2;
  Ared = cgetg(n+1,t_MAT); /* Mat of const coefs of series */
  for(j=1;j<=n;j++)
  {
    gel(Ared,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(Ared,i,j) = gmael3(A,j,i,2);
  }
  if(h==1) /* Constant series, call ZqM_ker */
  {
    Ared = ZqM_ker(Ared,T,pe,p,e);
    /* Turn constants into constant series */
    r = lg(Ared);
    K = cgetg(r,t_MAT);
    for(j=1;j<r;j++)
    {
      gel(K,j) = cgetg(n+1,t_COL);
      for(i=1;i<=n;i++)
        gcoeff(K,i,j) = ZqXn_from_Zq(gcoeff(Ared,i,j),1,vt);
    }
    return gerepileupto(av,K);
  }
  IJ = FqM_indexrank(Ared,T,p);
  I = gel(IJ,1); /* Rows spanning the eqns, ignore others (good red) */
  J = gel(IJ,2); /* Cols forming invertible block */
  r = lg(J)-1;
  J1 = VecSmallCompl(J,n); /* Other cols */
  P = cgetg(n+1,t_VECSMALL);
  for(j=1;j<=r;j++) P[j] = J[j];
  for(j=1;j<=n-r;j++) P[r+j] = J1[j];
  av1 = avma;
  A1 = cgetg(r+1,t_MAT); /* Invertible block */
  for(j=1;j<=r;j++)
  {
    gel(A1,j) = cgetg(r+1,t_COL);
    for(i=1;i<=r;i++) gcoeff(A1,i,j) = gcoeff(A,I[i],P[j]);
  }
  B = gerepileupto(av1,ZqXnM_inv(A1,T,pe,p,e));
  A2 = cgetg(n-r+1,t_MAT); /* Other block */
  for(j=1;j<=n-r;j++)
  {
    gel(A2,j) = cgetg(r+1,t_COL);
    for(i=1;i<=r;i++) gcoeff(A2,i,j) = gcoeff(A,I[i],P[j+r]);
  }
  /* K = vcat of A1^-1*A2, -Id_{n-r}, with perm P^-1 of rows */
  B = gerepileupto(av1,ZqXnM_mul(B,A2,T,pe));
  R0 = ZqXn_0(h,vt,va);
  Rm1 = ZqXn_from_Z(gen_m1,h,vt,va);
  K = cgetg(n-r+1,t_MAT);
  for(j=1;j<=n-r;j++)
  {
    gel(K,j) = cgetg(n+1,t_COL);
    for(i=1;i<=r;i++)
      gcoeff(K,P[i],j) = gcoeff(B,i,j);
    for(i=r+1;i<=n;i++)
      gcoeff(K,P[i],j) = j+r==i?Rm1:R0;
  }
  return gerepilecopy(av,K);
}

GEN
ZqXnM_eqn(GEN A, GEN T, GEN pe, GEN p, long e)
{ /* Assumes good red, i.e. the rank does not decrease mod p */
  pari_sp av = avma, av1;
  GEN Ared,IJ,I,J,I1,P,A1,A2,B,K;
  ulong h,r,i,j;
  long m,n,vt,va;
  GEN R0,Rm1;
  RgM_dimensions(A,&m,&n);
  if(m*n==0)
    pari_err(e_IMPL,"Size zero case");
  vt = varn(gcoeff(A,1,1));
  va = varn(T);
  h = lg(gcoeff(A,1,1))-2;
  Ared = cgetg(n+1,t_MAT); /* Mat of const coefs of series */
  for(j=1;j<=n;j++)
  {
    gel(Ared,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(Ared,i,j) = gmael3(A,j,i,2);
  }
  if(h==1) /* Constant series, call ZqM_eqn */
  {
    Ared = ZqM_eqn(Ared,T,pe,p,e);
    /* Turn constants into constant series */
     RgM_dimensions(Ared,&m,&n);
    K = cgetg(n+1,t_MAT);
    for(j=1;j<=n;j++)
    {
      gel(K,j) = cgetg(m+1,t_COL);
      for(i=1;i<=m;i++)
        gcoeff(K,i,j) = ZqXn_from_Zq(gcoeff(Ared,i,j),1,vt);
    }
    return gerepileupto(av,K);
  }
  IJ = FqM_indexrank(Ared,T,p);
  I = gel(IJ,1); /* Rows forming invertible block */
  J = gel(IJ,2); /* Columns spanning the space, ignore others (good red) */
  r = lg(I)-1;
  I1 = VecSmallCompl(I,m); /* Other rows */
  P = cgetg(n+1,t_VECSMALL); /* First I then I1 */
  for(i=1;i<=r;i++) P[i] = I[i];
  for(i=1;i<=m-r;i++) P[r+i] = I1[i];
  av1 = avma;
  A1 = cgetg(r+1,t_MAT); /* Invertible block */
  for(j=1;j<=r;j++)
  {
    gel(A1,j) = cgetg(r+1,t_COL);
    for(i=1;i<=r;i++) gcoeff(A1,i,j) = gcoeff(A,P[i],J[j]);
  }
  B = gerepileupto(av1,ZqXnM_inv(A1,T,pe,p,e));
  A2 = cgetg(r+1,t_MAT); /* Other block */
  for(j=1;j<=r;j++)
  {
    gel(A2,j) = cgetg(m-r+1,t_COL);
    for(i=1;i<=m-r;i++) gcoeff(A2,i,j) = gcoeff(A,P[i+r],J[j]);
  }
  /* E = hcat of A2*A1^-1, -Id_{n-r}, with perm P^-1 of cols*/
  B = gerepileupto(av1,ZqXnM_mul(A2,B,T,pe));
  R0 = ZqXn_0(h,vt,va);
  Rm1 = ZqXn_from_Z(gen_m1,h,vt,va);
  K = cgetg(m+1,t_MAT);
  for(j=1;j<=r;j++)
    gel(K,P[j]) = gel(B,j);
  for(j=r+1;j<=m;j++)
  {
    gel(K,P[j]) = cgetg(m-r+1,t_COL);
    for(i=1;i<=m-r;i++) gcoeff(K,i,P[j]) = i+r==j?Rm1:R0;
  }
  return gerepilecopy(av,K);
}

GEN
ZqXn_Subspace_normalize(GEN V, GEN I, GEN T, GEN pe, GEN p, long e, long drop)
{ /* V represents a subspace, I list of rows. Change basis so that I-block of V==1. */
  pari_sp av = avma;
  GEN P;
  ulong n,i,j;
  n = lg(V);
  P = cgetg(n,t_MAT);
  for(j=1;j<n;j++)
  {
    gel(P,j) = cgetg(n,t_COL);
    for(i=1;i<n;i++)
      gcoeff(P,i,j) = gcoeff(V,I[i],j);
  }
  P = ZqXnM_inv(P,T,pe,p,e);
  V = ZqXnM_mul(V,P,T,pe);
  if(drop)
  {
    V = RgM_drop_rows(V,I);
    return gerepilecopy(av,V);
  }
  else return gerepileupto(av,V);
}

/* Picard group over Zq[t]/(p^e,t^h) */

GEN
tDivMul(GEN f, GEN W, GEN T, GEN pe)
{ /* { fw | w in W } */
  ulong nW,nZ,i,j;
  GEN fW;
  nW = lg(W);
  nZ = lg(f);
  fW = cgetg(nW,t_MAT);
  for(j=1;j<nW;j++)
  {
    gel(fW,j) = cgetg(nZ,t_COL);
    for(i=1;i<nZ;i++)
      gcoeff(fW,i,j) = ZqXn_mul(gel(f,i),gcoeff(W,i,j),T,pe);
  }
  return fW;
}

GEN
tDivAdd(GEN WA, GEN WB, ulong d, GEN T, GEN p, GEN pe, ulong excess)
{ /* Does products s*t, with s=sum n_i s_i, n_i = 0 50%, -1 25%, +1 25%; similarly for t */
  /* Fails from time to time but overall good speedup */
  pari_sp av=avma;
  ulong nZ,j,P,r;
  GEN WAB,s,t,st;
  nZ = lg(gel(WA,1));
  while(1)
  {
    WAB = cgetg(d+excess+1,t_MAT);
    for(j=1;j<=d+excess;j++)
    {
      s = ZqXn_RandVec_1(WA,pe); /* random fn in WA */
      t = ZqXn_RandVec_1(WB,pe); /* random fn in WB */
      st = cgetg(nZ,t_COL); /* Product */
      for(P=1;P<nZ;P++)
      {
        gel(st,P) = ZqXn_mul(gel(s,P),gel(t,P),T,pe);
      }
      gel(WAB,j) = st;
    }
    WAB = ZqXnM_image(WAB,T,p);
    r = lg(WAB)-1;
    if(r==d)
      return gerepileupto(av,WAB);
    if(DEBUGLEVEL>=4) err_printf("divadd(%lu/%lu)",r,d);
    excess++;
    set_avma(av);
  }
}

GEN
tDivSub(GEN WA, GEN WB, GEN KV, ulong d, GEN T, GEN p, long e, GEN pe, ulong nIGS)
{ /* { v in Ker KV | v*WA c WB } */
  pari_sp av1,av = avma;
  ulong nZ,P,nE,E,nV,nB,n,r;
  GEN KB,K,s,res;
  nZ = lg(KV);
  nV = lg(gel(KV,1))-1;
  KB = ZqXnM_eqn(WB,T,pe,p,e);
  nB = lg(gel(KB,1))-1;
  /* Prepare a mat K of size a v stack of KV + nIGS copies of KB */
  /* and copy KV at the top */
  nE = nV + nIGS*nB;
  K = cgetg(nZ,t_MAT);
  for(P=1;P<nZ;P++)
  {
    gel(K,P) = cgetg(nE+1,t_COL);
    for(E=1;E<=nV;E++)
      gcoeff(K,E,P) = gcoeff(KV,E,P);
  }
  av1 = avma;
  while(1)
  {
    /* nIGS times, take rand s in WA, and stack s.KB down K */
    for(n=1;n<=nIGS;n++)
    {
      s = ZqXn_RandVec(WA,T,p,pe); /* Note: RandVec_1 would be slower here */
      for(E=1;E<=nB;E++)
      {
        for(P=1;P<nZ;P++)
          gcoeff(K,nV+(n-1)*nB+E,P) = ZqXn_mul(gel(s,P),gcoeff(KB,E,P),T,pe);
      }
    }
    res = ZqXnM_ker(K,T,pe,p,e);
    r = lg(res)-1;
    if(r==d) return gerepileupto(av,res);
    if(DEBUGLEVEL>=4) err_printf("divsub(%lu/%lu)",r,d);
    set_avma(av1);
  }
}

GEN
tDivSub_dimval(GEN WA, GEN WB, long dim, GEN KV, GEN T, GEN p, long e, GEN pe)
{ /* Finds accuracy at which DivSub(WA,WB) has dimension dim. in the form vp(t^0), vp(t^1), ... */
  pari_sp av = avma;
  ulong nZ,P,nE,E,nV,nA,nB,n,h,i,j,v;
  GEN KB,K,L,Lv,res;
  h = lg(gcoeff(KV,1,1))-2; /* Ambient t-adic prec */
  nZ = lg(KV);
  nV = lg(gel(KV,1))-1;
  KB = ZqXnM_eqn(WB,T,pe,p,e);
  nB = lg(gel(KB,1))-1;
  nA = lg(WA)-1;

  /* Prepare a mat K of size a v stack of KV + nA copies of KB */
  /* and copy KV at the top */
  nE = nV + nA*nB; /* K of dim nE * nZ */
  K = cgetg(nZ,t_MAT);
  for(P=1;P<nZ;P++)
  {
    gel(K,P) = cgetg(nE+1,t_COL);
    for(E=1;E<=nV;E++)
      gcoeff(K,E,P) = gcoeff(KV,E,P);
  }
  /* Stack a.KB down K for a in basis of WA */
  for(n=1;n<=nA;n++)
  {
    for(E=1;E<=nB;E++)
    {
      for(P=1;P<nZ;P++)
        gcoeff(K,nV+(n-1)*nB+E,P) = ZqXn_mul(gcoeff(WA,P,n),gcoeff(KB,E,P),T,pe);
    }
  }
  L = ZqXnM_ker(K,T,pe,p,e);
  /* Is L even of the right dim mod p ? */
  if(lg(L)-1 != dim)
    return gc_const(av,gen_0);
  /* Now L of size nZ * dim */
  L = ZqXnM_mul(K,L,T,pe);
  /* Now L of size nE * dim */
  /* if(gequal0(L)) TODO never detected, need to write proper function
  {
    avma = av;
    res = cgetg(h+1,t_VECSMALL);
    for(v=0;v<h;i++)
      res[v+1] = (ulong)e;
    return res;
  }*/
  res = cgetg(h+1,t_VECSMALL);
  Lv = cgetg(dim+1,t_MAT);
  for(j=1;j<=dim;j++)
    gel(Lv,j) = cgetg(nE+1,t_COL);
  for(v=0;v<h;v++)
  { /* Lv <- L[t^v] */
    for(j=1;j<=dim;j++)
    {
      for(i=1;i<=nE;i++)
        gcoeff(Lv,i,j) = gmael3(L,j,i,v+2);
    }
    res[v+1] = gequal0(Lv) ? e : gvaluation(Lv,p);
  }
  return gerepileupto(av,res);
}

int val_allOK(GEN x, ulong h, long e)
{ /* Analyse the output of dimval */
  ulong i;
  if(gequal0(x))
    return 0;
  if(gequal1(x))
    return 1;
  for(i=1;i<=h;i++)
  {
    if(x[i]!=e) return 0;
  }
  return 1;
}

GEN
tPicNeg(GEN J, GEN W, long flag)
{ /* flag: 1: choose s randomly, 2: also return s */
  /* TODO use auts when possible */
  pari_sp av = avma;
  GEN s,sV,WN,res;
  GEN V,KV,T,p,pe;
  long g,d0,e;

  V = JgetV(J,2);
  KV = JgetKV(J,2);
  JgetTpe(J,&T,&pe,&p,&e);
  g = Jgetg(J);
  d0 = Jgetd0(J);

  /* (s) = -2D_0-D-N */
  if(flag & 1) s = ZqXn_RandVec(W,T,p,pe);
  else s = gel(W,1);
  sV = tDivMul(s,V,T,pe); /* L(4D_0-D-N) */
  WN = tDivSub(W,sV,KV,d0+1-g,T,p,e,pe,2); /* L(2D_0-N) */

  if(flag & 2)
  {
    res = cgetg(3,t_VEC);
    gel(res,1) = gcopy(WN);
    gel(res,2) = gcopy(s);
    return gerepileupto(av,res);
  }
  return gerepileupto(av,WN);
}

GEN
tPicRand(GEN J, GEN randseed)
{
  pari_sp av = avma;
  ulong nS,nZ,nV;
  ulong i,j;
  long e;
  GEN T,p,pe,U,V;
  GEN S,K;

  if(randseed && !gequal0(randseed))
    setrand(randseed);

  if(random_Fl(2)==0 && !gequal0(U=JgetEvalData(J)))
  { /* In 1/2 cases, use EvalData, if present */
    U = gel(U,1+random_Fl(2));
    V = gel(U,1+random_Fl(lg(U)-1));
    nS = Jgetg(J);
  }
  else
  {
    V = JgetV(J,2);
    nS = Jgetd0(J);
  }
  JgetTpe(J,&T,&pe,&p,&e);
  nV = lg(V);
  nZ = lg(gel(V,1));

  K = cgetg(nV,t_MAT);
  S = rand_subset(nZ-1,nS);
  for(j=1;j<nV;j++)
  {
    gel(K,j) = cgetg(nS+1,t_COL);
    for(i=1;i<=nS;i++)
      gcoeff(K,i,j) = gcoeff(V,S[i],j);
  }
  K = ZqXnM_ker(K,T,pe,p,e);
  K = ZqXnM_mul(V,K,T,pe);
  return gerepileupto(av,K);
}

GEN
tPicMember_val(GEN J, GEN W)
{
  pari_sp av = avma;
  GEN T,pe,p,w,V,wV,KV,res;
  long e;

  JgetTpe(J,&T,&pe,&p,&e);
  V = JgetV(J,2);
  KV = JgetKV(J,2);

  do
    w = ZqXn_RandVec_1(W,pe);
  while(gequal0(w));
  wV = tDivMul(w,V,T,pe);
  res = tDivSub_dimval(W,wV,lg(W)-1,KV,T,p,e,pe);
  return gerepileupto(av,res);
}

int
tPicMember(GEN J, GEN W)
{
  pari_sp av = avma;
  return gc_bool(av,val_allOK(tPicMember_val(J,W),Jgeth(J),Jgete(J)));
}

GEN
tPicEq_val(GEN J, GEN WA, GEN WB)
{
  pari_sp av = avma;
  long e;
  GEN s,sWB,KV,T,p,pe,res;

  JgetTpe(J,&T,&pe,&p,&e);
  KV = JgetKV(J,2);

  /* Take s in WA: (s) = -2D0+A+A1 */
  s = gel(WA,1);
  /* Compute s*WB = L(4D0-A-B-A1) */
  sWB = tDivMul(s,WB,T,pe);
  /* Find { v in V | v*WA c s*WB } = L(2D0-B-A1) */
  /* This space is nontrivial iff. A~B */
  res = tDivSub_dimval(WA,sWB,1,KV,T,p,e,pe);
  return gerepileupto(av,res);
}

int
tPicEq(GEN J, GEN WA, GEN WB)
{
  pari_sp av = avma;
  return gc_bool(av,val_allOK(tPicEq_val(J,WA,WB),Jgeth(J),Jgete(J)));
}

GEN
tPicIsZero_val(GEN J, GEN W)
{
  pari_sp av = avma;
  long e;
  GEN V1,KV1,T,p,pe,res;

  JgetTpe(J,&T,&pe,&p,&e);
  V1 = JgetV(J,1);
  KV1 = JgetKV(J,1);

  res = tDivSub_dimval(V1,W,1,KV1,T,p,e,pe);
  return gerepileupto(av,res);
}

int
tPicIsZero(GEN J, GEN W)
{
  pari_sp av = avma;
  return gc_bool(av,val_allOK(tPicIsZero_val(J,W),Jgeth(J),Jgete(J)));
}

GEN
tPicChord(GEN J, GEN WA, GEN WB, long flag)
{ /* flag: 1: choose s randomly, 2: also return s */
  pari_sp av = avma;
  GEN WAWB,WAB,s,sV,WC,res;
  GEN V,KV,KV3,V1,T,p,pe;
  long g,d0,e;

  V = JgetV(J,2);
  KV = JgetKV(J,2);
  KV3 = JgetKV(J,3);
  V1 = JgetV(J,1);
  JgetTpe(J,&T,&pe,&p,&e);
  g = Jgetg(J);
  d0 = Jgetd0(J);

  /* L(4D0-A-B) */
  WAWB = tDivAdd(WA,WB,2*d0+1-g,T,p,pe,0);
  /* L(3D0-A-B) */
  WAB = tDivSub(V1,WAWB,KV3,d0+1-g,T,p,e,pe,2);
  if(gc_needed(av,1)) WAB = gerepileupto(av,WAB);
  if(flag & 1) s = ZqXn_RandVec(WAB,T,p,pe);
  else s = gel(WAB,1);
  /* s in WB: (s) = -3D0+A+B+C */
  /* L(5D0-A-B-C) */
  sV = tDivMul(s,V,T,pe);
  /* L(2D0-C) */
  WC = tDivSub(WAB,sV,KV,d0+1-g,T,p,e,pe,2);

  if(flag & 2)
  {
    res = cgetg(3,t_VEC);
    gel(res,1) = gcopy(WC);
    gel(res,2) = gcopy(s);
    return gerepileupto(av,res);
  }
  else
  {
    return gerepileupto(av,WC);
  }
}

GEN
tPicAdd(GEN J, GEN WA, GEN WB)
{
  pari_sp av = avma;
  GEN W;
  W = tPicChord(J,WA,WB,0);
  W = tPicNeg(J,W,0);
  return gerepileupto(av,W);
}

GEN
tPicSub(GEN J, GEN WA, GEN WB)
{
  pari_sp av = avma;
  GEN W;
  W = tPicNeg(J,WB,0);
  W = tPicChord(J,W,WA,0);
  return gerepileupto(av,W);
}

GEN
tPicMul(GEN J, GEN W, GEN n, long flag)
{ /* flag: 2: sign matters, 1: pass to PicChord and PicNeg */
  pari_sp av = avma;
  GEN C,Wlist,WA,WB;
  ulong nC,i;
  long a,b;

  if(gequal0(n)) return gcopy(JgetW0(J));
  if(gequal(n,gen_1)) return gcopy(W);
  C = AddFlipChain(n,flag&2);
  nC = lg(C);
  if(DEBUGLEVEL>=2)
  {
    if(flag&2)
      pari_printf("picmul by %Ps in %lu steps\n",n,nC-2);
    else
      pari_printf("picmul by +-%Ps in %lu steps\n",n,nC-2);
  }
  Wlist = cgetg(nC,t_VEC);
  gel(Wlist,1) = W;
  for(i=2;i<nC;i++)
  {
    a = gmael(C,i,2)[1];
    b = gmael(C,i,2)[2];
    if(a)
    {
      WA = gel(Wlist,a);
      if(b)
      {
        WB = gel(Wlist,b);
        gel(Wlist,i) = tPicChord(J,WA,WB,(i==nC-1)&&(flag&1));
      }
      else gel(Wlist,i) = tPicNeg(J,WA,(i==nC-1)&&(flag&1));
    }
    else gel(Wlist,i) = b?tPicNeg(J,gel(Wlist,b),(i==nC-1)&&(flag&1)):gcopy(JgetW0(J));
    /* Does not respect flag if a==b==0 but this is not supposed to happen */
  }
  return gerepileupto(av,gel(Wlist,nC-1));
}

GEN
tPicFrob(GEN J, GEN W)
{ /* Relative Frobenius: acts on Zq but not on t */
  GEN W2,T,pe,FrobMat,FrobCyc;
  ulong nW,nZ,i,j;

  T = JgetT(J);
  pe = Jgetpe(J);
  FrobMat = JgetFrobMat(J);
  FrobCyc = JgetFrobCyc(J);
  nW = lg(W);
  nZ = lg(FrobCyc);

  W2 = cgetg(nW,t_MAT);
  for(j=1;j<nW;j++)
  {
    gel(W2,j) = cgetg(nZ,t_COL);
    for(i=1;i<nZ;i++)
      gcoeff(W2,FrobCyc[i],j) = ZqXn_relFrob(gcoeff(W,i,j),FrobMat,T,pe);
  }
  return W2;
}

GEN
tPicFrobPow(GEN J, GEN W, long n)
{
  pari_sp av = avma;
  GEN W2,T,pe,M,cyc;
  ulong a,m,nW,nZ,i,j;

  T = JgetT(J);
  a = degpol(T);
  m = umodsu(n,a);
  if(m==0) return gcopy(W);
  if(m==1) return tPicFrob(J,W);
  pe = Jgetpe(J);
  M = FpM_powu(JgetFrobMat(J),m,pe);
  cyc = perm_powu(JgetFrobCyc(J),m);
  nW = lg(W);
  nZ = lg(cyc);

  W2 = cgetg(nW,t_MAT);
  for(j=1;j<nW;j++)
  {
    gel(W2,j) = cgetg(nZ,t_COL);
    for(i=1;i<nZ;i++)
      gcoeff(W2,cyc[i],j) = ZqXn_relFrob(gcoeff(W,i,j),M,T,pe);
  }
  return gerepileupto(av,W2);
}

GEN
tPicFrobPoly(GEN J, GEN W, GEN F)
{
  pari_sp av = avma;
  ulong d,i;
  GEN n,FW,res;

  if(gequal0(F))
    return gcopy(JgetW0(J));
  d = degree(F);
  FW = W;
  n = truecoeff(F,0);
  if(d&1L) n = negi(n);
  res = tPicMul(J,W,n,2);
  for(i=1;i<=d;i++)
  {
    FW = tPicFrob(J,FW);
    n = truecoeff(F,i);
    if((d+1-i)&1L) n = negi(n);
    res = tPicChord(J,res,tPicMul(J,FW,n,2),0);
  }
  return gerepileupto(av,res);
}

GEN
tPicIsTors_val(GEN J, GEN W, GEN F)
{
  pari_sp av = avma;
  GEN res;
  if(type(F)==t_INT)
    W = tPicFrobMul(J,W,F,0);
  else
    W = tPicFrobPoly(J,W,F);
  res = tPicIsZero_val(J,W);
  return gerepileupto(av,res);
}

int
tPicIsTors(GEN J, GEN W, GEN F)
{
  pari_sp av = avma;
  W = tPicFrobPoly(J,W,F);
  return gc_bool(av,val_allOK(tPicIsZero_val(J,W),Jgeth(J),Jgete(J)));
}

GEN
tPicChart(GEN J, GEN W, ulong P0, GEN P1) /* /!\ Not Galois-equivariant ! */
{
  pari_sp av = avma;
  ulong d0,g,n1,nZ,nW;
  ulong j,P;
  long e;
  GEN V,KV,T,p,pe;
  GEN K,col,s,sV,U;

  g = Jgetg(J);
  d0 = Jgetd0(J);
  n1 = d0-g;
  V = JgetV(J,2);
  KV = JgetKV(J,2);
  nZ = lg(gel(V,1))-1;
  nW = lg(W)-1;
  JgetTpe(J,&T,&pe,&p,&e);

  K = cgetg(nW+1,t_MAT);
  for(j=1;j<=nW;j++)
  { /* C = sum of pts P0+1, ..., P0+d0-g */
    col = cgetg(n1+1,t_COL);
    for(P=1;P<=n1;P++) gel(col,P) = gcoeff(W,P+P0,j);
    gel(K,j) = col;
  }
  K = ZqXnM_ker(K,T,pe,p,e);
  if(lg(K)!=2)
  {
    pari_printf("Genericity 1 failed in PicChart\n");
    return gc_NULL(av);
  }
  s = ZqXnM_ZqXnC_mul(W,gel(K,1),T,pe); /* Generator of L(2D0-D-C) */

  sV = tDivMul(s,V,T,pe); /* L(4D0-D-C-E_D), deg E_D = g */
  U = tDivSub(W,sV,KV,d0+1-g,T,p,e,pe,2); /* L(2D0-C-E_D) */
  for(j=1;j<=nW;j++) /* Remove zero rows */
  {
    for(P=1;P<=n1;P++) gcoeff(U,P0+P,j) = gcoeff(U,P0+n1+P,j);
    setlg(gel(U,j),nZ-n1+1);
  }
  if(P1)
    U = ZqXn_Subspace_normalize(U,P1,T,pe,p,e,1);
  return gerepilecopy(av,mat2col0(U));
}


/* Construction of Jacobian */

GEN tFnEvalAt(GEN F, GEN P, GEN vars, GEN T, GEN pe, GEN p, long e, ulong h)
{ /* Coords of P can be (independently) Zq or ZqXn */
  pari_sp av;
  GEN N,D,u;
  long i,n,v,a;
  //pari_printf("Eval %Ps at %Ps mod %Ps, %Ps^%ld=%Ps, t^%lu\n",F,P,T,p,e,pe,h);
  switch(typ(F))
  {
    case t_INT:
    case t_FRAC:
      av = avma;
      //printf("type constant\n");
      N = Rg_to_Fp(F,pe);
      N = ZqXn_from_Z(N,h,vars[3],varn(T));
      return gerepileupto(av,N);
    case t_RFRAC:
      av = avma;
      N = tFnEvalAt(gel(F,1),P,vars,T,pe,p,e,h);
      D = tFnEvalAt(gel(F,2),P,vars,T,pe,p,e,h);
      return gerepileupto(av,ZqXn_div(N,D,T,pe,p,e));
    case t_POL:
      n = degpol(F);
      //v = varn(F); // TODO debug
      //printf("Type pol, deg %ld, var %ld\n",n,v);
      if(n<0) return ZqXn_0(h,vars[3],varn(T));
      v = varn(F);
      if(v==vars[3]) /* Rg[t] */
      {
        a = varn(T);
        N = cgetg(h+2,t_POL);
        N[1] = 0;
        setsigne(N,1);
        setvarn(N,v);
        n = degpol(F);
        for(i=0;i<h;i++)
          gel(N,i+2) = i<=n ? scalarpol(Rg_to_Fp(gel(F,i+2),pe),a) : pol_0(a);
        return N;
      }
      av = avma;
      if(v==vars[2])
      {
        u = gel(P,2);
      }
      else
      {
        if(v!=vars[1])
          pari_err(e_MISC,"Incorrect variable in tFnEvalAt");
        u = gel(P,1);
      }
      if(varn(u) != vars[3]) u = ZqXn_from_Zq(u,h,vars[3]); /* In case u is just a Zq */
      N = tFnEvalAt(gel(F,n+2),P,vars,T,pe,p,e,h);
      for(i=n-1;i>=0;i--)
      {
        N = ZqXn_mul(N,u,T,pe);
        N = ZqXn_addred(N,tFnEvalAt(gel(F,i+2),P,vars,T,pe,p,e,h),pe); // TODO do not red until end
      }
      return gerepileupto(av,N);
    default:
      pari_err(e_MISC,"Incorrect type in tFnEvalAt");
      return NULL;
  }
  return NULL;
}

GEN
tFnsEvalAt(GEN Fns, GEN Z, GEN vars, GEN T, GEN pe, GEN p, long e, ulong h)
{
  GEN A;
  ulong nF,nZ;
  ulong i,j;
  nF = lg(Fns);
  nZ = lg(Z);
  A = cgetg(nF,t_MAT);
  for(j=1;j<nF;j++)
  {
    gel(A,j) = cgetg(nZ,t_COL);
    for(i=1;i<nZ;i++)
    {
      gcoeff(A,i,j) = tFnEvalAt(gel(Fns,j),gel(Z,i),vars,T,pe,p,e,h);
    }
  }
  return A;
}

GEN tCrvLiftPty(GEN F, GEN dF, GEN F0, GEN vars, GEN x0, GEN y0, GEN T, GEN pe, GEN p, long e, ulong h)
{
  pari_sp av=avma;
  GEN y,dF0,z,dz,P,pm;
  ulong m;
  P = cgetg(3,t_VEC);
  gel(P,1) = x0;
  F0 = gsubst(F0,vars[1],x0);
  F0 = FqX_red(F0,T,pe);
  //pari_printf("F0=%Ps\n",F0);
  dF0 = deriv(F0,vars[2]);
  //pari_printf("dF0=%Ps\n",dF0);
  y = y0;
  m = 1;
  while(m<e) // TODO
  {
    m *= 2;
    if(m>e) m=e;
    //pari_printf("O(%Ps^%lu)\n",p,m);
    pm = powis(p,m);
    //pari_printf("y=%Ps, dF0(y)=%Ps\n",y,FqX_eval(dF0,y,T,pm));
    y = ZX_sub(y,ZpXQ_div(FqX_eval(F0,y,T,pm),FqX_eval(dF0,y,T,pm),T,pm,p,m));
    //pari_printf("%Ps\n",y);
  }
  y = scalarpol(FpX_red(y,pe),vars[3]);
  m = 1;
  while(m<h) // TODO
  {
    m *= 2;
    if(m>h) m=h;
    //pari_printf("O(t^%lu)\n",m);
    y = ZqXn_setprec(y,m,varn(T));
    gel(P,2) = y;
    z = tFnEvalAt(F,P,vars,T,pe,p,e,m);
    //pari_printf("z=%Ps\n",z);
    dz = tFnEvalAt(dF,P,vars,T,pe,p,e,m);
    //pari_printf("dz=%Ps\n",dz);
    dz = ZqXn_div(z,dz,T,pe,p,e);
    //pari_printf("dy=%Ps\n",dz);
    y = ZqXn_sub(y,dz);
    //pari_printf("%Ps\n",y);
  }
  //printf("End liftPty\n");
  //gel(P,2) = y;
  //pari_printf("Verif: %Ps\n",tFnEvalAt(F,P,vars,T,pe,p,e,h));
  return gerepileupto(av,ZqXn_red(y,NULL,pe));
}

long BadVecSearch(GEN V, GEN X)
{ // TODO
  long n,i;
  n = lg(V);
  for(i=1;i<n;i++)
    if(gequal(gel(V,i),X)) return i;
  return 0;
}

GEN tCurveNewRandPt(GEN f, GEN df, GEN f0, GEN vars, GEN Z0, GEN bad, GEN T, GEN pe, GEN p, long e, ulong h)
{
  pari_sp av = avma, av1;
  long vT,dT;
  GEN x,fx,y,badpt,P,P0;
  vT = varn(T);
  dT = degree(T);
  //pari_printf("Looking for new pt, f0=%Ps, T=%Ps, dT=%ld, vT=%ld\n",f0,T,dT,vT);
  av1 = avma;
  for(;;)
  {
    set_avma(av1);
    x = random_FpX(dT,vT,p);
    //pari_printf("Trying x=%Ps\n",x);
    fx = gsubst(f0,vars[1],x);
    fx = FqX_red(fx,T,p);
    //pari_printf("fx=%Ps\n",fx);
    y = FqX_roots(fx,T,p);
    if(lg(y)==1) continue; /* No roots */
    y = gel(y,itos(genrand(stoi(lg(y)-1)))+1);
    P0 = mkvec2(x,y);
    //pari_printf("Considering P0=%Ps\n",P0);
    if(BadVecSearch(Z0,P0)) continue; /* Already got this point */
    badpt = FnEvalAt(bad,P0,vars,T,p,1,p);
    badpt = Fq_red(badpt,T,p);
    if(gequal0(badpt)) continue; /* Forbidden locus */
    y = tCrvLiftPty(f,df,f0,vars,x,y,T,pe,p,e,h);
    x = ZqXn_from_Zq(x,h,vars[3]);
    P = mkvec2(mkvec2(x,y),P0);
    return gerepilecopy(av,P);
  }
}

GEN
tCurveApplyAut(GEN aut, GEN P, GEN vars, GEN T, GEN pe, GEN p, long e, ulong h)
{ /* aut = [X,Y,Z] function of x,y. Return [X/Z,Y/Z]. */
  pari_sp av = avma;
  GEN a,b,c,Q;
  a = tFnEvalAt(gel(aut,1),P,vars,T,pe,p,e,h);
  b = tFnEvalAt(gel(aut,2),P,vars,T,pe,p,e,h);
  c = tFnEvalAt(gel(aut,3),P,vars,T,pe,p,e,h);
  c = ZqXn_inv(c,T,pe,p,e);
  Q = cgetg(3,t_VEC);
  gel(Q,1) = ZqXn_mul(a,c,T,pe);
  gel(Q,2) = ZqXn_mul(b,c,T,pe);
  return gerepileupto(av,Q);
}

GEN
tCurveApplyFrob(GEN P, GEN FrobMat, GEN T, GEN pe)
{
  pari_sp av = avma;
  GEN Q;
  Q = cgetg(3,t_VEC);
  gel(Q,1) = ZqXn_relFrob(gel(P,1),FrobMat,T,pe);
  gel(Q,2) = ZqXn_relFrob(gel(P,2),FrobMat,T,pe);
  return gerepileupto(av,Q);
}

GEN
tCurveAutFrobClosure(GEN P, GEN P0, GEN Auts, GEN vars, GEN FrobMat, GEN T, GEN pe, GEN p, long e, ulong h)
{ /* Orbit of point P under Frob and Auts, and induced permutations */
  pari_sp av = avma;
  GEN OP,OP0,sFrob,sAuts,res;
  ulong nAuts,nO,nmax;
  ulong i,j,k,m,n;

  //printf("Into Orb closure\n");
  //pari_printf("With P0=%Ps\n",P0);
  OP = cgetg(2,t_VEC); /* Orbit of P, will grow as needed */
  OP0 = cgetg(2,t_VEC); /* Same mod M */
  gel(OP,1) = P;
  gel(OP0,1) = P0;
  nO = 1; /* Size of orbit */
  sFrob = cgetg(2,t_VECSMALL); /* Perm induced by Frob, will grow as needed */
  sFrob[1] = 0;
  nAuts = lg(Auts);
  sAuts = cgetg(nAuts,t_VEC); /* Perms induced by Auts, will grow as needed */
  for(i=1;i<nAuts;i++)
  {
    gel(sAuts,i) = cgetg(2,t_VECSMALL);
    gel(sAuts,i)[1] = 0;
  }
  /* A 0 in a permutation means we do not know yet the image by the permutation */
  nmax = 2; /* Current size of vectors. If size nO of orbit reaches this, the vectors must grow! */

  for(n=1;n<=nO;n++)
  {
    /* Do we know what happens to OP[n] for all auts? */
    for(i=0;i<nAuts;i++) /* i=0: Frob. i>0: Auts[i] */
    {
      if(gel(i?gel(sAuts,i):sFrob,n)==0)
      { /* We do not know, let's find out. */
        m = n; /* Index of the point we are following */
        P = gel(OP,m);
        P0 = gel(OP0,m);
        for(;;)
        {
          /* Apply aut to P */
          if(i)
          {
            P = tCurveApplyAut(gmael(Auts,i,1),P,vars,T,pe,p,e,h);
            //pari_printf("Applying aut %Ps to %Ps ",gmael(Auts,i,1),P0);
            P0 = CurveApplyAut(gmael(Auts,i,1),P0,vars,T,p,p,1);
            //pari_printf("yields %Ps\n",P0);
          }
          else
          {
            P = tCurveApplyFrob(P,FrobMat,T,pe);
            //pari_printf("Frobbing %Ps ",P0);
            P0 = mkvec2(Fq_pow(gel(P0,1),p,T,p),Fq_pow(gel(P0,2),p,T,p));
            //pari_printf("yields %Ps\n",P0);
          }
          /* Is the result a point we already know? */
          k = BadVecSearch(OP0,P0);
          if(k)
          { /* We're back to a pt we know, stop search */
            //printf("Found in pos %lu\n",k);
            (i?gel(sAuts,i):sFrob)[m] = k;
                     //pari_printf("Frob: %Ps\n",sFrob);
          //pari_printf("Aut 1: %Ps\n",gel(sAuts,1));
            break;
          }
          /* This is a new pt. Add it to orbit and create placeholders for its transfos */
          nO++;
          //printf("Not found, new point %lu\n",nO);
          (i?gel(sAuts,i):sFrob)[m] = nO;
          if(nO==nmax) /* Must extend all vectors */
          {
            nmax*=2;
            OP = VecExtend(OP);
            OP0 = VecExtend(OP0);
            sFrob = VecSmallExtend(sFrob);
            for(j=1;j<nAuts;j++) gel(sAuts,j) = VecSmallExtend(gel(sAuts,j));
          }
          gel(OP,nO)=P;
          gel(OP0,nO)=P0;
          setlg(OP,nO+1);
          setlg(OP0,nO+1);
          m = nO;
          sFrob[nO]=0;
          setlg(sFrob,nO+1);
          for(j=1;j<nAuts;j++)
          {
            gel(sAuts,j)[nO]=0;
            setlg(gel(sAuts,j),nO+1);
          }
          //pari_printf("Frob: %Ps\n",sFrob);
          //pari_printf("Aut 1: %Ps\n",gel(sAuts,1));
        }
      }
      //printf("End of %lu-orbit\n",i);
    }
  }
  //printf("End of orbit, size %lu",nO);
  res = mkvecn(4,OP,OP0,sFrob,sAuts);
  return gerepilecopy(av,res);
}


GEN
tPicInit(GEN f, GEN Auts, ulong g, ulong d0, GEN L, GEN bad, GEN p, GEN AT, long e, ulong h, GEN Lp)
{
  pari_sp av = avma;
  ulong a,nZ,nV2,nAuts,n,nOP,m,i,j;
  GEN f0,df,vars,pe,T,FrobMat,Z,Z0,P,P0,FrobCyc,AutData,OP,V1,V2,V20,W0,V,M,I,KV,U,params,L12,J;
  struct pari_mt pt;
  GEN worker,done,E,H;
  long workid,pending,k;

  vars = variables_vecsmall(f);
  nZ = 5*d0+1; /* min required #pts */

  Get_ff_aT(AT,p,&a,&T);
  pari_printf("vars=%Ps, a=%lu, T=%Ps\n",vars,a,T);
  pe = powis(p,e);
  FrobMat = ZpXQ_FrobMat(T,p,e,pe);

  if(DEBUGLEVEL>=2) printf("picinit: Finding points\n");
  n = 0; /* current #pts */
  Z = cgetg(1,t_VEC); /* list of pts */
  Z0 = cgetg(1,t_VEC); /* same mod p,t */
  /* Initialise empty cycles */
  FrobCyc = cgetg(1,t_VECSMALL);
  nAuts = lg(Auts);
  AutData = cgetg(nAuts,t_VEC);
  for(i=1;i<nAuts;i++)
  {
    gel(AutData,i) = cgetg(3,t_VEC);
    gmael(AutData,i,1) = cgetg(1,t_VECSMALL);
    gmael(AutData,i,2) = gmael(Auts,i,2);
  }
  f0 = gsubst(f,vars[3],gen_0);
  df = deriv(f,vars[2]);
  /* Loop until we have enough pts */
  while(n<nZ)
  {
    P = tCurveNewRandPt(f,df,f0,vars,Z0,bad,T,pe,p,e,h);
    P0 = gel(P,2);
    P = gel(P,1);
    //pari_printf("New point: %Ps, residue %Ps\n",P,P0);
    /* Compute closure under Frob and Auts */
    OP = tCurveAutFrobClosure(P,P0,Auts,vars,FrobMat,T,pe,p,e,h);
    nOP = lg(gel(OP,1))-1; /* # new pts */
    if(DEBUGLEVEL>=3) printf("picinit: Got closure of size %lu\n",nOP);
    /* Add new pts */
    Z = gconcat(Z,gel(OP,1));
    Z0 = gconcat(Z0,gel(OP,2));
    /* Shift permutation describing Frob and Auts */
    for(m=1;m<=nOP;m++)
    {
      gel(OP,3)[m] += n;
      for(i=1;i<nAuts;i++)
        gmael(OP,4,i)[m] += n;
    }
    /* Add these permutaton data */
    FrobCyc = gconcat(FrobCyc,gel(OP,3));
    for(i=1;i<nAuts;i++)
      gmael(AutData,i,1) = gconcat(gmael(AutData,i,1),gmael(OP,4,i));
    /* Update # pts */
    n += nOP;
  }
  //pari_printf("Frob: %Ps\n",FrobCyc);
  //pari_printf("Aut 1: %Ps\n",gmael(AutData,1,1));

  if(DEBUGLEVEL>=2) printf("picinit: Evaluating rational functions\n");
  V = cgetg(6,t_VEC);
  gel(V,1) = V1 = tFnsEvalAt(gel(L,1),Z,vars,T,pe,p,e,h);
  gel(V,2) = V2 = tFnsEvalAt(gel(L,2),Z,vars,T,pe,p,e,h);
  gel(V,3) = tDivAdd(V1,V2,3*d0+1-g,T,p,pe,0);
  V20 = ZqXnM_to_ZqM_shallow(V2);
  gel(V,5) = I = gel(FqM_indexrank(V20,T,p),1); /* Rows of V2 forming invertible block */
  /* That invertible block */
  nV2 = ((d0+1)<<1)-g;
  M = cgetg(nV2,t_MAT);
  for(j=1;j<nV2;j++)
  {
    gel(M,j) = cgetg(nV2,t_COL);
    for(i=1;i<nV2;i++)
      gcoeff(M,i,j) = gcoeff(V2,I[i],j);
  }
  gel(V,4) = ZqXnM_inv(M,T,pe,p,e);
  W0 = V1;
  if(DEBUGLEVEL>=2) printf("picinit: Computing equation matrices\n");
  KV = cgetg(4,t_VEC);
  E = stoi(e);
  worker = strtofunction("_ZqXnM_eqn");
  mt_queue_start_lim(&pt,worker,3);
  for(k=1;k<=3||pending;k++)
  {
    mt_queue_submit(&pt,k,k<=3?mkvecn(5,gel(V,k),T,pe,p,E):NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done) gel(KV,workid) = done;
  }
  mt_queue_end(&pt);
  if(DEBUGLEVEL>=2) printf("picinit: Constructing evaluation maps\n");
  H = utoi(h);
  L12 = gel(L,3);
  if(gequal0(L12)) U = gen_0;
  else
  {
    params = cgetg(9,t_VEC);
    gel(params,2) = Z;
    gel(params,3) = vars;
    gel(params,4) = T;
    gel(params,5) = pe;
    gel(params,6) = p;
    gel(params,7) = E;
    gel(params,8) = H;
    U = cgetg(4,t_VEC);
    worker = strtofunction("_tFnsEvalAt");
    mt_queue_start_lim(&pt,worker,2);
    for(i=1;i<=2||pending;i++)
    {
      if(i<=2)
      {
        gel(params,1) = gel(L12,i);
        mt_queue_submit(&pt,i,params);
      }
      else mt_queue_submit(&pt,0,NULL);
      done = mt_queue_get(&pt,&workid,&pending);
      if(done) gel(U,workid) = mkvec(done);
    }
    mt_queue_end(&pt);
    gel(U,3) = gen_0;
  }
  if(Lp==NULL) Lp = gen_0;
  J = mkvecn(lgtJ,f,stoi(g),stoi(d0),L,T,p,E,pe,FrobMat,Lp,V,KV,W0,U,Z,FrobCyc,AutData,H);
  return gerepilecopy(av,J);
}

GEN tPicTruncate(GEN J)
{
  GEN J0;
  ulong nZ,m,i,j,vt;
  vt = variables_vecsmall(gel(J,1))[3];
  J0 = cgetg(18,t_VEC);
  gel(J0,1) = gsubst(gel(J,1),vt,gen_0);
  gel(J0,4) = gsubst(gel(J,4),vt,gen_0);
  for(i=2;i<=10;i++) /* From g to Lp, except L */
  {
    if(i==4) continue;
    gel(J0,i) = gcopy(gel(J,i));
  }

  gel(J0,11) = cgetg(6,t_VEC);
  for(i=1;i<=4;i++) /* V */
    gmael(J0,11,i) = ZqXnM_to_ZqM(gmael(J,11,i));
  gmael(J0,11,5) = gcopy(gmael(J,11,5));
  gel(J0,12) = cgetg(4,t_VEC);
  for(i=1;i<=3;i++) /* KV */
    gmael(J0,12,i) = ZqXnM_to_ZqM(gmael(J,12,i));
  gel(J0,13) = ZqXnM_to_ZqM(gel(J,13)); /* W0 */
  if(!gequal0(gel(J,14))) /* EvalData */
  {
    gel(J0,14) = cgetg(4,t_VEC);
    for(i=1;i<=2;i++)
    {
      m = lg(gmael(J,14,i));
      gmael(J0,14,i) = cgetg(m,t_VEC);
      for(j=1;j<m;j++)
        gmael3(J0,14,i,j) = ZqXnM_to_ZqM(gmael3(J,14,i,j));
    }
    gmael(J0,14,3) = gequal0(gmael(J,14,3)) ? gcopy(gen_0) : ZqXnM_to_ZqM(gmael(J,14,3));
  }
  nZ = lg(gel(J,15));
  gel(J0,15) = cgetg(nZ,t_VEC);
  for(i=1;i<nZ;i++)
  {
    gmael(J0,15,i) = cgetg(3,t_VEC);
    gmael3(J0,15,i,1) = gcopy(gmael4(J,15,i,1,2));
    gmael3(J0,15,i,2) = gcopy(gmael4(J,15,i,2,2));
  }
  gel(J0,16) = gcopy(gel(J,16)); /* FrobCyc */
  gel(J0,17) = gcopy(gel(J,17)); /* AutData */
  return J0;
}

ulong Jgeth(GEN J) { return itou(gel(J,18));}

GEN tPicSetPrec(GEN J, ulong h)
{
  GEN J0;
  ulong nZ,m,i,j,h0;
  if(h==0)
    return tPicTruncate(J);
  h0 = Jgeth(J);
  if(h>h0)
    pari_err(e_IMPL,"Unable to perform this reduction for now");
  J0 = cgetg(lgtJ+1,t_VEC);
  for(i=1;i<=10;i++) /* From f to Lp */
    gel(J0,i) = gcopy(gel(J,i));
  gel(J0,11) = cgetg(6,t_VEC);
  for(i=1;i<=4;i++) /* V */
    gmael(J0,11,i) = ZqXnM_redprec(gmael(J,11,i),h);
  gmael(J0,11,5) = gcopy(gmael(J,11,5));
  gel(J0,12) = cgetg(4,t_VEC);
  for(i=1;i<=3;i++) /* KV */
    gmael(J0,12,i) = ZqXnM_redprec(gmael(J,12,i),h);
  gel(J0,13) = ZqXnM_redprec(gel(J,13),h); /* W0 */
  if(!gequal0(gel(J,14))) /* EvalData */
  {
    gel(J0,14) = cgetg(4,t_VEC);
    for(i=1;i<=2;i++)
    {
      m = lg(gmael(J,14,i));
      gmael(J0,14,i) = cgetg(m,t_VEC);
      for(j=1;j<m;j++)
        gmael3(J0,14,i,j) = ZqXnM_redprec(gmael3(J,14,i,j),h);
    }
    gmael(J0,14,3) = gequal0(gmael(J,14,3)) ? gcopy(gen_0) : ZqXnM_redprec(gmael(J,14,3),h);
  }
  nZ = lg(gel(J,15));
  gel(J0,15) = cgetg(nZ,t_VEC);
  for(i=1;i<nZ;i++)
  {
    gmael(J0,15,i) = cgetg(3,t_VEC);
    gmael3(J0,15,i,1) = ZqXn_redprec(gmael3(J,15,i,1),h);
    gmael3(J0,15,i,2) = ZqXn_redprec(gmael3(J,15,i,2),h);
  }
  gel(J0,16) = gcopy(gel(J,16)); /* FrobCyc */
  gel(J0,17) = gcopy(gel(J,17)); /* AutData */
  gel(J0,18) = utoi(h);
  return J0;
}

/* Eval maps */

GEN
tPicEval(GEN J, GEN W)
{
  pari_sp av = avma, av1, av2;
  GEN T,p,pe,V,KV,U,U1,U2,res,resi1;
  long e;
  ulong n1,n2,i1,i2;
  GEN S1,S2,I,M,s2,s2I,K;
  ulong d0,g,nV,i;

  U = JgetEvalData(J); /* L(2D0-Ei), deg Ei = d0-g (i=1,2), repeated for each embedding into Qq */
  if(gequal0(U))
    pari_err(e_MISC,"this Jacobian does not contain the data required to evaluate points");
  U1 = gel(U,1);
  n1 = lg(U1); /* Deg of E1 / Q */
  U2 = gel(U,2);
  n2 = lg(U2); /* Deg of E2 / Q */
  M = gel(U,3); /* Matrix to apply to the I-entries */
  JgetTpe(J,&T,&pe,&p,&e);
  d0 = Jgetd0(J);
  g = Jgetg(J);
  V = JgetV_all(J);
  I = gel(V,5); /* Row indices to look at to ID an elt of V */
  if(typ(M)==t_INT) M = gel(V,4);
  V = gel(V,2);
  nV = lg(V);
  KV = JgetKV(J,2);

  res = cgetg(n1,t_MAT);
  for(i1=1;i1<n1;i1++)
  {
    av1 = avma;
    S1 = tDivAdd(W,gel(U1,i1),2*d0+1,T,p,pe,0); /* L(4D0-D-E1) */
    S1 = tDivSub(V,S1,KV,1,T,p,e,pe,2); /* L(2D0-D-E1), generically 1-dimensional */
    S1 = gerepileupto(av1,gel(S1,1));
    S1 = tDivMul(S1,V,T,pe); /* L(4D0-D-E1-ED) */
    S1 = gerepileupto(av1,S1);
    S1 = tDivSub(W,S1,KV,d0+1-g,T,p,e,pe,2); /* L(2D0-E1-ED) */
    S1 = gerepileupto(av1,S1);
    resi1 = cgetg(n2,t_COL);
    for(i2=1;i2<n2;i2++)
    {
      av2 = avma;
      S2 = tDivAdd(S1,gel(U2,i2),2*d0+1,T,p,pe,0); /* L(4D0-E1-E2-ED) */
      S2 = gerepileupto(av2,S2);
      S2 = tDivSub(V,S2,KV,1,T,p,e,pe,2); /* L(2D0-E1-E2-ED), generically 1-dimensional */
      s2 = gel(S2,1); /* Generator */
      s2 = gerepileupto(av2,s2);
      /* get coords of s2 w.r.t. V */
      s2I = cgetg(nV,t_COL);
      for(i=1;i<nV;i++)
        gel(s2I,i) = gel(s2,I[i]);
      K = ZqXnM_ZqXnC_mul(M,s2I,T,pe);
      gel(resi1,i2) = gerepileupto(av2,K);
    }
    gel(res,i1) = gerepileupto(av1,resi1);
  }
  return gerepileupto(av,res);
}

GEN
tPicEval_worker(GEN W, GEN J)
{
  return tPicEval(J,W);
}

/* Lift */

GEN
tPicDeflate(GEN J, GEN W, ulong nIGS)
{ /* Finds nIGS elts w1, .. , wn in W s.t. (W) = min (wi) */
  pari_sp av,av1;
  GEN V,T,pe,p,IGS,IV,wV;
  ulong g,nV,nW,r,i,j,k;
  long e;

  V = JgetV(J,2);
  JgetTpe(J,&T,&pe,&p,&e);
  g = Jgetg(J);
  nV = lg(V)-1;
  nW = lg(W)-1;

  IGS = cgetg(nIGS+1,t_VEC);
  av = avma;
  while(1)
  {
    set_avma(av);
    for(i=1;i<=nIGS;i++) gel(IGS,i) = ZqXn_RandVec(W,T,p,pe);
    av1 = avma;
    IV = cgetg(nIGS*nV+1,t_MAT);
    k=1;
    for(i=1;i<=nIGS;i++)
    {
      wV = tDivMul(gel(IGS,i),V,T,p);
      for(j=1;j<=nV;j++)
      {
        gel(IV,k) = gel(wV,j);
        k++;
      }
    }
    r = FqM_rank(ZqXnM_to_ZqM(IV),T,p);
    if(r==nV+nW+g-1)
    {
      set_avma(av1);
      return IGS;
    }
    printf("IGS[%lu,%lu]\n",r,nV+nW+g-1);
  }
}

GEN
tPicDeflate_U(GEN J, GEN W, ulong nIGS)
{ /* Find IGS and express its coords on V */
  pari_sp av = avma;
  GEN T,pe,p;
  long e;
  GEN GW,K,U,X,I,M;
  ulong i,j,m;

  JgetTpe(J,&T,&pe,&p,&e);
  GW = tPicDeflate(J,W,nIGS); /* IGS of W */
  /* Get coords // basis of V */
  X = JgetV_all(J);
  M = gel(X,4);
  I = gel(X,5);
  m = lg(I);
  K = cgetg(nIGS+1,t_MAT);
  for(j=1;j<=nIGS;j++)
  {
    gel(K,j) = cgetg(m,t_COL);
    for(i=1;i<m;i++)
      gcoeff(K,i,j) = gcoeff(GW,I[i],j);
  }
  U = ZqXnM_mul(M,K,T,pe);
  return gerepileupto(av,U);
}

GEN
tPicInflate_U(GEN J, GEN U, GEN I) /* Takes IGS given by coords // V */
{  /* I : indices of rows forming invtble block -> make it 1 */
  pari_sp av = avma;
  GEN T,pe,p;
  long e;
  GEN V,KV,GWV,wV,W;
  ulong d0,g;
  ulong nU,nV,nW;
  ulong i,j,k;

  JgetTpe(J,&T,&pe,&p,&e);
  V = JgetV(J,2);
  KV = JgetKV(J,2);
  nU = lg(U)-1;
  nV = lg(V)-1;
  d0 = Jgetd0(J);
  g = Jgetg(J);
  nW = d0+1-g;

  GWV = cgetg(nU*nV+1,t_MAT); /* w*V for w in GW */
  k = 1;
  for(i=1;i<=nU;i++)
  {
    wV = tDivMul(ZqXnM_ZqXnC_mul(V,gel(U,i),T,pe),V,T,pe); /* TODO useful to precompte V[i]*V ? */
    for(j=1;j<=nV;j++)
    {
      gel(GWV,k) = gel(wV,j);
      k++;
    }
  }
  GWV = ZqXnM_image(GWV,T,p);
  W = tDivSub(V,GWV,KV,nW,T,p,e,pe,3); /* TODO pass precomputed IGS of V */
  if(I) /* Change basis to make block = 1 */
    W = ZqXn_Subspace_normalize(W,I,T,pe,p,e,0);
  return gerepileupto(av,W);
}

GEN
tM2ABCD_1block(GEN M, ulong top, ulong left, GEN uv)
/* Same as above, but all zeros except for block M starting at top+1,left+1 */
/* /!\ Not suitable for gerepile */
{
  GEN u,v,res,A,col,zero;
  long h,vt,va;
  long m,n;
  ulong bot,right,i,j,p,q,ui,vj;
  A = gcoeff(M,1,1);
  h = lg(A)-2;
  vt = varn(A);
  va = varn(gel(A,2));
  zero = ZqXn_0(h,vt,va);
  res = cgetg(5,t_VEC);
  RgM_dimensions(M,&m,&n);
  bot = top+m;
  right = left+n;
  for(p=1;p<=2;p++)
  {
    u = gmael(uv,1,p);
    m = lg(u);
    for(q=1;q<=2;q++)
    {
      v = gmael(uv,2,q);
      n = lg(v);
      A = cgetg(n,t_MAT);
      for(j=1;j<n;j++)
      {
        col = cgetg(m,t_COL);
        vj = v[j];
        for(i=1;i<m;i++)
        {
          ui = u[i];
          if(vj>left && vj<=right && ui>top && ui<=bot) gel(col,i) = gcoeff(M,ui-top,vj-left);
          else gel(col,i) = zero;
        }
        gel(A,j) = col;
      }
      gel(res,q+2*(p-1)) = A;
    }
  }
  return res;
}


GEN
tPicLift_worker(GEN V0j, ulong shift, GEN uv, GEN AinvB, GEN CAinv, GEN T, GEN pe)
{
  pari_sp av = avma; /* TODO save mem? */
  GEN abcd,drho;
  abcd = tM2ABCD_1block(V0j,0,shift,uv); /* Split */
  drho = ZqXnM_sub(ZqXnM_mul(gel(abcd,1),AinvB,T,pe),gel(abcd,2)); /* aA^-1B-b */
  drho = ZqXnM_mul(CAinv,drho,T,pe); /* CA^-1aA^-1B - CA^-1b */
  drho = ZqXnM_add(gel(abcd,4),drho); /* d + CA^-1aA^-1B - CA^-1b */
  drho = ZqXnM_sub(drho,ZqXnM_mul(gel(abcd,3),AinvB,T,pe)); /* d + CA^-1aA^-1B - CA^-1b - cA^-1B */
  drho = mat2col0(drho);
  return gerepilecopy(av,drho);
}

GEN
tPicLift_RandLift_U(GEN U, GEN U0, GEN KM, GEN T, GEN p, GEN pe, long e, ulong h1, ulong h2)
{ /* U prec h2, U0 h12, KM h12 */
  pari_sp av;

  GEN K,red,newU,c;
  ulong nU,nU0,nV;
  ulong i,j,k,m,s;

  nU = lg(U);
  nU0 = lg(U0);
  nV = lg(gel(U,1));

  av=avma;
  do
  { /* Get random vector in KM with nonzero last entry */
    avma=av;
    K = ZqXn_RandVec_1(KM,pe);
    red = gel(K,lg(K)-1);
  } while(ZqXn_is0mod(red,p));
  /* Divide by last entry */
  red = ZqXn_inv(red,T,pe,p,e);
  setlg(K,lg(K)-1);
  K = ZqXn_ZqXnC_mul(red,K,T,pe);
  newU = gcopy(U);
  k = 1;
  for(i=1;i<nU;i++)
  {
    /* Correct U[i] */
    for(j=1;j<nU0;j++)
    { /* Add the proper multiple of U0[j] to it */
      for(m=1;m<nV;m++)
      {
        c = ZqXn_mul(gel(K,k),gcoeff(U0,m,j),T,pe);
        for(s=h1;s<h2;s++)
        {
          gmael3(newU,i,m,s+2) = ZX_add(gmael3(newU,i,m,s+2),gel(c,s+2-h1));
        }
      }
      k++;
    }
  }
  return gerepileupto(av,newU);
}

GEN
tPicLiftTors_Chart_worker(GEN randseed, GEN J, GEN l, GEN U, GEN U0, GEN I, GEN KM, ulong h1, ulong h2, GEN c0, ulong P0, GEN P1)
{
  pari_sp av=avma,avU;
  GEN T,p,pe;
  long e;
  GEN W,c,res;
  ulong nc,i;
  setrand(randseed);
  JgetTpe(J,&T,&pe,&p,&e);
  nc = lg(c0)-1; /* Size of coords */

  res = cgetg(3,t_VEC);
  /* Get a random lift */
  gel(res,1) = U = tPicLift_RandLift_U(U,U0,KM,T,p,pe,e,h1,h2);
  avU = avma;
  W = tPicInflate_U(J,U,I);
  W = tPicMul(J,W,l,0);
  W = gerepileupto(avU,W);
  /* Mul by l, get coordinates, and compare them to those of W0 */
  c = tPicChart(J,W,P0,P1);
  if(c==NULL)
   return gc_const(av,gen_0);
  c = gerepileupto(avU,c);
  for(i=1;i<=nc;i++) /* The coords are c0 mod t^h1 -> divide */
    gel(c,i) = ZqXn_dropdiv(ZqXn_sub(gel(c,i),gel(c0,i)),h1);
  gel(res,2) = gerepileupto(avU,c);
  return res;
}

GEN
tPicLiftTors(GEN J, GEN W, GEN l, long hini)
{
  pari_sp av=avma,avrho,av1,av2,av3;
  GEN T,p,pe,V;
  long va,vt,e,hfin,h1,h2,h12,mask;
  ulong g,d0,nV,nW,nZ,nGW=2;
  ulong r,i,j,k;
  GEN Wq,Jq,Uq,sW,Vs,U0,V0,U,GWV,wV,uv,ABCD,Ainv,CAinv,AinvB,rho,K,KM;
  GEN J2,Vh2;
  GEN c0=NULL,P1=NULL,Ulifts,clifts,Ktors,red,U2;
  int liftsOK=0,P0_tested=0;
  ulong nc,n,P0=1;
  struct pari_mt pt;
  GEN vFixedParams,args,worker,done,randseed;
  long workid,pending;

  JgetTpe(J,&T,&pe,&p,&e);
  hfin = Jgeth(J);
  if(hini >= hfin) return gcopy(W);
  mask = quadratic_prec_mask(hfin); /* Best scheme to reach prec efin */
  mask >>= 1;
  /* TODO determine where to start */
  g = Jgetg(J);
  d0 = Jgetd0(J);
  V = JgetV(J,2);
  nV = lg(V)-1;
  nZ = lg(gel(V,1))-1;
  nW = lg(W)-1;
  vt = varn(gcoeff(V,1,1));
  va = varn(T);

  if(hini!=-1) /* Is W a ZqM or already a ZqXnM? */
    pari_err(e_IMPL,"W already ZqXnM");

  Wq = W;
  Jq = tPicTruncate(J);
  Uq = PicDeflate_U(Jq,Wq,nGW);
  U = ZqXnM_from_ZqM(Uq,2,vt);

  sW = gel(FqM_indexrank(Wq,T,p),1); /* rows s.t. this block is invertible, # = nW, we won't change them */
  Vs = cgetg(nV+1,t_MAT); /* V with only the rows in sW */
  for(j=1;j<=nV;j++)
  {
    gel(Vs,j) = cgetg(nW+1,t_COL);
    for(i=1;i<=nW;i++) gcoeff(Vs,i,j) = gcoeff(V,sW[i],j);
  }
  U0 = ZqXnM_ker(Vs,T,pe,p,e); /* # = nV-nW = d0 */
  V0 = cgetg(d0+1,t_VEC);
  for(i=1;i<=d0;i++)
    gel(V0,i) = tDivMul(ZqXnM_ZqXnC_mul(V,gel(U0,i),T,pe),V,T,pe); /* s*V for s in subspace of V whose rows in sW are 0 */
  /* TODO parallel? */

  r = 3*d0+1-g; /* Wanted rank of GWV */
  av1 = avma; /* To collect mem at each main loop iteration */
  /* Main loop */
  for(h1=1,h2=2;;)
  {
    if(DEBUGLEVEL) pari_printf("tpiclifttors: Lifting %Ps-torsion point from prec O(t^%lu) to O(t^%lu)\n",l,h1,h2);
    h12 = h2-h1;
    J2 = h2 < hfin ? tPicSetPrec(J,h2) : J;
    GWV = cgetg(nGW*nV+1,t_MAT); /* w*V for w in GW */
    /* We need it to have rk r, it is already the case mod t^h1 */
    Vh2 = ZqXnM_redprec(V,h2);
    //U = ZqXnM_setprec(U,h2,va); // TODO necessary?
    k = 1;
    for(i=1;i<=nGW;i++)
    {
      wV = tDivMul(ZqXnM_ZqXnC_mul(Vh2,gel(U,i),T,pe),Vh2,T,pe); // Prec h2
      for(j=1;j<=nV;j++)
      {
        gel(GWV,k) = gel(wV,j);
        k++;
      }
    }

    avrho = avma;
    uv = FqM_MinorCompl(ZqXnM_to_ZqM(GWV),T,p); /* How to split GWV TODO constant? */
    ABCD = M2ABCD(GWV,uv); /* Splitting */
    Ainv = ZqXnM_inv(gel(ABCD,1),T,pe,p,e); // All prec h2
    CAinv = ZqXnM_mul(gel(ABCD,3),Ainv,T,pe);
    AinvB = ZqXnM_mul(Ainv,gel(ABCD,2),T,pe);
    rho = ZqXnM_mul(CAinv,gel(ABCD,2),T,pe);
    rho = ZqXnM_sub(gel(ABCD,4),rho); /* Prec h2; size nZ-r,nGW*nV-r(=dW if nGW-2); tests if rk = r */
    for(i=1;i<=nZ-r;i++)
    {
      for(j=1;j<=nGW*nV-r;j++)
        gcoeff(rho,i,j) = ZqXn_dropdiv(gcoeff(rho,i,j),h1); /* Divide by t^h1 -> prec h12 */
    }

    /* Now deform the w in GW by t^e1*V0. Actually we deform U1 by t^e1*U0. */
    /* TODO do not deform U1[1]? */
    K = cgetg(nGW*d0+2,t_MAT); /* Lin sys to solve in prec h12 */
    vFixedParams = cgetg(6,t_VEC);
    gel(vFixedParams,1) = uv;
    gel(vFixedParams,2) = ZqXnM_redprec(AinvB,h12);
    gel(vFixedParams,3) = ZqXnM_redprec(CAinv,h12);
    gel(vFixedParams,4) = T;
    gel(vFixedParams,5) = pe;
    args = cgetg(3,t_VEC);
    worker = snm_closure(is_entry("_tPicLift_worker"),vFixedParams);
    pending = 0;
    i = nGW;
    j = 0;
    mt_queue_start_lim(&pt,worker,nGW*d0);
    for(k=1;k<=nGW*d0||pending;k++)
    {
      if(k<=nGW*d0)
      {
        if(++i>nGW)
        {
          i = 1;
          gel(args,1) = ZqXnM_redprec(gel(V0,++j),h12);
        }
        gel(args,2) = utoi((i-1)*nV);
        mt_queue_submit(&pt,j+d0*(i-1),args);
      }
      else mt_queue_submit(&pt,k,NULL);
      done = mt_queue_get(&pt,&workid,&pending);
      if(done) gel(K,workid) = done;
    }
    mt_queue_end(&pt);
    gel(K,nGW*d0+1) = mat2col0(rho);
    /* Find a random solution to the inhomogeneous system */
    KM = gerepileupto(avrho,ZqXnM_ker(K,T,pe,p,e)); /* Prec h12 */
    if(DEBUGLEVEL>=3||(lg(KM)==1)) printf("tpicliftors: dim ker lift: %ld\n",lg(KM)-1);
    Ulifts = cgetg(g+2,t_VEC);
    clifts = cgetg(g+2,t_MAT);
    vFixedParams = cgetg(12,t_VEC);
    randseed = cgetg(2,t_VEC);
    av2 = av3 = avma;
    while(1)
    {
      set_avma(av3);
      if(c0==NULL) /* Compute coords of 0 if not already done */
      {
        /* Find coords of 0 */
        for(;;)
        {
          if(DEBUGLEVEL>=2) printf("tpiclifttors: Computing coords of 0, P0=%lu\n",P0);
          c0 = tPicChart(J,JgetW0(J),P0,NULL);
          if(c0) break;
          P0++;
          if(P0>nZ+g-d0)
            pari_err(e_MISC,"tpiclifttors: Run out of charts while computing coords of 0");
        }
        c0 = gerepileupto(av3,c0);
        nc = lg(c0)-1;
        /* Find indep set of rows to normalize */
        c0 = col2mat(c0,nc/nW,nW);
        P1 = FqM_indexrank(ZqXnM_to_ZqM(c0),T,p);
        P1 = gel(P1,1);
        c0 = ZqXn_Subspace_normalize(c0,P1,T,pe,p,e,1);
        c0 = mat2col0(c0);
        gerepileall(av2,2,&c0,&P1);
        av3 = avma;
      }
      /* Find g+1 lifts TODO in parallel */
      gel(vFixedParams,1) = J2;
      gel(vFixedParams,2) = l;
      gel(vFixedParams,3) = U;
      gel(vFixedParams,4) = ZqXnM_redprec(U0,h12);
      gel(vFixedParams,5) = sW;
      gel(vFixedParams,6) = KM;
      gel(vFixedParams,7) = utoi(h1);
      gel(vFixedParams,8) = utoi(h2);
      gel(vFixedParams,9) = ZqXnC_redprec(c0,h2);
      gel(vFixedParams,10) = utoi(P0);
      gel(vFixedParams,11) = P1;
      worker = snm_closure(is_entry("_tPicLiftTors_Chart_worker"),vFixedParams);
      pending = 0;
      liftsOK = 1;
      mt_queue_start_lim(&pt,worker,g+1);
      for(i=1;i<=g+1||pending;i++)
      {
        if(i<=g+1)
        {
          gel(randseed,1) = utoi(pari_rand());
          mt_queue_submit(&pt,i,randseed);
        }
        else mt_queue_submit(&pt,i,NULL);
        done = mt_queue_get(&pt,&workid,&pending);
        if(done)
        {
          if(done==gen_0)
          {
            if(DEBUGLEVEL>=3) printf("tpiclifttors: Lift %ld had a chart issue\n",workid);
            liftsOK = 0;
          }
          else
          {
            gel(Ulifts,workid) = gel(done,1);
            gel(clifts,workid) = gel(done,2);
          }
        }
      }
      mt_queue_end(&pt);
      if(liftsOK==0)
      { /* This chart does not work. Take the next one, reset data, and restart */
        if(DEBUGLEVEL>=3) printf("tpiclifttors: Changing chart\n");
        P0++; /* New chart */
        printf("P0=%lu\n",P0);
        if(P0>nZ+g-d0)
          pari_err(e_MISC,"tpiclifttors: run out of charts while computing coords of 0");
        P0_tested = 0;
        c0 = NULL; /* Coords of 0 must be recomputed */
        av3 = av2;
        continue; /* Try again with this new chart */
      }
      Ktors = ZqXnM_ker(clifts,T,pe,p,e); /* Find comb with coord = 0 */
      n = lg(Ktors)-1;
      printf("dim Ktors = %lu\n",n);
      if(n!=1)
      { /* l-tors is etale, so this can only happen if Chart is not diffeo - > change chart */
        P0++; /* New chart */
        if(DEBUGLEVEL>=3)
        {
          printf("tpiclifttors: Dim ker tors = %ld (expected 1), changing charts\n",n);
          if(DEBUGLEVEL>=5)
            printf("nZ=%lu, g=%lu, d0=%lu\nP0=%lu\n",nZ,g,d0,P0);
        }
        P0++; /* New chart */
        if(P0>nZ+g-d0)
          pari_err(e_MISC,"tpiclifttors: run out of charts while computing coords of 0");
        P0_tested = 0;
        c0 = NULL; /* Coords of 0 must be recomputed */
        av3 = av2;
        continue; /* Try again with this new chart */
      }
      Ktors = ZqXnC_setprec(gel(Ktors,1),h2,varn(T));
      red = gel(Ktors,1);
      for(i=2;i<=g+1;i++)
        red = ZqXn_add(red,gel(Ktors,i));
      if(ZqXn_is0mod(red,p)) /* Want nonzero sum */
      {
        if(DEBUGLEVEL>=3) printf("tpiclifttors: Sum of Ktors is zero!\n");
        continue;
      }
      Ktors = ZqXn_ZqXnC_mul(ZqXn_inv(red,T,pe,p,e),Ktors,T,pe); /* Normalise so that sum = 1 */
      W = NULL; /* If done, return updated W; else update U. */
      for(i=1;i<=g+1;i++)
        gel(Ulifts,i) = ZqXnM_ZqXn_mul(gel(Ulifts,i),gel(Ktors,i),T,pe);
      U2 = gel(Ulifts,1);
      for(i=2;i<=g+1;i++)
        U2 =ZqXnM_add(U2,gel(Ulifts,i));
      U2 = gerepileupto(av3,U2);
      /* But first check if really l-tors, as the chart might not be injective ! */
      if(P0_tested == 0)
      {
        if(DEBUGLEVEL>=3) pari_printf("tpiclifttors: Checking %Ps-tors\n",l);
        W = tPicInflate_U(J2,U2,NULL);
        if(!tPicIsTors(J2,W,l))
        {
          if(DEBUGLEVEL>=3) printf("Not actually l-torsion!!! Changing charts\n");
          P0++;
          c0 = NULL;
          av3 = av2;
          continue;
        }
        P0_tested = 1;
      }
      break;
    }
    /* END LIFTING */
    if(h2==hfin)
    {
      if(W == NULL) /* Update W, if not already done, and return it */
        W = tPicInflate_U(J,U2,NULL);
      break;
    }
    h1 = h2;
    h2<<=1;
    if(mask&1) h2--;
    mask>>=1;
    U = ZqXnM_setprec(U2,h2,va);
    if(c0)
      gerepileall(av1,3,&U,&c0,&P1);
    else
      U = gerepileupto(av1,U);
  }
  return gerepileupto(av,W);
}

/* GalRep */

GEN
tTorsSpaceFrob_worker(GEN W1, GEN X1, GEN W2, GEN X2, GEN J)
{
  pari_sp av = avma;
  GEN W;
  ulong x1,x2;
  x1 = itou(X1);
  if(W2==gen_0)
  {
    W = tPicNeg(J,W1,0);
    W = tPicFrobPow(J,W,x1);
    return gerepileupto(av,W);
  }
  x2 = itou(X2);
  W1 = tPicFrobPow(J,W1,x1);
  W2 = tPicFrobPow(J,W2,x2);
  W = tPicChord(J,W1,W2,0);
  return gerepileupto(av,W);
}

GEN
tPicTorsSpaceFrobEval(GEN J, GEN gens, GEN cgens, ulong l, GEN matFrob, GEN matAuts)
{
  return XPicTorsSpaceFrobEval(J,gens,cgens,l,matFrob,matAuts,"_tTorsSpaceFrob_worker","_tPicEval_worker");
}

GEN
ZqXnV_mroots_to_pol(GEN Z,GEN T, GEN pe)
{
  pari_sp av = avma;
  GEN a,C,F;
  ulong n,k,j;
  n = lg(Z);
  if(n==1)
    return scalarpol(gen_1,0);
  C = cgetg(n,t_VEC);
  gel(C,1) = gel(Z,1);
  for(k=2;k<n;k++)
  {
    a = gel(Z,k);
    gel(C,k) = ZqXn_add(a,gel(C,k-1));
    for(j=k-1;j>1;j--)
      gel(C,j) = ZqXn_add(gel(C,j-1),ZqXn_mul(a,gel(C,j),T,pe));
    gel(C,1) = ZqXn_mul(gel(C,1),a,T,pe);
  }
  F = cgetg(n+2,t_POL);
  F[1] = 0;
  setsigne(F,1);
  setvarn(F,0);
  for(k=1;k<n;k++)
    gel(F,k+1) = ZqXn_red(gel(C,k),T,pe);
  gel(F,n+1) = gcopy(gen_1);
  return gerepileupto(av,F);
}

GEN
tPolExpID(GEN Z, GEN T, GEN pe) /* bestappr of prod(x-z), z in Z */
{
  pari_sp av=avma;
  GEN f;
  f = ZqXnV_mroots_to_pol(Z,T,pe);
  if(poldegree(f,varn(T))>0) pari_err(e_MISC,"Irrational coefficient: %Ps",f);
  f = simplify_shallow(f);
  f = gmodulo(f,pe);
  f = bestappr(f,NULL);
  return gerepileupto(av,f);
}

GEN
tOnePol(GEN N, GEN D, GEN ImodF, GEN Jfrobmat, ulong l, GEN QqFrobMat, GEN T, GEN pe)
{ /* Actually returns a vector of n1*n2 pols (all elem. symm. fns) */
  pari_sp av = avma, av1;
  GEN R,Z,Z1,F,Fi,z;
  ulong d,ld,j,k,n,i1,i2,i;
  long n1,n2,n12;
  n = lg(N);
  //pari_printf("N=%Ps\nD=%Ps\n",N,D);
  RgM_dimensions(gel(N,1),&n2,&n1);
  /* N, D vectors of length n-1 of n2*n1 matrices
   * N[i]*D[i] = value at pt indexed by ImodF[i]
   * Get the others by applying Frob */
  d = lg(Jfrobmat)-1;
  ld = upowuu(l,d);
  n12 = n1*n2;
  R = cgetg(n,t_VEC);
  Z = cgetg(n12+1,t_VEC);
  for(k=1;k<n;k++)
  {
    i=1;
    for(i1=1;i1<=n1;i1++)
    {
      for(i2=1;i2<=n2;i2++)
      {
        gel(Z,i) = ZqXn_mul(gmael3(N,k,i1,i2),gmael3(D,k,i1,i2),T,pe);
        i++;
      }
    }
    gel(R,k) = ZqXnV_mroots_to_pol(Z,T,pe);
  }
  R = gerepileupto(av,R);
  F = cgetg(n12+1,t_VEC);
  Z = cgetg(ld,t_VEC);
  for(i=0;i<n12;i++)
  {
    av1 = avma;
    for(j=1;j<ld;j++) gel(Z,j) = NULL; /* Mark roots as unknown */
    for(k=1;k<n;k++)
    {
      z = polcoef(gel(R,k),i,0);
      j = ImodF[k];
      for(;;)
      {
        gel(Z,j) = z;
        j = ActOni(Jfrobmat,j,l);
        if(gel(Z,j)) break;
        z = ZqXn_relFrob(z,QqFrobMat,T,pe);
      }
    }
    /* Multiple roots? */
    Z1 = gen_indexsort_uniq(Z,(void*)&cmp_universal,&cmp_nodata);
    if(lg(Z1)<lg(Z))
    {
      set_avma(av1);
      Fi = gen_0;
    }
    else
    {
      Fi = tPolExpID(Z,T,pe);
      if(typ(Fi)!=t_VEC)
        Fi = gerepilecopy(av1,mkvec2(Fi,Z));
      else
      { /* Bestappr failed */
        set_avma(av1);
        Fi = gen_m1;
      }
    }
    gel(F,i+1) = Fi;
  }
  return gerepileupto(av,F);
}

GEN
tAllPols(GEN J, GEN Z, ulong l, GEN JFrobMat)
{
  pari_sp av = avma, avj;
  GEN QqFrobMat,T,pe,p;
  GEN F,ImodF,Jfrobmat,Ft,F1,f,pols,args,res;
  ulong d,nF,lF,npols,n,i,j,j0,i1,i2,m,k,nmult,nfail;
  long e;
  int All0;
  long n1,n2,n12;
  struct pari_mt pt;
  GEN worker,done;
  long pending,workid;

  JgetTpe(J,&T,&pe,&p,&e);
  QqFrobMat = JgetFrobMat(J);
  F = gel(Z,1);
  ImodF = gel(Z,2);
  d = lg(JFrobMat)-1;
  Jfrobmat = M2Flm(JFrobMat,l,d,d); /* JFrobMat, version Flm */
  nF = lg(F); /* Number of vectors */
  RgM_dimensions(gel(F,1),&n2,&n1);
  n12 = n1*n2;
  lF = lg(gmael3(F,1,1,1))-1; /* Size of each vector */
  /* F = list of nF-1 matrices of size n2*n1 of vectors of size lF */
  Ft = cgetg(lF,t_VEC);
  /* Ft[j,i,i1,i2] = F[i,i1,i2,j], keeping only the j such that F[.,.,.,j] not identically 0 */
  for(j=j0=1;j<lF;j++)
  {
    All0 = 1;
    avj = avma;
    gel(Ft,j0) = cgetg(nF,t_VEC);
    for(i=1;i<nF;i++)
    {
      gmael(Ft,j0,i) = cgetg(n1+1,t_MAT);
      for(i1=1;i1<=n1;i1++)
      {
        gmael3(Ft,j0,i,i1) = cgetg(n2+1,t_COL);
        for(i2=1;i2<=n2;i2++)
        {
          f = gmael4(Ft,j0,i,i1,i2) = gmael4(F,i,i1,i2,j);
          if(gequal0(f)==0) All0 = 0;
        }
      }
    }
    if(All0) set_avma(avj); /* Drop this j */
    else j0++;
  }
  if(DEBUGLEVEL>=3) printf("AllPols: Reducing lF from %lu to %lu\n",lF-1,j0-1);
  lF = j0;
  F1 = cgetg(lF,t_VEC);
  npols = 0;
  for(i=1;i<lF;i++) /* Find the i such that the ith coord of all the vectors in all the matrices are invertible, and store there inverses */
  {
    npols++;
    gel(F1,i) = cgetg(nF,t_VEC);
    for(j=1;j<nF;j++)
    {
      gmael(F1,i,j) = cgetg(n1+1,t_MAT);
      for(i1=1;i1<=n1;i1++)
      {
        gmael3(F1,i,j,i1) = cgetg(n2+1,t_COL);
        for(i2=1;i2<=n2;i2++)
        {
          f = gmael4(Ft,i,j,i1,i2);
          if(ZqXn_is0mod(f,p))
          {
            gel(F1,i) = NULL;
            npols--;
            i2=n2+1;i1=n1+1;j=nF;
          }
          else
            gmael4(F1,i,j,i1,i2) = ZqXn_inv(f,T,pe,p,e); /* TODO do it later in case we give up this i */
        }
      }
    }
  }
  pending = 0;
  nmult = nfail = 0;
  worker = strtofunction("_tOnePol");
  args = cgetg(9,t_VEC);
  gel(args,3) = ImodF;
  gel(args,4) = Jfrobmat;
  gel(args,5) = utoi(l);
  gel(args,6) = QqFrobMat;
  gel(args,7) = T;
  gel(args,8) = pe;
  npols *= (lF-2)*n12;
  pols = cgetg(npols+1,t_VEC);
  mt_queue_start_lim(&pt,worker,npols);
  done = NULL;
  for(i=j=m=n=1;i<lF||pending;n++,j++)
  {
    if(j==lg(F1))
    {
      j=1;
      i++;
    }
    if(gel(F1,j)==NULL || i==j) continue; /* Skip if denom=0 or if denom=num */
    if(i<lF)
    {
      gel(args,1) = gel(Ft,i);
      gel(args,2) = gel(F1,j);
      mt_queue_submit(&pt,n,args);
    }
    else mt_queue_submit(&pt,0,NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done)
    {
      for(k=1;k<=n12;k++)
      {
        res = gel(done,k);
        if(gequal(res,gen_m1))
        { /* Bestappr failed */
          nfail++;
         continue;
        }
        if(gequal0(res))
        { /* Repeated roots */
          nmult++;
          continue;
        }
        gel(pols,m++) = res;
      }
    }
  }
  mt_queue_end(&pt);
  if(DEBUGLEVEL)
    printf("Out of %lu polynomials, %lu had repeated roots, %lu could not be identified, and %lu were identified.\n",npols,nmult,nfail,m-1);
  if(nmult==npols)
    pari_err(e_MISC,"No squarefree polynomial, try again with another evaluation map");
  setlg(pols,m);
  return gerepilecopy(av,pols);
}


