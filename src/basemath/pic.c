#include "pari.h"
#include "paripriv.h"

#define lgJ 16

/* Linear algebra */

long ZX_is0mod(GEN x, GEN p)
{
  pari_sp av = avma;
  GEN red;
  long res;
  red = (typ(x)==t_POL?FpX_red(x,p):Fp_red(x,p));
  res = gequal0(red);
  avma = av;
  return res;
}

GEN FpXM_red(GEN A, GEN p)
{
  long m,n,i,j;
  GEN B,c;
  RgM_dimensions(A,&m,&n);
  B = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(B,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
    {
      c = gcoeff(A,i,j);
      gcoeff(B,i,j) = (typ(c)==t_POL?FpX_red(c,p):Fp_red(c,p));
    }
  }
  return B;
}

GEN FpXM_add(GEN A, GEN B, GEN p)
{
  long m,n,i,j;
  GEN C;
  RgM_dimensions(A,&m,&n);
  C = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(C,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(C,i,j) = FpX_add(gcoeff(A,i,j),gcoeff(B,i,j),p);
  }
  return C;
}

GEN FpXM_sub(GEN A, GEN B, GEN p)
{
  long m,n,i,j;
  GEN C;
  RgM_dimensions(A,&m,&n);
  C = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(C,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(C,i,j) = FpX_sub(gcoeff(A,i,j),gcoeff(B,i,j),p);
  }
  return C;
}

GEN ZXM_add(GEN A, GEN B)
{
  long m,n,i,j;
  GEN C;
  RgM_dimensions(A,&m,&n);
  C = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(C,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(C,i,j) = ZX_add(gcoeff(A,i,j),gcoeff(B,i,j));
  }
  return C;
}

GEN ZXM_sub(GEN A, GEN B)
{
  long m,n,i,j;
  GEN C;
  RgM_dimensions(A,&m,&n);
  C = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(C,j) = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
      gcoeff(C,i,j) = ZX_sub(gcoeff(A,i,j),gcoeff(B,i,j));
  }
  return C;
}

GEN FqV_Fq_mul(GEN v, GEN a, GEN T, GEN p)
{
  ulong n,i;
  GEN av;
  n = lg(v);
  av = cgetg(n,t_VEC);
  for(i=1;i<n;i++)
  {
    gel(av,i) = Fq_mul(a,gel(v,i),T,p);
  }
  return av;
}

GEN FqM_Fq_mul(GEN v, GEN a, GEN T, GEN p)
{
  ulong n,i;
  GEN av;
  n = lg(v);
  av = cgetg(n,t_MAT);
  for(i=1;i<n;i++)
  {
    gel(av,i) = FqC_Fq_mul(gel(v,i),a,T,p);
  }
  return av;
}

GEN ZXM_Z_mul(GEN A, GEN a)
{
  long m,n,i,j;
  GEN B,col;
  RgM_dimensions(A,&m,&n);
  B = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    col = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
    {
      gel(col,i) = ZX_Z_mul(gcoeff(A,i,j),a);
    }
    gel(B,j) = col;
  }
  return B;
}

GEN FpXC_add(GEN A, GEN B, GEN p)
{
  ulong n = lg(A),i;
  GEN C;
  C = cgetg(n,t_COL);
  for(i=1;i<n;i++) gel(C,i) = FpX_add(gel(A,i),gel(B,i),p);
  return C;
}

GEN FpXC_sub(GEN A, GEN B, GEN p)
{
  ulong n = lg(A),i;
  GEN C;
  C = cgetg(n,t_COL);
  for(i=1;i<n;i++) gel(C,i) = FpX_sub(gel(A,i),gel(B,i),p);
  return C;
}

GEN ZXC_add(GEN A, GEN B)
{
  ulong n = lg(A),i;
  GEN C;
  C = cgetg(n,t_COL);
  for(i=1;i<n;i++) gel(C,i) = ZX_add(gel(A,i),gel(B,i));
  return C;
}

GEN ZXC_sub(GEN A, GEN B)
{
  ulong n = lg(A),i;
  GEN C;
  C = cgetg(n,t_COL);
  for(i=1;i<n;i++) gel(C,i) = ZX_sub(gel(A,i),gel(B,i));
  return C;
}

GEN RandVec_1(GEN A, GEN pe)
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
          if(random_Fl(2)) v = ZXC_sub(v,gel(A,j));
          else v = ZXC_add(v,gel(A,j));
        }
      }
    }
  } while(v==NULL);
  return gerepileupto(av,v);
}

GEN RandVec_padic(GEN A, GEN T, GEN p, GEN pe)
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
      c = Fq_mul(b,gcoeff(A,i,j),T,pe);
      if(j==1) gel(v,i) = c;
      else gel(v,i) = Fq_add(gel(v,i),c,T,pe);
    }
    v = gerepilecopy(av,v);
  }
  return v;
}

GEN ZpXQMinv(GEN A, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma, avk;
  ulong n,i,j,k;
  GEN B,col,l,col2,C;
  GEN I;
  GEN Fq0,Fq1;

  n = lg(A)-1;
  if(n==0) return cgetg(1,t_MAT);
  I = cgetg(n+1,t_VECSMALL); /* Vector of permutation of rows */
  for(i=1;i<=n;i++) I[i] = i;
  Fq0 = pol_0(varn(T));
  Fq1 = pol_1(varn(T));
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
      gel(col,i+n) = i==k? Fq1 : Fq0;
    }
    /* Col is now vcat Ak,Ik */
    /* The last k cols of B are known */
    /* Upper part of B is UT1, lower part is LT */
    /* Reduce Ck using Cj for j=n..k+1 */
    /* Actually only need coeffs for i<k and i>=n+k */
    for(j=n;j>k;j--)
    {
      l = Fq_red(ZX_neg(gel(col,I[j])),T,pe);
      /* Ck += l*Cj */
      for(i=1;i<=j;i++)
        gel(col,I[i]) = ZX_add(gel(col,I[i]),ZX_mul(l,gcoeff(B,I[i],j)));
      /* Useless
      for(i=j;i<=n;i++)
        gel(col,I[i]) = Fq0; */
      for(i=n+j;i<=2*n;i++)
        gel(col,i) = ZX_add(gel(col,i),ZX_mul(l,gcoeff(B,i,j)));
      col = gerepileupto(avk,col);
    }
    for(i=1;i<=k;i++) gel(col,I[i]) = Fq_red(gel(col,I[i]),T,pe);
    for(i=n+k+1;i<=2*n;i++) gel(col,i) = Fq_red(gel(col,i),T,pe);
    /* Now coefs k+1..n of col are 0 */
    /* Find pivot above k (hopefully k) */
    for(i=k;i;i--)
    {
      l = gel(col,I[i]);
      if(ZX_is0mod(l,p)==0) break;
    }
    if(i!=k)
    {
      j = I[k]; I[k] = I[i]; I[i] = j;
    }
    /* Divide by pivot */
    l = ZpXQ_inv(l,T,p,e);
    col2 = cgetg(2*n+1,t_COL);
    for(i=1;i<k;i++) gel(col2,I[i]) = Fq_mul(gel(col,I[i]),l,T,pe);
    gel(col2,I[k]) = Fq1;
    for(i=k+1;i<=n;i++) gel(col2,I[i]) = Fq0;
    for(i=n+1;i<n+k;i++) gel(col2,i) = Fq0;
    for(i=n+k;i<=2*n;i++) gel(col2,i) = Fq_mul(gel(col,i),l,T,pe);
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
      l = FpX_neg(gcoeff(B,I[j],k),pe);
      /* Ck += l*Cj */
      for(i=(k==2?j:1);i<=n;i++) gel(col,i) = ZX_add(gel(col,i),ZX_mul(l,gcoeff(C,i,I[j])));
      col = gerepileupto(avk,col);
    }
    col2 = cgetg(n+1,t_COL);
    for(i=1;i<=n;i++) gel(col2,i) = Fq_red(gel(col,i),T,pe);
    gel(C,I[k]) = gerepileupto(avk,col2);
  }
  /* Ensure C is suitable for gerepile */
  for(i=1;i<=n;i++)
    gcoeff(C,i,I[1]) = gcopy(gcoeff(C,i,I[1]));
  return gerepileupto(av,C);
}

GEN VecSmallCompl(GEN v, ulong n)
{
  ulong iv,ic,m;
  GEN c;
  c = cgetg(n+2-lg(v),t_VECSMALL);
  iv = ic = 1;
  for(m=1;m<=n;m++)
  {
    if(m<v[iv]) c[ic++]=m;
    else iv++;
  }
  return c;
}

GEN matkerpadic(GEN A, GEN T, GEN pe, GEN p, long e)
{ /* Assumes good red, i.e. the rank does not decrease mod p */
  pari_sp av = avma, av1;
  GEN IJ,I,J,J1,P,A1,A2,B,K;
  ulong n,r,i,j;
  GEN Fq0,Fqm1;
  if(e==1) return FqM_ker(A,T,p);
  n = lg(A)-1;
  IJ = FqM_indexrank(A,T,p);
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
  B = gerepileupto(av1,ZpXQMinv(A1,T,pe,p,e));
  A2 = cgetg(n-r+1,t_MAT); /* Other block */
  for(j=1;j<=n-r;j++)
  {
    gel(A2,j) = cgetg(r+1,t_COL);
    for(i=1;i<=r;i++) gcoeff(A2,i,j) = gcoeff(A,I[i],P[j+r]);
  }
  /* K = vcat of A1^-1*A2, -Id_{n-r}, with perm P^-1 of rows */
  B = gerepileupto(av1,FqM_mul(B,A2,T,pe));
  Fq0 = pol_0(varn(T));
  Fqm1 = scalarpol(gen_m1,varn(T));
  K = cgetg(n-r+1,t_MAT);
  for(j=1;j<=n-r;j++)
  {
    gel(K,j) = cgetg(n+1,t_COL);
    for(i=1;i<=r;i++)
      gcoeff(K,P[i],j) = gcoeff(B,i,j);
    for(i=r+1;i<=n;i++)
      gcoeff(K,P[i],j) = j+r==i?Fqm1:Fq0;
  }
  return gerepilecopy(av,K);
}

GEN mateqnpadic(GEN A, GEN T, GEN pe, GEN p, long e)
{ /* Assumes good red, i.e. the rank does not decrease mod p */
  pari_sp av = avma, av1;
  GEN IJ,I,J,I1,P,A1,A2,B,E;
  ulong n,r,i,j;
  GEN Fq0,Fqm1;
  if(e==1)
    return gerepilecopy(av,shallowtrans(FqM_ker(shallowtrans(A),T,p)));
  n = lg(gel(A,1))-1;
  IJ = FqM_indexrank(A,T,p);
  I = gel(IJ,1); /* Rows forming invertible block */
  J = gel(IJ,2); /* Columns spanning the space, ignore others (good red) */
  r = lg(I)-1;
  I1 = VecSmallCompl(I,n); /* Other rows */
  P = cgetg(n+1,t_VECSMALL); /* First I then I1 */
  for(i=1;i<=r;i++) P[i] = I[i];
  for(i=1;i<=n-r;i++) P[r+i] = I1[i];
  av1 = avma;
  A1 = cgetg(r+1,t_MAT); /* Invertible block */
  for(j=1;j<=r;j++)
  {
    gel(A1,j) = cgetg(r+1,t_COL);
    for(i=1;i<=r;i++) gcoeff(A1,i,j) = gcoeff(A,P[i],J[j]);
  }
  B = gerepileupto(av1,ZpXQMinv(A1,T,pe,p,e));
  A2 = cgetg(r+1,t_MAT); /* Other block */
  for(j=1;j<=r;j++)
  {
    gel(A2,j) = cgetg(n-r+1,t_COL);
    for(i=1;i<=n-r;i++) gcoeff(A2,i,j) = gcoeff(A,P[i+r],J[j]);
  }
  /* E = hcat of A2*A1^-1, -Id_{n-r}, with perm P^-1 of cols*/
  B = gerepileupto(av1,FqM_mul(A2,B,T,pe));
  Fq0 = pol_0(varn(T));
  Fqm1 = scalarpol(gen_m1,varn(T));
  E = cgetg(n+1,t_MAT);
  for(j=1;j<=r;j++)
    gel(E,P[j]) = gel(B,j);
  for(j=r+1;j<=n;j++)
  {
    gel(E,P[j]) = cgetg(n-r+1,t_COL);
    for(i=1;i<=n-r;i++) gcoeff(E,i,P[j]) = i+r==j?Fqm1:Fq0;
  }
  return gerepilecopy(av,E);
}

GEN mat2col(GEN A)
{
  unsigned long n,m,i,j=1;
  GEN C;
  n = lg(A)-1;
  if(n==0) return cgetg(1,t_COL);
  m = lg(gel(A,1))-1;
  C = cgetg(n*m+1,t_COL);
  for(i=1;i<=m;i++)
  {
    for(j=1;j<=n;j++)
    {
      gel(C,(i-1)*n+j) = gcoeff(A,i,j);
    }
  }
  return C;
}

GEN col2mat(GEN C, unsigned long m, unsigned long n)
{
  GEN A,Aj;
  unsigned long i=1,j=1;
  A = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    Aj = cgetg(m+1,t_COL);
    for(i=1;i<=m;i++)
    {
      gel(Aj,i) = gel(C,(i-1)*n+j);
    }
    gel(A,j) = Aj;
  }
  return A;
}

GEN FqM_MinorCompl(GEN A, GEN T, GEN p)
{
  pari_sp av=avma;
  GEN IJ,uv;
  long m,n;
  RgM_dimensions(A,&m,&n);
  IJ = FqM_indexrank(A,T,p);
  uv = cgetg(3,t_VEC);
  gel(uv,1) = cgetg(3,t_VEC);
  gel(uv,2) = cgetg(3,t_VEC);
  gmael(uv,1,1) = gel(IJ,1);
  gmael(uv,1,2) = VecSmallCompl(gel(IJ,1),m);
  gmael(uv,2,1) = gel(IJ,2);
  gmael(uv,2,2) = VecSmallCompl(gel(IJ,2),n);
  return gerepilecopy(av,uv);
}

GEN M2ABCD(GEN M, GEN uv)
{ /* 2*2 block splitting of matrix */
  GEN u,v,res,A,col;
  ulong m,n,i,j,p,q;
  res = cgetg(5,t_VEC);
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
        for(i=1;i<m;i++)
        {
          gel(col,i) = gcoeff(M,u[i],v[j]);
        }
        gel(A,j) = col;
      }
      gel(res,q+2*(p-1)) = A;
    }
  }
  return res;
}

GEN M2ABCD_1block(GEN M, ulong top, ulong left, GEN uv)
/* Same as above, but all zeros except for block M starting at top+1,left+1 */
/* /!\ Not suitable for gerepile */
{
  GEN u,v,res,A,col;
  long m,n;
  ulong bot,right,i,j,p,q,ui,vj;
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
          else gel(col,i) = gen_0;
        }
        gel(A,j) = col;
      }
      gel(res,q+2*(p-1)) = A;
    }
  }
  return res;
}

GEN RgM_drop_rows(GEN A, GEN I)
{
  GEN B;
  ulong i,j,k,iB,iI;
  long m,n;
  RgM_dimensions(A,&m,&n);
  k = lg(I)-1;
  B = cgetg(n,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(B,j) = cgetg(m-k+1,t_COL);
    iI=iB=1;
    for(i=1;i<=m;i++)
    {
      if(I[iI]==i) iI++;
      else gcoeff(B,iB++,j)=gcoeff(A,i,j);
    }
  }
  return B;
}

GEN Subspace_normalize(GEN V, GEN I, GEN T, GEN pe, GEN p, long e, long drop)
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
  P = ZpXQMinv(P,T,pe,p,e);
  V = FqM_mul(V,P,T,pe);
  if(drop)
  {
    V = RgM_drop_rows(V,I);
    return gerepilecopy(av,V);
  }
  else return gerepileupto(av,V);
}

/* Add-flip chains */

GEN NAF(GEN n)
{ /* Non-adjacent form of integer n */
  pari_sp av = avma;
  GEN B,B2,C,N;
  ulong l,i;

  B = binary_zv(n);
  l = lg(B);
  B2 = cgetg(l+2,t_VECSMALL);
  C = cgetg(l+2,t_VECSMALL);
  N = cgetg(l+1,t_VECSMALL);
  for(i=1;i<l;i++)
  {
    B2[i] = B[l-i];
  }
  C[1] = B2[l] = B2[l+1] = 0;
  for(i=1;i<=l;i++)
  { 
    C[i+1] = (C[i]+B2[i]+B2[i+1])/2;
    N[i] = B2[i]+C[i]-2*C[i+1];
  }
  if(N[l]==0) setlg(N,l);
  return gerepilecopy(av,N);
}

GEN AddFlipChain(GEN n, long signmatters)
{ /* Fast-exponentiation chain w.r.t. operation (x,y)->-(x+y) */
  pari_sp av = avma;
  GEN N,A,m;
  ulong l,i,j,jm1;
  long sn;

  if(equalis(n,3))
  {
    A = mkvecn(4,
        mkvec2(gen_1,mkvecsmall2(0,-1)),
        mkvec2(gen_m2,mkvecsmall2(1,1)),
        mkvec2(gen_m1,mkvecsmall2(1,0)),
        mkvec2(stoi(3),mkvecsmall2(3,2))
      );
    return gerepilecopy(av,A);
  }
  if(equalis(n,-3))
  {
    A = mkvecn(4,
        mkvec2(gen_1,mkvecsmall2(0,-1)),
        mkvec2(gen_m2,mkvecsmall2(1,1)),
        mkvec2(gen_2,mkvecsmall2(2,0)),
        mkvec2(stoi(-3),mkvecsmall2(3,1))
      );
    return gerepilecopy(av,A);
  }

  sn = signe(n);
  setsigne(n,1);
  N = NAF(n);
  l = lg(N);
  A = cgetg(2*l,t_VEC);
  gel(A,1) = mkvec2(gen_1,mkvecsmall2(0,-1));
  j = 1;
  jm1 = 0;
  m = gen_1;
  for(i=l-2;i;i--)
  {
    j++;
    m = mulii(m,gen_m2);
    gel(A,j) = mkvec2(m,mkvecsmall2(j-1,j-1));
    if(N[i])
    {
      j++;
      if(signe(m)*N[i]>0)
      {
        m = negi(addiu(m,1));
        gel(A,j) = mkvec2(m,mkvecsmall2(j-1,1));
      }
      else
			{
        m = subui(1,m);
        if(jm1==0)
        {
          jm1 = j;
          gel(A,jm1) = mkvec2(gen_m1,mkvecsmall2(1,0));
          j++;
          gel(A,j) = mkvec2(m,mkvecsmall2(j-2,jm1));
        }
        else gel(A,j) = mkvec2(m,mkvecsmall2(j-1,jm1));
      }
    }
  }
  if(signmatters && signe(m)*sn<0)
  {
    j++;
    gel(A,j) = mkvec2(negi(m),mkvecsmall2(j-1,0));
  }
  setlg(A,j+1);
  setsigne(n,sn);
  avma = av;
  return gerepilecopy(av,A);
}

/* Picard group */

/*
Structure of a Jacobian:
1: f, equation of curve (0 if not available)
2: g, genus
3: d0, degree of line bundle B
4: If B=O_X(D0), basis of RR spaces L(D0), L(2D0), L(2D0-E1), L(2D0-E2) in terms of x and y (the latter 2 used for EvalData); else []
5: T, poly in Z[t] such that Qq = Qp[t]/T
6: p
7: e, such that we work in J(Zq/p^e)
8: p^e
9: FrobMat, gives matrix of Frob on the power basis 1,t,t²,... of Qq
10: V = [V1,V2,V3] where Vn = H0(n*B). (Having a nice basis of V2 improves the evaluaton map.)
11: KV = [KV1,KV2,KV3], where KVn = equation matrix for Vn
12: W0 = f*V1 for some f in V1, subspace of V2 representing the origin
13: EvalData [U1,U2,I,M]: pair of subspaces Ui of the form V2(-E) with E effective of degree d0-g, used for construction of eval map, then vecsmall I of row indices, and matrix M such that v in V should be taken to M*(v_I) for evaluation
14: If B=O_X(D0), vector Z of points at which the sections are evaluated; else []
15: FrobCyc, permutation describing the action of Frob on Z
16: AutsCyc, vector of permutations describing the action of Auts on Z

Note: usually, B=O_X(D0), in which case W0=V1=L(D0).
Note: if either of f, one of the RR spaces L(...), or Z are not available, then the p-adic accuracy cannot be increased.
Note: if accuracy is increased, assume that in 13, the block formed by the I-rows of V2 is invertible, and that M is the inverse of that block.
*/

GEN Jgetf(GEN J) {return gel(J,1);}
long Jgetg(GEN J) {return itos(gel(J,2));}
long Jgetd0(GEN J) {return itos(gel(J,3));}
GEN JgetL(GEN J) {return gel(J,4);}
GEN JgetT(GEN J) {return gel(J,5);}
GEN Jgetp(GEN J) {return gel(J,6);}
long Jgete(GEN J) {return itos(gel(J,7));}
GEN Jgetpe(GEN J) {return gel(J,8);}
GEN JgetFrobMat(GEN J) {return gel(J,9);}
GEN JgetV(GEN J, ulong n) {return gmael(J,10,n);}
GEN JgetV_all(GEN J) {return gel(J,10);}
GEN JgetKV(GEN J, ulong n) {return gmael(J,11,n);}
GEN JgetKV_all(GEN J) {return gel(J,11);}
GEN JgetW0(GEN J) {return gel(J,12);}
GEN JgetEvalData(GEN J) {return gel(J,13);}
GEN JgetZ(GEN J) {return gel(J,14);}
GEN JgetFrobCyc(GEN J) {return gel(J,15);}
GEN JgetAutsCyc(GEN J) {return gel(J,16);}

void JgetTpe(GEN J, GEN* T, GEN* pe, GEN* p, long* e)
{
  *T = gel(J,5);
  *p = gel(J,6);
  *e = itos(gel(J,7));
  *pe = gel(J,8);
}

GEN PicRed(GEN J, ulong e)
{
  pari_sp av = avma;
  GEN Je,p,pe;
  ulong i;
  if(Jgete(J)<e) pari_err(e_MISC,"Cannot perform this reduction");
  Je = cgetg(lgJ+1,t_VEC);
  gel(Je,1) = gcopy(Jgetf(J));
  gel(Je,2) = stoi(Jgetg(J));
  gel(Je,3) = stoi(Jgetd0(J));
  gel(Je,4) = gcopy(JgetL(J));
  gel(Je,5) = gcopy(JgetT(J));
  gel(Je,6) = p = gcopy(Jgetp(J));
  gel(Je,7) = utoi(e);
  gel(Je,8) = pe = powiu(p,e);
  gel(Je,9) = FpXM_red(JgetFrobMat(J),pe);
  gel(Je,10) = cgetg(4,t_VEC);
  for(i=1;i<=3;i++) gmael(Je,10,i) = FpXM_red(gmael(J,10,i),pe);
  gel(Je,11) = cgetg(4,t_VEC);
  for(i=1;i<=3;i++) gmael(Je,11,i) = FpXM_red(gmael(J,11,i),pe);
  gel(Je,12) = FpXM_red(JgetW0(J),pe);
  gel(Je,13) = cgetg(5,t_VEC);
  gmael(Je,13,1) = FpXM_red(gmael(J,13,1),pe);
  gmael(Je,13,2) = FpXM_red(gmael(J,13,2),pe);
  gmael(Je,13,3) = gcopy(gmael(J,13,3));
  gmael(Je,13,4) = FpXM_red(gmael(J,13,4),pe);
  gel(Je,14) = FpXT_red(JgetZ(J),pe);
  gel(Je,15) = gcopy(JgetFrobCyc(J));
  gel(Je,16) = gcopy(JgetAutsCyc(J));
  return gerepileupto(av,Je);
}

GEN DivMul(GEN f, GEN W, GEN T, GEN pe)
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
      gcoeff(fW,i,j) = Fq_mul(gel(f,i),gcoeff(W,i,j),T,pe);
  }
  return fW;
}

GEN DivAdd(GEN WA, GEN WB, ulong d, GEN T, GEN p, long e, GEN pe, ulong excess)
{ /* Does products s*t, with s=sum n_i s_i, n_i = 0 50%, -1 25%, +1 25%; similarly for t */
  /* Fails from time to time but overall good speedup */
  pari_sp av=avma;
  unsigned long nZ,j,P,r;
  GEN WAB,s,t,st;
  nZ = lg(gel(WA,1));
  while(1)
  {
    WAB = cgetg(d+excess+1,t_MAT);
    for(j=1;j<=d+excess;j++)
    {
      s = RandVec_1(WA,pe); /* random fn in WA */
      t = RandVec_1(WB,pe); /* random fn in WB */
      st = cgetg(nZ,t_COL); /* Product */
      for(P=1;P<nZ;P++)
      {
        gel(st,P) = Fq_mul(gel(s,P),gel(t,P),T,pe);
      }
      gel(WAB,j) = st;
    }
    WAB = FqM_image(WAB,T,p);
    r = lg(WAB)-1;
    if(r==d)
      return gerepileupto(av,WAB);
    if(DEBUGLEVEL) err_printf("add1(%lu/%lu)",r,d);
    excess++;
    avma = av;
  }
}

GEN DivSub(GEN WA, GEN WB, GEN KV, ulong d, GEN T, GEN p, long e, GEN pe, ulong nIGS)
{ /* { v in Ker KV | v*WA c WB } */
  pari_sp av1,av = avma;
  unsigned long nZ,P,nE,E,nV,nB,n,r;
  GEN KB,K,s,res;
  nZ = lg(KV);
  nV = lg(gel(KV,1))-1;
  KB = mateqnpadic(WB,T,pe,p,e);
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
      s = RandVec_padic(WA,T,p,pe); /* Note: RandVec_1 would be slower here */
      for(E=1;E<=nB;E++)
      {
        for(P=1;P<nZ;P++)
          gcoeff(K,nV+(n-1)*nB+E,P) = Fq_mul(gel(s,P),gcoeff(KB,E,P),T,pe);
      }
    }
    res = matkerpadic(K,T,pe,p,e);
    r = lg(res)-1;
    if(r==d) return gerepileupto(av,res);
    if(DEBUGLEVEL) err_printf("sub(%lu/%lu)",r,d);
    avma = av1;
  }
}

ulong DivSub_dimval(GEN WA, GEN WB, long dim, GEN KV, GEN T, GEN p, long e, GEN pe)
{ /* Finds the highest p-adic accuracy at which DivSub(WA,WB) has dimension dim */
  pari_sp av = avma;
  ulong nZ,P,nE,E,nV,nA,nB,n,res;
  GEN KB,K,L;
  nZ = lg(KV);
  nV = lg(gel(KV,1))-1;
  KB = mateqnpadic(WB,T,pe,p,e);
  nB = lg(gel(KB,1))-1;
  nA = lg(WA)-1;

  /* Prepare a mat K of size a v stack of KV + nA copies of KB */
  /* and copy KV at the top */
  nE = nV + nA*nB;
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
        gcoeff(K,nV+(n-1)*nB+E,P) = Fq_mul(gcoeff(WA,P,n),gcoeff(KB,E,P),T,pe);
    }
  }
  L = matkerpadic(K,T,pe,p,e);
  /* Is L even of the right dim mop p ? */
  if(lg(L)-1 != dim)
  {
    avma = av;
    return 0;
  }
  /* return vp(K*L) */
  L = FqM_mul(K,L,T,pe);
  if(gequal0(L))
  {
    avma = av;
    return (ulong)e;
  }
  res = gvaluation(L,p);
  avma = av;
  return res;
}

GEN PicNeg(GEN J, GEN W, long flag)
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

  /* (s) = -2_0-D-N */
  if(flag & 1) s = RandVec_padic(W,T,p,pe);
  else s = gel(W,1);
  sV = DivMul(s,V,T,pe); /* L(4D_0-D-N) */
  WN = DivSub(W,sV,KV,d0+1-g,T,p,e,pe,2); /* L(2D_0-N) */

  if(flag & 2)
  {
    res = cgetg(3,t_VEC);
    gel(res,1) = gcopy(WN);
    gel(res,2) = gcopy(s);
    return gerepileupto(av,res);
  }
  else
  {
    return gerepileupto(av,WN);
  }
}

GEN rand_subset(ulong n, ulong r)
{
  pari_sp av;
  GEN X,S;
  ulong m,i;
  S = cgetg(r+1,t_VECSMALL);
  av = avma;
  X = cgetg(n+1,t_VECSMALL);
  for(i=1;i<=n;i++) X[i] = 1;
  m = 0;
  while(m<r)
  {
    i = random_Fl(n)+1;
    if(X[i])
    {
      X[i] = 0;
      m++;
      S[m] = i;
    }
  }
  avma = av;
  return S;
}

GEN PicRand(GEN J, GEN randseed)
{
  pari_sp av = avma;
  ulong d0,nZ,nV;
  ulong i,j;
  long e;
  GEN T,p,pe,V;
  GEN S,col,K;

  if(randseed && !gequal0(randseed))
    setrand(randseed);

  d0 = Jgetd0(J);
  JgetTpe(J,&T,&pe,&p,&e);
  V = JgetV(J,2);
  nV = lg(V);
  nZ = lg(gel(V,1));

  K = cgetg(nV,t_MAT);
  S = rand_subset(nZ-1,d0);
  for(j=1;j<nV;j++)
  {
    col = cgetg(d0+1,t_COL);
    for(i=1;i<=d0;i++)
    {
      gel(col,i) = gcoeff(V,S[i],j);
    }
    gel(K,j) = col;
  }
  K = matkerpadic(K,T,pe,p,e);
  K = FqM_mul(V,K,T,pe);
  return gerepileupto(av,K);
}

ulong PicMember_val(GEN J, GEN W)
{
  pari_sp av = avma;
  GEN T,pe,p,w,V,wV,KV;
  long e;
  ulong res;

  JgetTpe(J,&T,&pe,&p,&e);
  V = JgetV(J,2);
  KV = JgetKV(J,2);

  do
    w = RandVec_1(W,pe);
  while(gequal0(w));
  wV = DivMul(w,V,T,pe);

  res = DivSub_dimval(W,wV,lg(W)-1,KV,T,p,e,pe);
  avma = av;
  return res;
}

ulong PicEq_val(GEN J, GEN WA, GEN WB)
{
  pari_sp av = avma;
  long e;
  GEN s,sWB,KV,T,p,pe;
  ulong r;

  JgetTpe(J,&T,&pe,&p,&e);
  KV = JgetKV(J,2);

  /* Take s in WA: (s) = -2D0+A+A1 */
  s = gel(WA,1);
  /* Compute s*WB = L(4D0-A-B-A1) */
  sWB = DivMul(s,WB,T,pe);
  /* Find { v in V | v*WA c s*WB } = L(2D0-B-A1) */
  /* This space is nontrivial iff. A~B */
  r = DivSub_dimval(WA,sWB,1,KV,T,p,e,pe);
  avma = av;
  return r;
}

ulong PicIsZero_val(GEN J, GEN W)
{
  pari_sp av = avma;
  long e;
  GEN V1,KV1,T,p,pe;
  ulong r;

  JgetTpe(J,&T,&pe,&p,&e);
  V1 = JgetV(J,1);
  KV1 = JgetKV(J,1);

  r = DivSub_dimval(V1,W,1,KV1,T,p,e,pe);
  avma = av;
  return r;
}

GEN PicChord(GEN J, GEN WA, GEN WB, long flag)
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
  WAWB = DivAdd(WA,WB,2*d0+1-g,T,p,e,pe,0);
  /* L(3D0-A-B) */
  WAB = DivSub(V1,WAWB,KV3,d0+1-g,T,p,e,pe,2);
  if(gc_needed(av,1)) WAB = gerepileupto(av,WAB);
  if(flag & 1) s = RandVec_padic(WAB,T,p,pe);
  else s = gel(WAB,1);
  /* s in WB: (s) = -3D0+A+B+C */
  /* L(5D0-A-B-C) */
  sV = DivMul(s,V,T,pe);
  /* L(2D0-C) */
  WC = DivSub(WAB,sV,KV,d0+1-g,T,p,e,pe,2);

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

GEN PicAdd(GEN J, GEN WA, GEN WB)
{
  pari_sp av = avma;
  GEN W;
  W = PicChord(J,WA,WB,0);
  W = PicNeg(J,W,0);
  return gerepileupto(av,W);
}

GEN PicSub(GEN J, GEN WA, GEN WB)
{
  pari_sp av = avma;
  GEN W;
  W = PicNeg(J,WB,0);
  W = PicChord(J,W,WA,0);
  return gerepileupto(av,W);
}

GEN PicMul(GEN J, GEN W, GEN n, long flag)
{ /* flag: 2: sign matters, 1: pass to PicChord and PicNeg */
  pari_sp av = avma;
  GEN C,Wlist,WA,WB;
  ulong nC,i;
  long a,b;

  if(gequal0(n)) return gcopy(JgetW0(J));
  if(gequal(n,gen_1)) return gcopy(W);
  C = AddFlipChain(n,flag&2);
  nC = lg(C);
  if(DEBUGLEVEL)
  {
    if(flag&2)
      pari_printf("   PicMul : Mul by %Ps in %lu steps\n",n,nC-2);
    else
      pari_printf("   PicMul : Mul by ±%Ps in %lu steps\n",n,nC-2);
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
        gel(Wlist,i) = PicChord(J,WA,WB,(i==nC-1)&&(flag&1));
      }
      else gel(Wlist,i) = PicNeg(J,WA,(i==nC-1)&&(flag&1));
    }
    else gel(Wlist,i) = b?PicNeg(J,gel(Wlist,b),(i==nC-1)&&(flag&1)):gcopy(JgetW0(J));
    /* Does not respect flag if a==b==0 but this is not supposed to happen */
  }
  return gerepileupto(av,gel(Wlist,nC-1));
}

GEN PicLC(GEN J, GEN C, GEN W)
{
/* Computes sum_i C[i]*W[i] in J
   C vector of t_INT coefficients, W vector of points on J */
  pari_sp av = avma;
  ulong i,j,n;
  GEN C1,W1,c,S;
  /* select nonzero coeffs */
  n = lg(C);
  C1 = cgetg(n,t_VEC);
  W1 = cgetg(n,t_VEC);
  j=1;
  for(i=1;i<n;i++)
  {
    if(!gequal0(gel(C,i)))
    {
      gel(C1,j) = gel(C,i);
      gel(W1,j) = gel(W,i);
      j++;
    }
  }
  if(j==1)
  { /* 0 linear combination */
    avma = av;
    return JgetW0(J);
  }
  c = gel(C1,1);
  if(j%2) c = negi(c);
  S = PicMul(J,gel(W1,1),c,2);
  for(i=2;i<j;i++)
  {
    /* Now S = (-1)^(j-i) sum_{k<i} C1[k]*W1[k] */
    c = gel(C1,i);
    if((j-i)%2) c = negi(c);
    S = PicChord(J,S,PicMul(J,gel(W1,i),c,2),0);
    /* Now S = (-1)^(j-i-1) sum_{k<=i} C1[i]*W1[k] */
  }
  return gerepileupto(av,S);
}

GEN TorsOrd(GEN J, GEN W, GEN l)
{
/*Given that W is an l-power torsion point of J,
finds v s.t. the order of W is l^v,
and returns [+-l^(v-1)W, v]*/
  pari_sp av = avma;
  GEN lW;
  ulong e,v;

  e = Jgete(J);
  lW = W;
  for(v=0;PicIsZero_val(J,lW)<e;v++)
  {
    W = lW;
    lW = PicMul(J,W,l,0);
  }
  W = mkvec2(W,utoi(v));
  return gerepilecopy(av,W);
}

GEN ZpXQ_FrobMat(GEN T, GEN p, long e, GEN pe)
{ /* Matrix of Frob on basis 1,t,t²,... of Z[t]/(T,p^e) */
  pari_sp av = avma;
  GEN F,M,col,Fj;
  long v = gvar(T),d = degpol(T),i,j;
  F = ZpX_Frobenius(T,p,e);
  M = cgetg(d+1,t_MAT);
  col = cgetg(d+1,t_COL);
  gel(col,1) = gen_1;
  for(i=2;i<=d;i++) gel(col,i) = gen_0;
  gel(M,1) = col;
  if(d==1) return gerepileupto(av,M);
  col = cgetg(d+1,t_COL);
  for(i=0;i<d;i++) gel(col,i+1) = polcoef(F,i,v);
  gel(M,2) = col;
  Fj = F;
  for(j=2;j<d;j++)
  {
    Fj = Fq_mul(Fj,F,T,pe);
    col = cgetg(d+1,t_COL);
    for(i=0;i<d;i++) gel(col,i+1) = polcoef(Fj,i,v);
    gel(M,j+1) = col;
  }
  return gerepilecopy(av,M);
}

GEN Frob(GEN x, GEN FrobMat, GEN T, GEN pe)
{
  pari_sp av = avma;
  GEN cx,cy,y;
  long var = gvar(T), d = degpol(T), i;
  cx = cgetg(d+1,t_COL);
  for(i=0;i<d;i++) gel(cx,i+1) = polcoef(x,i,var);
  cy = FpM_FpC_mul(FrobMat,cx,pe);
  y = cgetg(d+2,t_POL);
  y[1] = 0;
  setsigne(y,1);
  setvarn(y,var);
  for(i=1;i<=d;i++) gel(y,i+1) = gel(cy,i);
  y = normalizepol(y);
  return gerepilecopy(av,y);
}

GEN PicFrob(GEN J, GEN W)
{
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
      gcoeff(W2,FrobCyc[i],j) = Frob(gcoeff(W,i,j),FrobMat,T,pe);
  }
  return W2;
}

GEN PicFrobInv(GEN J, GEN W)
{
  pari_sp av = avma;
  GEN W2,T,pe,FrobMatInv,FrobCyc;
  ulong nW,nZ,i,j;

  T = JgetT(J);
  pe = Jgetpe(J);
  FrobMatInv = FpM_powu(JgetFrobMat(J),degpol(T)-1,pe); /* TODO carry in J? */
  FrobCyc = JgetFrobCyc(J);
  nW = lg(W);
  nZ = lg(FrobCyc);

  W2 = cgetg(nW,t_MAT);
  for(j=1;j<nW;j++)
  {
    gel(W2,j) = cgetg(nZ,t_COL);
    for(i=1;i<nZ;i++)
      gcoeff(W2,i,j) = Frob(gcoeff(W,FrobCyc[i],j),FrobMatInv,T,pe);
  }
  return gerepileupto(av,W2);
}

GEN PicFrobPow(GEN J, GEN W, long n)
{
  pari_sp av = avma;
  GEN W2,T,pe,M,cyc;
  ulong a,m,nW,nZ,i,j;

  T = JgetT(J);
  a = degpol(T);
  m = umodsu(n,a);
  if(m==0) return gcopy(W);
  if(m==1) return PicFrob(J,W);
  if(m==a-1) return PicFrobInv(J,W);
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
      gcoeff(W2,cyc[i],j) = Frob(gcoeff(W,i,j),M,T,pe);
  }
  return gerepileupto(av,W2);
}

GEN PicFrobPoly(GEN J, GEN W, GEN F)
{
  pari_sp av = avma;
  ulong d,i;
  GEN n,FW,res;

  d = degree(F);
  FW = W;
  n = truecoeff(F,0);
  if(d&1L) n = negi(n);
  res = PicMul(J,W,n,2);
  for(i=1;i<=d;i++)
  {
    FW = PicFrob(J,FW);
    n = truecoeff(F,i);
    if((d+1-i)&1L) n = negi(n);
    res = PicChord(J,res,PicMul(J,FW,n,2),0);
  }
  return gerepileupto(av,res);
}

GEN PicAut(GEN J, GEN W, ulong nAut)
{ /* TODO allow multiples */
  GEN W2,Cyc;
  long i,j,nW,nZ;

  Cyc = gel(JgetAutsCyc(J),nAut);
  RgM_dimensions(W,&nZ,&nW);

  W2 = cgetg(nW+1,t_MAT);
  for(j=1;j<=nW;j++)
  {
    gel(W2,j) = cgetg(nZ+1,t_COL);
    for(i=1;i<=nZ;i++)
    {
      gcoeff(W2,Cyc[i],j) = gcopy(gcoeff(W,i,j));
    }
  }

  return W2;
}

GEN PicChart(GEN J, GEN W, ulong P0, GEN P1) /* /!\ Not Galois-equivariant ! */
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
  K = matkerpadic(K,T,pe,p,e);
  if(lg(K)!=2)
  {
    pari_printf("Genericity 1 failed in PicChart\n");
    avma = av;
    return NULL;
  }
  s = FqM_FqC_mul(W,gel(K,1),T,pe); /* Generator of L(2D0-D-C) */

  sV = DivMul(s,V,T,pe); /* L(4D0-D-C-E_D), deg E_D = g */
  U = DivSub(W,sV,KV,d0+1-g,T,p,e,pe,2); /* L(2D0-C-E_D) */
  for(j=1;j<=nW;j++) /* Remove zero rows */
  {
    for(P=1;P<=n1;P++) gcoeff(U,P0+P,j) = gcoeff(U,P0+n1+P,j);
    setlg(gel(U,j),nZ-n1+1);
  }
  if(P1)
    U = Subspace_normalize(U,P1,T,pe,p,e,1);
  return gerepilecopy(av,mat2col(U));
}

GEN EvalRatMod(GEN F, long var, GEN x, GEN T, GEN p, long e, GEN pe) /* /!\ Not memory-clean */
{
  GEN N,D;
  if(typ(F)==t_INT) return scalarpol(F,varn(T));
  if(typ(F)==t_FRAC) return scalarpol(Fp_div(gel(F,1),gel(F,2),pe),varn(T));
  if(varn(F)==varn(T)) return F;
  if(gvar(F)!=var) pari_err(e_MISC,"Bad var 1 in %Ps",F);
  if(typ(F)==t_POL)
  {
    N = liftall(poleval(F,gmodulo(gmodulo(x,T),pe)));
    if(typ(N)==t_INT) N=scalarpol(N,varn(T));
    return N;
  }
  N = liftall(poleval(gel(F,1),gmodulo(gmodulo(x,T),pe)));
  if(typ(N)==t_INT) N=scalarpol(N,varn(T));
  D = liftall(poleval(gel(F,2),gmodulo(gmodulo(x,T),pe)));
  if(typ(D)==t_INT) D=scalarpol(D,varn(T));
  N = ZpXQ_div(N,D,T,pe,p,e);
  return N;
}

GEN FnEvalAt(GEN F, GEN P, GEN vars, GEN T, GEN p, long e/*GEN E*/, GEN pe)
/* F=N/D, N,D=R(y)x^n+...+R(y), R(y) rat fracs. Assumes P=(a,b) is s.t. the denom of R(b) is nonzero mod p for all R. */
{
  pari_sp av = avma;
  GEN N,D,Fy;
  long /*e = itos(E),*/d;
  ulong i;
  if(typ(F)==t_INT) return scalarpol(F,varn(T));
  if(typ(F)==t_FRAC) return scalarpol(Fp_div(gel(F,1),gel(F,2),pe),varn(T));
  if(typ(F)==t_RFRAC)
  {
    N = FnEvalAt(gel(F,1),P,vars,T,p,e,pe);
    if(typ(N)==t_INT) N=scalarpol(N,varn(T));
    D = FnEvalAt(gel(F,2),P,vars,T,p,e,pe);
    if(typ(D)==t_INT) D=scalarpol(D,varn(T));
    return gerepileupto(av,ZpXQ_div(N,D,T,pe,p,e));
  }
  if(gvar(F)==vars[2]) return liftall(poleval(F,gmodulo(gmodulo(gel(P,2),T),pe)));
  if(gvar(F)!=vars[1]) pari_err(e_MISC,"Bad var 2 in %Ps",F);
  d = lg(F);
  Fy = cgetg(d,t_POL);
  Fy[1] = 0;
  setsigne(Fy,1);
  setvarn(Fy,vars[1]);
  for(i=2;i<d;i++) gel(Fy,i) = EvalRatMod(gel(F,i),vars[2],gel(P,2),T,p,e,pe);
  F = liftall(poleval(Fy,gmodulo(gmodulo(gel(P,1),T),pe)));
  return gerepilecopy(av,F);
}

GEN FnsEvalAt(GEN Fns, GEN Z, GEN vars, GEN T, GEN p, long e, GEN pe)
{
  pari_sp av = avma;
  GEN A;//E;
  ulong nF,nZ;
  long i,j;//k;
  /*struct pari_mt pt;
  GEN worker,done;
  long pending,workid;*/

  /*E = stoi(e);*/
  nF = lg(Fns);
  nZ = lg(Z);
  A = cgetg(nF,t_MAT);
  for(j=1;j<nF;j++)
  {
    gel(A,j) = cgetg(nZ,t_COL);
    for(i=1;i<nZ;i++)
    {
      //printf("%ld,%ld\n",i,j);
      gcoeff(A,i,j) = FnEvalAt(gel(Fns,j),gel(Z,i),vars,T,p,e,pe);
    }
  }
  /* Abandoned parallel version (not useful)
  nF--;nZ--;
  pending = 0;
  worker = strtofunction("FnEvalAt");
  mt_queue_start(&pt,worker);
  for(k=0;k<nF*nZ||pending;k++)
  {
    if(k<nF*nZ)
    {
      i = 1 + (k%nZ);
      j = 1 + (k/nZ);
      printf("%ld,%ld\n",i,j);
      mt_queue_submit(&pt,k,mkvecn(7,gel(Fns,j),gel(Z,i),vars,T,p,E,pe));
    }
    else mt_queue_submit(&pt,k,NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done)
    {
      i = 1 + (k%nZ);
      j = 1 + (k/nZ);
      gcoeff(A,i,j) = done;
    }
  }*/
  return gerepilecopy(av,A);
}

GEN FnsEvalAt_Rescale(GEN Fns, GEN Z, GEN vars, GEN T, GEN p, long e, GEN pe)
{
  pari_sp av = avma;
  GEN F,S,K,f,redo,rF;
  ulong i,j,k,nF,nK;
  F = gcopy(Fns);
  nF = lg(F);
  S = FnsEvalAt(F,Z,vars,T,p,e,pe);
  while(1)
  {
    K = FqM_ker(S,T,p);
    nK = lg(K);
    /* Are the evals (and hence the fns) independent ? */
    if(nK==1)
    {
      if(DEBUGLEVEL) printf("Good, no relation\n");
      return gerepileupto(av,S);
    }
    pari_printf("Found %ld relations, eliminating and re-evaluating\n",nK-1);
    /* No. We assume Z def / Q, so K has entries in Fp */
    /* Do elimination and start over */
    redo = cgetg(nK,t_VECSMALL);
    rF = cgetg(nK,t_VEC);
    for(j=1;j<nK;j++)
    {
      /* k = pivot = last nonzero entry of the col (it's a 1) */
      k = 0;
      for(i=1;i<nF;i++)
      {
        if(!gequal0(gcoeff(K,i,j))) k=i;
      }
      redo[j]=k;
      /* Form corresponding lin comb, and div by p */
      f = gel(F,k);
      for(i=1;i<k;i++)
      {
        if(!gequal0(gcoeff(K,i,j)))
        {
          f = gadd(f,gmul(centerlift(gmodulo(gcoeff(K,i,j),p)),gel(F,i)));
        }
      }
      gel(F,k) = gel(rF,j) = gdiv(f,p);
    }
    rF = FnsEvalAt(rF,Z,vars,T,p,e,pe);
    for(j=1;j<nK;j++) gel(S,redo[j]) = gel(rF,j);
  }
}

GEN Fn1_FieldOfDef(GEN f, long var)
{
  GEN W,W1,c;
  long i,d;
  if(typ(f)==t_RFRAC)
  {
    W1 = Fn1_FieldOfDef(gel(f,1),var);
    W = Fn1_FieldOfDef(gel(f,2),var);
    if(W1 && W && !gequal(W1,W)) pari_err(e_MODULUS,"function",W1,W);
    return W1?W1:W;
  }

  if(typ(f)==t_POL)
  {
    W = NULL;
    d = poldegree(f,var);
    for(i=0;i<=d;i++)
    {
      c = polcoef(f,i,var);
      if(typ(c)==t_POLMOD)
      {
        W1=gel(c,1);
        if(W && !gequal(W1,W)) pari_err(e_MODULUS,"function",W1,W);
        W = W1;
      }
    }
    return W;
  }
  if(typ(f)==t_POLMOD) return gel(f,1);
  return NULL;
}

GEN Fn2_FieldOfDef(GEN f, GEN vars)
{
  GEN W,W1,c;
  long i,d;
  if(typ(f)==t_RFRAC)
  {
    W1 = Fn2_FieldOfDef(gel(f,1),vars);
    W = Fn2_FieldOfDef(gel(f,2),vars);
    if(W1 && W && !gequal(W1,W)) pari_err(e_MODULUS,"function",W1,W);
    return W1?W1:W;
  }

  if(typ(f)==t_POL)
  {
    W = NULL;
    d = poldegree(f,vars[1]);
    for(i=0;i<=d;i++)
    {
      c = polcoef(f,i,vars[1]);
      W1 = Fn1_FieldOfDef(c,vars[2]);
      if(W1)
      {
        if(W && !gequal(W1,W)) pari_err(e_MODULUS,"function",W1,W);
        W = W1;
      }
    }
    return W;
  }
  if(typ(f)==t_POLMOD) return gel(f,1);
  return NULL;
}

GEN RRspace_FieldOfDef(GEN L, GEN vars)
{
  GEN W,W1;
  ulong n,i;
  n = lg(L);
  W = NULL;
  for(i=1;i<n;i++)
  {
    W1 = Fn2_FieldOfDef(gel(L,i),vars);
    if(W1)
    {
      if(W && !gequal(W1,W)) pari_err(e_MODULUS,"function",W1,W);
      W = W1;
    }
  }
  return W;
}

GEN RRspaceEval(GEN L, GEN vars, GEN pts, GEN T, GEN p, long e, GEN pe)
{
  pari_sp av = avma;
  long w,dW;
  GEN W,S,s,Li,res;
  ulong i;

  W = RRspace_FieldOfDef(L,vars);
  if(W) /* Algebraic case */
  {
    /* Get field of definition */
    w = gvar(W);
    dW = poldegree(W,w);
    /* Lift */
    L = liftpol(L);
    /* Find embeddings into Qp[t]/(T) */
    S = polrootsmod(W,mkvec2(T,p));
    if(lg(S) < dW+1) /* Should have all embeddings */
      pari_err(e_MISC,"Field of definition of Riemann-Roch space cannot be totally embedded into Q_q");
    res = cgetg(dW+1,t_VEC);
    for(i=1;i<=dW;i++)
    {
      s = gel(S,i); /* Embedding mod p */
      s = liftint(s);
      s = gadd(s,zeropadic(p,e));
      s = padicappr(W,s);
      s = gel(s,1);
      s = liftint(s);
      s = gmodulo(s,pe);
      Li = gsubst(L,w,s);
      Li = liftall(Li);
      /* TODO if there is a rescale, loss of p-adic accuracy? */
      gel(res,i) = FnsEvalAt_Rescale(Li,pts,vars,T,p,e,pe);
    }
    return gerepilecopy(av,res);
  }
  else /* Rational case */
  {
    avma = av;
    return mkvec(FnsEvalAt_Rescale(L,pts,vars,T,p,e,pe));
  }
}

GEN CurveLiftPty(GEN fx, GEN y, GEN T, GEN p, long e)
{
  pari_sp av = avma;
  y = gmodulo(liftall(y),T);
  y = gadd(y,zeropadic(p,e));
  y = padicappr(fx,y);
  y = gel(y,1);
  y = liftall(y);
  return gerepileupto(av,y);
}

GEN CurveRandPt(GEN f, GEN T, GEN p, long e, GEN bad)
{
  pari_sp av = avma, av1;
  long vT,dT;
  GEN vars,x,fx,y,badpt,dfx,dy,P;
  vT = varn(T);
  dT = degree(T);
  vars = variables_vecsmall(f);
  av1 = avma;
  for(;;)
  {
    avma = av1;
    x = random_FpX(dT,vT,p);
    if(ZX_is0mod(x,p)) continue; /* Want x != 0 */
    fx = poleval(f,x);
    y = polrootsmod(fx,mkvec2(T,p));
    if(lg(y)==1) continue; /* No roots */
    y = gel(y,itos(genrand(stoi(lg(y)-1)))+1);
    badpt = FnEvalAt(bad,mkvec2(x,liftall(y)),vars,T,p,1,p);
    badpt = Fq_red(badpt,T,p);
    if(gequal0(badpt)) continue; /* Forbidden locus */
    dfx = RgX_deriv(fx);
    dy = poleval(dfx,y);
    if(gequal0(dy)) continue; /* Bad for Hensel */
    y = CurveLiftPty(fx,y,T,p,e);
    P = mkvec2(x,y);
    return gerepilecopy(av,P);
  }
}

GEN PicEvalInit(GEN L, GEN vars, GEN Z, GEN V2, GEN T, GEN p, long e, GEN pe)
{
  pari_sp av = avma;
  GEN res,I,M;
  ulong i,j,nV2;
  res = cgetg(5,t_VEC);
  for(i=1;i<=2;i++) /* TODO parallelise */
    gel(res,i) = RRspaceEval(gel(L,i+2),vars,Z,T,p,e,pe);
  nV2 = lg(V2);
  I = FqM_indexrank(V2,T,p);
  I = gel(I,1); /* Rows of V2 forming invertible block */
  gel(res,3) = I;
  /* That invertible block */
  M = cgetg(nV2,t_MAT);
  for(j=1;j<nV2;j++)
  {
    gel(M,j) = cgetg(nV2,t_COL);
    for(i=1;i<nV2;i++)
      gcoeff(M,i,j) = gcoeff(V2,I[i],j);
  }
  gel(res,4) = ZpXQMinv(M,T,pe,p,e);
  return gerepilecopy(av,res);
}

ulong FindMod(GEN P, GEN Z, ulong n, GEN p, int check)
{ /* Finds 1<=i<=n such that P = Z[i] mod p, else returns 0 */
  pari_sp av = avma;
  ulong i;
  GEN Pp;
  if(n==0) return 0; /* Empty list */
  Pp = FpXV_red(P,p);
  for(i=1;i<=n;i++)
  {
    if(gequal(Pp,FpXV_red(gel(Z,i),p)))
    {
      if(check && !gequal(P,gel(Z,i))) pari_err(e_MISC,"Points agree mod p but not mod pe");
      avma = av;
      return i;
    }
  }
  avma = av;
  return 0;
}

GEN CurveApplyAut(GEN aut, GEN P, GEN vars, GEN T, GEN pe, GEN p, long e)
{ /* aut = [X,Y,Z] function of x,y. Return [X/Z,Y/Z]. */
  pari_sp av = avma;
  GEN a,b,c,Q;
  a = FnEvalAt(gel(aut,1),P,vars,T,p,e,pe);
  b = FnEvalAt(gel(aut,2),P,vars,T,p,e,pe);
  c = FnEvalAt(gel(aut,3),P,vars,T,p,e,pe);
  c = ZpXQ_inv(c,T,p,e);
  Q = cgetg(3,t_VEC);
  gel(Q,1) = FpXQ_mul(a,c,T,pe);
  gel(Q,2) = FpXQ_mul(b,c,T,pe);
  return gerepileupto(av,Q);
}

GEN CurveApplyFrob(GEN P, GEN FrobMat, GEN T, GEN pe)
{
  pari_sp av = avma;
  GEN Q;
  Q = cgetg(3,t_VEC);
  gel(Q,1) = Frob(gel(P,1),FrobMat,T,pe);
  gel(Q,2) = Frob(gel(P,2),FrobMat,T,pe);
  return gerepileupto(av,Q);
}

GEN VecExtend(GEN V)
{ /* Doubles length, leaves second half uninitialised */
  ulong n = lg(V),i;
  GEN V2;
  V2 = cgetg(2*n,t_VEC);
  for(i=1;i<n;i++) gel(V2,i) = gel(V,i);
  return V2;
}

GEN VecSmallExtend(GEN V)
{ /* Doubles length, leaves second half uninitialised */
  ulong n = lg(V),i;
  GEN V2;
  V2 = cgetg(2*n,t_VECSMALL);
  for(i=1;i<n;i++) V2[i] = V[i];
  return V2;
}

GEN CurveAutFrobClosure(GEN P, GEN Auts, GEN vars, GEN FrobMat, GEN T, GEN pe, GEN p, long e)
{ /* Orbit of point P under Frob and Auts, and induced permutations */
  pari_sp av = avma;
  GEN OP,sFrob,sAuts,res;
  ulong nAuts,nO,nmax;
  ulong i,j,k,m,n;

  OP = cgetg(2,t_VEC); /* Orbit of P, will grow as needed */
  gel(OP,1) = P;
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
        for(;;)
        {
          /* Apply aut to P */
          if(i) P = CurveApplyAut(gel(Auts,i),P,vars,T,pe,p,e);
          else P = CurveApplyFrob(P,FrobMat,T,pe);
          /* Is the result a point we already know? */
          k = FindMod(P,OP,nO,p,1);
          if(k)
          { /* We're back to a pt we know, stop search */
            (i?gel(sAuts,i):sFrob)[m] = k;
            break;
          }
          /* This is a new pt. Add it to orbit and create placeholders for its transfos */
          nO++;
          (i?gel(sAuts,i):sFrob)[m] = nO;
          if(nO==nmax) /* Must extend all vectors */
					{
            nmax*=2;
            OP = VecExtend(OP);
            sFrob = VecSmallExtend(sFrob);
            for(j=1;j<nAuts;j++) gel(sAuts,j) = VecSmallExtend(gel(sAuts,j));
          }
          gel(OP,nO)=P;
          m = nO;
          sFrob[nO]=0;
          for(j=1;j<nAuts;j++) gel(sAuts,j)[nO]=0;
        }
      }
    }
  }
  setlg(OP,nO+1);
  setlg(sFrob,nO+1);
  for(i=1;i<nAuts;i++) setlg(gel(sAuts,i),nO+1);
  res = mkvecn(3,OP,sFrob,sAuts);
  return gerepilecopy(av,res);
}

GEN PicInit(GEN f, GEN Auts, ulong g, ulong d0, GEN L, GEN bad, GEN p, ulong a, long e)
{
  pari_sp av = avma;
  long t;
  ulong nZ,nAuts,n,nOP,m,i;
  GEN vars,pe,T,FrobMat,Z,P,FrobCyc,AutsCyc,OP,V1,V2,V3,W0,V,KV,U,J;
  struct pari_mt pt;
  GEN worker,done,E;
  long workid,pending,k;

  vars = variables_vecsmall(f);
  nZ = 5*d0+1; /* min required #pts */

  t = fetch_var();
  name_var(t,"t");
  T = liftint(ffinit(p,a,t));
  pe = powis(p,e);
  FrobMat = ZpXQ_FrobMat(T,p,e,pe);

  if(DEBUGLEVEL) printf("PicInit: Finding points\n");
  n = 0; /* current #pts */
  Z = cgetg(1,t_VEC); /* list of pts */
  /* Initialise empty cycles */
  FrobCyc = cgetg(1,t_VECSMALL);
  nAuts = lg(Auts);
  AutsCyc = cgetg(nAuts,t_VEC);
  for(i=1;i<nAuts;i++)
    gel(AutsCyc,i) = cgetg(1,t_VECSMALL);
  /* Loop until we have enough pts */
  while(n<nZ)
  {
    /* Get new point */
    P = CurveRandPt(f,T,p,e,bad);
    /* Is it new mod p ? */
    if(FindMod(P,Z,n,p,0)) continue;
    if(DEBUGLEVEL) printf("Got new pt\n");
    /* Compute closure under Frob and Auts */
    OP = CurveAutFrobClosure(P,Auts,vars,FrobMat,T,pe,p,e);
    nOP = lg(gel(OP,1))-1; /* # new pts */
    if(DEBUGLEVEL) printf("Got closure of size %lu\n",nOP);
    /* Add new pts */
    Z = gconcat(Z,gel(OP,1));
    /* Shift permutation describing Frob and Auts */
    for(m=1;m<=nOP;m++)
    {
      gel(OP,2)[m] += n;
      for(i=1;i<nAuts;i++)
        gmael(OP,3,i)[m] += n;
    }
    /* Add these permutaton data */
    FrobCyc = gconcat(FrobCyc,gel(OP,2));
    for(i=1;i<nAuts;i++)
      gel(AutsCyc,i) = gconcat(gel(AutsCyc,1),gmael(OP,3,i));
    /* Update # pts */
    n += nOP;
  }

  if(DEBUGLEVEL) printf("PicInit: Evaluating rational functions\n");
  V1 = FnsEvalAt_Rescale(gel(L,1),Z,vars,T,p,e,pe);
  V2 = FnsEvalAt_Rescale(gel(L,2),Z,vars,T,p,e,pe);
  V3 = DivAdd(V1,V2,3*d0+1-g,T,p,e,pe,0);
  W0 = V1;
  V = mkvecn(3,V1,V2,V3);
  if(DEBUGLEVEL) printf("PicInit: Computing equation matrices\n");
  KV = cgetg(4,t_VEC);
  E = stoi(e);
  worker = strtofunction("mateqnpadic");
  mt_queue_start_lim(&pt,worker,3);
  for(k=1;k<=3||pending;k++)
  {
    mt_queue_submit(&pt,k,k<=3?mkvecn(5,gel(V,k),T,pe,p,E):NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done) gel(KV,workid) = done;
  }
  mt_queue_end(&pt);
  if(DEBUGLEVEL) printf("PicInit: Constructing evaluation maps\n");
  U = PicEvalInit(L,vars,Z,V2,T,p,e,pe);
  J = mkvecn(lgJ,f,stoi(g),stoi(d0),L,T,p,stoi(e),pe,FrobMat,V,KV,W0,U,Z,FrobCyc,AutsCyc);
  return gerepilecopy(av,J);
}

GEN Jlift(GEN J, ulong e2)
{
  pari_sp av = avma, avZ;
  GEN J2,T,p,pe2,f,vars,L,FrobCyc,FrobMat2;
  long g,d0;
  GEN Z,Z2,V,W0,KV,P,x,y,fx,U,V2,I,M;
  ulong nZ,i,j,nV2;
  struct pari_mt pt;
  GEN worker,done,E2;
  long pending,k,workid;
  if(Jgete(J)>=e2)
  {
    pari_warn(warner,"Current accuracy already higher than required in Jlift, not changing anything");
    return gcopy(J);
  }
  f = Jgetf(J);
  if(gequal0(f))
    pari_err(e_MISC,"Cannot increase accuracy for this curve (missing equation)");
  L = JgetL(J);
  if(lg(L)!=5)
    pari_err(e_MISC,"Cannot increase accuracy for this curve (missing RR spaces)");
  Z = JgetZ(J);
  if(lg(Z)==1)
    pari_err(e_MISC,"Cannot increase accuracy for this curve (missing points)");
  T = JgetT(J);
  p = Jgetp(J);
  vars = variables_vecsmall(f);
  g = Jgetg(J);
  d0 = Jgetd0(J);

  J2 = cgetg(lgJ+1,t_VEC);
  gel(J2,1) = f;
  gel(J2,2) = stoi(g);
  gel(J2,3) = stoi(d0);
  gel(J2,4) = L;
  gel(J2,5) = T;
  gel(J2,6) = p;
  gel(J2,7) = E2 = utoi(e2);
  gel(J2,8) = pe2 = powiu(p,e2);
  gel(J2,9) = FrobMat2 = ZpXQ_FrobMat(T,p,e2,pe2);

  nZ = lg(Z);
  FrobCyc = JgetFrobCyc(J);
  avZ = avma;
  Z2 = cgetg(nZ,t_VEC);
  /* Need to lift while respecting Frob orbits */
  for(i=1;i<nZ;i++) /* Mark points as not done */
    gel(Z2,i) = NULL;
  for(i=1;i<nZ;i++)
  {
    if(gel(Z2,i)) continue; /* This point is part of a Frob orbit we have already treated */
    j = i; /* Start of a new orbit */
    P = gel(Z,i); /* Arbitrarily lift this point only */
    x = gel(P,1);
    y = gel(P,2);
    fx = poleval(f,x);
    y = CurveLiftPty(fx,y,T,p,e2);
    while(1)
    {
      gel(Z2,j) = mkvec2(x,y);
      j = FrobCyc[j];
      if(j==i) break; /* End of orbit */
      x = Frob(x,FrobMat2,T,pe2);
      y = Frob(y,FrobMat2,T,pe2);
    }
  }
  Z2 = gerepilecopy(avZ,Z2);
  V = cgetg(4,t_VEC);
  KV = cgetg(4,t_VEC);
  U = cgetg(5,t_VEC);
  /* TODO why does that parallel version not work?
  printf("RR\n");
  worker = strtofunction("RRspaceEval");
  mt_queue_start(&pt,worker);
  for(k=1;k<=4||pending;k++)
  {
    mt_queue_submit(&pt,k,k<=4?mkvecn(7,gel(L,k),vars,Z2,T,p,E2,pe2):NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done)
    {
      if(workid<=2) gel(V,workid) = gel(done,1);
      else gel(U,workid-2) = done;
    }
  }
  mt_queue_end(&pt);
  printf("End RR\n"); */
  gel(V,1) = gel(RRspaceEval(gel(L,1),vars,Z2,T,p,e2,pe2),1);
  V2 = gel(V,2) = gel(RRspaceEval(gel(L,2),vars,Z2,T,p,e2,pe2),1);
  gel(U,1) = RRspaceEval(gel(L,3),vars,Z2,T,p,e2,pe2);
  gel(U,2) = RRspaceEval(gel(L,4),vars,Z2,T,p,e2,pe2);
  gel(V,3) = DivAdd(gel(V,1),gel(V,2),3*d0+1-g,T,p,e2,pe2,0);
  W0 = gel(V,1); /* TODO can it happen that W0 != V1 even though all data is present? */
  I = gel(U,3) = gmael(J,13,3);
  nV2 = lg(V2);
  M = cgetg(nV2,t_MAT);
  for(j=1;j<nV2;j++)
  {
    gel(M,j) = cgetg(nV2,t_COL);
    for(i=1;i<nV2;i++)
      gcoeff(M,i,j) = gcoeff(V2,I[i],j);
  }
  gel(U,4) = ZpXQMinv(M,T,pe2,p,e2);
  worker = strtofunction("mateqnpadic");
  mt_queue_start_lim(&pt,worker,3);
  for(k=1;k<=3||pending;k++)
  {
    mt_queue_submit(&pt,k,k<=3?mkvecn(5,gel(V,k),T,pe2,p,E2):NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done) gel(KV,workid) = done;
  }
  mt_queue_end(&pt);
  gel(J2,10) = V;
  gel(J2,11) = KV;
  gel(J2,12) = W0;
  gel(J2,13) = U;
  gel(J2,14) = Z2;
  gel(J2,15) = JgetFrobCyc(J);
  gel(J2,16) = JgetAutsCyc(J);
  return gerepilecopy(av,J2);
}

GEN PicEval(GEN J, GEN W)
{
  pari_sp av = avma, av1, av2;
  GEN T,p,pe,V,KV,U,res,resi1;
  long e;
  ulong n1,n2,i1,i2;
  GEN S1,S2,I,M,s2,s2I,K;
  ulong d0,g,nV,i;

  JgetTpe(J,&T,&pe,&p,&e);
  d0 = Jgetd0(J);
  g = Jgetg(J);
  V = JgetV(J,2);
  nV = lg(V);
  KV = JgetKV(J,2);
  U = JgetEvalData(J); /* L(2D0-Ei), deg Ei = d0-g (i=1,2), repeated for each embedding into Qq */
  n1 = lg(gel(U,1)); /* Deg of E1 / Q */
  n2 = lg(gel(U,2)); /* Deg of E2 / Q */
  I = gel(U,3); /* Row indices to look at to ID an elt of V */
  M = gel(U,4); /* Matrix to apply to the I-entries */

  res = cgetg(n1,t_MAT);
  for(i1=1;i1<n1;i1++)
  {
    av1 = avma;
    S1 = DivAdd(W,gmael(U,1,i1),2*d0+1,T,p,e,pe,0); /* L(4D0-D-E1) */
    S1 = DivSub(V,S1,KV,1,T,p,e,pe,2); /* L(2D0-D-E1), generically 1-dimensional */
    S1 = gerepileupto(av1,gel(S1,1));
    S1 = DivMul(S1,V,T,pe); /* L(4D0-D-E1-ED) */
    S1 = gerepileupto(av1,S1);
    S1 = DivSub(W,S1,KV,d0+1-g,T,p,e,pe,2); /* L(2D0-E1-ED) */
    S1 = gerepileupto(av1,S1);
    resi1 = cgetg(n2,t_COL);
    for(i2=1;i2<n2;i2++)
    {
      av2 = avma;
      S2 = DivAdd(S1,gmael(U,2,i2),2*d0+1,T,p,e,pe,0); /* L(4D0-E1-E2-ED) */
      S2 = gerepileupto(av2,S2);
      S2 = DivSub(V,S2,KV,1,T,p,e,pe,2); /* L(2D0-E1-E2-ED), generically 1-dimensional */
      s2 = gel(S2,1); /* Generator */
      s2 = gerepileupto(av2,s2);
      /* get coords of s2 w.r.t. V */
      s2I = cgetg(nV,t_COL);
      for(i=1;i<nV;i++)
        gel(s2I,i) = gel(s2,I[i]);
      K = FqM_FqC_mul(M,s2I,T,pe);
      gel(resi1,i2) = gerepileupto(av2,K);
    }
    gel(res,i1) = gerepileupto(av1,resi1);
  }
  return gerepileupto(av,res);
}

GEN PicEval_worker(GEN W, GEN J)
{
  return PicEval(J,W);
}

/* Lift */

GEN PicDeflate(GEN J, GEN W, ulong nIGS)
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
		avma = av;
		for(i=1;i<=nIGS;i++) gel(IGS,i) = RandVec_padic(W,T,p,pe);
		av1 = avma;
		IV = cgetg(nIGS*nV+1,t_MAT);
		k=1;
		for(i=1;i<=nIGS;i++)
		{
			wV = DivMul(gel(IGS,i),V,T,p);
			for(j=1;j<=nV;j++)
			{
				gel(IV,k) = gel(wV,j);
				k++;
			}
		}
		r = FqM_rank(IV,T,p);
		if(r==nV+nW+g-1)
		{
			avma = av1;
			return IGS;
		}
		printf("IGS[%lu,%lu]\n",r,nV+nW+g-1);
	}
}

GEN PicDeflate_U(GEN J, GEN W, ulong nIGS)
{
	pari_sp av = avma;
	GEN V,T,pe,p;
	long e;
	ulong nV;
	GEN GW,K,U;
	ulong j;

	JgetTpe(J,&T,&pe,&p,&e);
	V = JgetV(J,2);
	nV = lg(V);

	GW = PicDeflate(J,W,nIGS); /* IGS of W */
  K = cgetg(nV+nIGS,t_MAT);
  for(j=1;j<nV;j++) gel(K,j) = gel(V,j);
  for(j=1;j<=nIGS;j++) gel(K,nV-1+j) = gel(GW,j);
  U = matkerpadic(K,T,pe,p,e); /* Coords of IGS of W // basis of V */ /* TODO use M from eval data */
  for(j=1;j<=nIGS;j++) setlg(gel(U,j),nV);
  return gerepilecopy(av,U);
}

GEN PicInflate_U(GEN J, GEN U, GEN I) /* Takes IGS given by coords // V */
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
    wV = DivMul(FqM_FqC_mul(V,gel(U,i),T,pe),V,T,pe); /* TODO useful to precompte V[i]*V ? */
    for(j=1;j<=nV;j++)
    {
      gel(GWV,k) = gel(wV,j);
      k++;
    }
  }
  GWV = FqM_image(GWV,T,p);
  W = DivSub(V,GWV,KV,nW,T,p,e,pe,3); /* TODO pass precomputed IGS of V */
	if(I) /* Change basis to make block = 1 */
		W = Subspace_normalize(W,I,T,pe,p,e,0);
	return gerepileupto(av,W);
}

GEN PicLift_worker(GEN V0j, ulong shift, GEN uv, GEN AinvB, GEN CAinv, GEN T, GEN pe21)
{
	pari_sp av = avma; /* TODO save mem? */
	GEN abcd,drho;
	abcd = M2ABCD_1block(V0j,0,shift,uv); /* Split */
  drho = ZXM_sub(FqM_mul(gel(abcd,1),AinvB,T,pe21),gel(abcd,2)); /* aA^-1B-b */
	drho = FqM_mul(CAinv,drho,T,pe21); /* CA^-1aA^-1B - CA^-1b */
	drho = ZXM_add(gel(abcd,4),drho); /* d + CA^-1aA^-1B - CA^-1b */
	drho = ZXM_sub(drho,FqM_mul(gel(abcd,3),AinvB,T,pe21)); /* d + CA^-1aA^-1B - CA^-1b - cA^-1B */
	drho = mat2col(drho);
	return gerepilecopy(av,drho);
}

GEN PicLift_RandLift_U(GEN U, GEN U0, GEN KM, GEN T, GEN p, GEN pe1, GEN pe21, long e21)
{
	pari_sp av;

	GEN K,red,newU;
	ulong nU,nU0,nV;
	ulong i,j,k,m;

	nU = lg(U);
	nU0 = lg(U0);
	nV = lg(gel(U,1));

	av=avma;
  do
  { /* Get random vector in KM with nonzero last entry */
    avma=av;
    K = RandVec_1(KM,pe21);
    red = gel(K,lg(K)-1);
  } while(ZX_is0mod(red,p));
	/* Divide by last entry */
  red = ZpXQ_inv(red,T,p,e21);
  setlg(K,lg(K)-1);
  K = FqC_Fq_mul(K,red,T,pe21);
  newU = gcopy(U);
  k = 1;
  for(i=1;i<nU;i++)
  {
		/* Correct U[i] */
    for(j=1;j<nU0;j++)
    { /* Add the proper multiple of U0[j] to it */
      for(m=1;m<nV;m++)
        gmael(newU,i,m) =
					ZX_add(gmael(newU,i,m),ZX_Z_mul(Fq_mul(gel(K,k),gcoeff(U0,m,j),T,pe21),pe1));
      k++;
    }
  }
	return gerepileupto(av,newU);
}

GEN PicLiftTors_Chart_worker(GEN randseed, GEN J, GEN l, GEN U, GEN U0, GEN I, GEN KM, GEN pe1, GEN pe21, long e21, GEN c0, ulong P0, GEN P1)
{
  pari_sp av=avma,avU;
	GEN T,p,pe2;
	long e2;
	GEN W,c,res;
  ulong nc,i;
  setrand(randseed);
	JgetTpe(J,&T,&pe2,&p,&e2);
  nc = lg(c0)-1;

	res = cgetg(3,t_VEC);
	/* Get a random lift */
	gel(res,1) = U = PicLift_RandLift_U(U,U0,KM,T,p,pe1,pe21,e21);
  avU = avma;
	W = PicInflate_U(J,U,I);
	W = PicMul(J,W,l,0);
	W = gerepileupto(avU,W);
  /* Mul by l, get coordinates, and compare them to those of W0 */
  c = PicChart(J,W,P0,P1);
	if(c==NULL)
	{
		avma = av;
		return gen_0;
	}
	c = gerepileupto(avU,c);
  for(i=1;i<=nc;i++) /* The coords are c0 mod pe1 -> divide */
		gel(c,i) = ZX_Z_divexact(FpX_sub(gel(c,i),gel(c0,i),pe2),pe1);
	gel(res,2) = gerepileupto(avU,c);
	return res;
}

GEN PicLiftTors(GEN J, GEN W, long eini, GEN l)
{
  pari_sp av=avma,av1,av2,av3,avrho,avtesttors;
	GEN T,p,V;
  long efin,e1,e2,e21,efin2;
  GEN pefin,pe1,pe21,pe2,pefin2;
  GEN J1,J2;
  GEN sW,Vs,U0,V0;
  GEN K,U,U2;
	GEN GWV,wV;
  GEN ABCD,uv,Ainv,CAinv,AinvB,rho;
  GEN KM,red;
  ulong g,nZ,nW;
  ulong nGW=2,nV,d0,nc,P0=0;
	GEN c0=NULL,P1=NULL;
	int P0_tested=0,liftsOK=0;
	GEN Clifts,Ulifts,Ktors;
	struct pari_mt pt;
  GEN randseed,vFixedParams,args,worker,done;
  long pending,workid;
  ulong r,i,j,k,n;
	ulong testtors;

	JgetTpe(J,&T,&pefin,&p,&efin);
	if(eini >= efin) return W;
	g = Jgetg(J);
  d0 = Jgetd0(J);
  V = JgetV(J,2);
  /*GV = JgetGV(J2);*/
  nV = lg(V)-1;
  nZ = lg(gel(V,1))-1;
  nW = lg(W)-1;

  sW = gel(FqM_indexrank(W,T,p),1); /* rows s.t. this block is invertible, # = nW, we won't change them */
  Vs = cgetg(nV+1,t_MAT); /* V with only the rows in sW */
  for(j=1;j<=nV;j++)
  {
    gel(Vs,j) = cgetg(nW+1,t_COL);
    for(i=1;i<=nW;i++) gcoeff(Vs,i,j) = gcoeff(V,sW[i],j);
  }
	efin2 = efin/2; /* Upper bound for e21 for all iterations */
	pefin2 = powis(p,efin2);
	U0 = matkerpadic(Vs,T,pefin2,p,efin2); /* # = nV-nW = d0 */
	V0 = cgetg(d0+1,t_VEC);
	for(i=1;i<=d0;i++) gel(V0,i) = DivMul(FqM_FqC_mul(V,gel(U0,i),T,pefin2),V,T,pefin2); /* s*V for s in subspace of V whose rows in sW are 0 */
	/* TODO parallel? */

	e1 = eini;
	pe1 = powiu(p,e1);
	av1 = avma; /* Use to collect garbage at each iteration */
	J1 = PicRed(J,e1);
	U = PicDeflate_U(J1,W,nGW); /* IGS of W1 // basis of V */
	U = gerepileupto(av1,U);

	r = 3*d0+1-g; /* Wanted rank of GWV */
	/* Main loop */
  while(1)
  {
    e2 = 2*e1;
    if(e2>efin) e2 = efin;
		e21 = e2-e1;
		pe21 = e21==e1 ? pe1 : powiu(p,e21);
    pari_printf("Lifting from prec O(%Ps^%lu) to O(%Ps^%lu)\n",p,e1,p,e2);
    J2 = e2<efin ? PicRed(J,e2) : J;
		pe2 = Jgetpe(J2);
		/* START LIFTING */
  	GWV = cgetg(nGW*nV+1,t_MAT); /* w*V for w in GW */
		/* We need it to have rk r, it is already the case mod pe1 */
  	k = 1;
  	for(i=1;i<=nGW;i++)
  	{
    	wV = DivMul(FqM_FqC_mul(V,gel(U,i),T,pe2),V,T,pe2);
    	for(j=1;j<=nV;j++)
    	{
      	gel(GWV,k) = gel(wV,j);
      	k++;
    	}
  	}
  	
		avrho = avma;
  	uv = FqM_MinorCompl(GWV,T,p); /* How to split GWV */
  	ABCD = M2ABCD(GWV,uv); /* Splitting */
  	Ainv = ZpXQMinv(gel(ABCD,1),T,pe2,p,e2);
  	CAinv = FqM_mul(gel(ABCD,3),Ainv,T,pe2);
  	AinvB = FqM_mul(Ainv,gel(ABCD,2),T,pe2);
  	rho = FqM_mul(CAinv,gel(ABCD,2),T,pe2);
  	rho = FpXM_sub(gel(ABCD,4),rho,pe2); /* size nZ-r,nGW*nV-r(=dW if nGW-2); tests if rk = r */
  	for(i=1;i<=nZ-r;i++)
  	{
    	for(j=1;j<=nGW*nV-r;j++) gcoeff(rho,i,j) = ZX_Z_divexact(gcoeff(rho,i,j),pe1);
    }
		
  	/* Now deform the w in GW by p^e1*V0. Actually we deform U1 by p^e1*U0. */
  	/* TODO do not deform U1[1]? */
  	K = cgetg(nGW*d0+2,t_MAT);
		vFixedParams = cgetg(6,t_VEC);
		gel(vFixedParams,1) = uv;
		gel(vFixedParams,2) = AinvB;
		gel(vFixedParams,3) = CAinv;
		gel(vFixedParams,4) = T;
		gel(vFixedParams,5) = pe21;
		args = cgetg(3,t_VEC);
		worker = snm_closure(is_entry("PicLift_worker"),vFixedParams);
		pending = 0;
    i = 1;
		j = 1;
		mt_queue_start_lim(&pt,worker,nGW*d0);
		for(k=1;k<=nGW*d0||pending;k++)
    {
			if(k<=nGW*d0)
      { /* GW[i] shifts by p^e1*V0[j] */
				gel(args,1) = gel(V0,j);
				gel(args,2) = utoi((i-1)*nV);
				mt_queue_submit(&pt,k,args);
				j++;
				if(j>d0) {j=1;i++;}
			}
			else mt_queue_submit(&pt,k,NULL);
			done = mt_queue_get(&pt,&workid,&pending);
      if(done) gel(K,workid) = done;
		}
    mt_queue_end(&pt);
  	gel(K,nGW*d0+1) = mat2col(rho);
  	/* Find a random solution to the inhomogeneous system */
  	KM = matkerpadic(K,T,pe21,p,e21);
		KM = gerepileupto(avrho,KM);
		if(DEBUGLEVEL||(lg(KM)==1)) printf("dim ker lift: %ld\n",lg(KM)-1);
		if(cmpii(pe21,powiu(l,g+1))<=0)
  	{
			av2 = avma;
    	if(DEBUGLEVEL) printf("Lift by mul\n");
			U = PicLift_RandLift_U(U,U0,KM,T,p,pe1,pe21,e21);
			W = PicInflate_U(J2,U,NULL);
			W = gerepileupto(av2,W);
    	W = PicMul(J2,W,pe21,0); /* Make it l-tors */
			if(e2==efin) /* Already done ? */
				return gerepileupto(av,W);
			W = gerepileupto(av2,W);
			U = PicDeflate_U(J2,W,nGW); /* Update U -> ready for new iteration */
		}
		else
		{
			if(DEBUGLEVEL) printf("Lift by chart\n");
			Clifts = cgetg(g+2,t_MAT);
			Ulifts = cgetg(g+2,t_VEC);
			vFixedParams = cgetg(13,t_VEC);
			randseed = cgetg(2,t_VEC);
  		av2 = av3 = avma;
  		while(1)
  		{
				avma = av3;
    		if(c0==NULL) /* Compute coords of 0 if not already done */
    		{
      		/* Find coords of 0 */
					for(;;)
					{
						if(DEBUGLEVEL) printf("Computing coords of 0, P0=%lu\n",P0);
						c0 = PicChart(J,JgetW0(J),P0,NULL);
						if(c0) break;
						P0++;
						if(P0>nZ+g-d0)
							pari_err(e_MISC,"Run out of charts while computing coords of 0");
					}
					c0 = gerepileupto(av3,c0);
      		nc = lg(c0)-1;
      		/* Find indep set of rows to normalize */
					c0 = col2mat(c0,nc/nW,nW);
					P1 = FqM_indexrank(c0,T,p);
					P1 = gel(P1,1);
					c0 = Subspace_normalize(c0,P1,T,pefin,p,efin,1);
					c0 = mat2col(c0);
					gerepileall(av2,2,&c0,&P1);
					av3 = avma;
    		}
    		/* Find g+1 lifts in parallel */
				gel(vFixedParams,1) = J2;
      	gel(vFixedParams,2) = l;
      	gel(vFixedParams,3) = U;
      	gel(vFixedParams,4) = U0;
      	gel(vFixedParams,5) = sW;
      	gel(vFixedParams,6) = KM;
      	gel(vFixedParams,7) = pe1;
      	gel(vFixedParams,8) = pe21;
      	gel(vFixedParams,9) = stoi(e21);
      	gel(vFixedParams,10) = c0;
      	gel(vFixedParams,11) = utoi(P0);
      	gel(vFixedParams,12) = P1;
      	worker = snm_closure(is_entry("PicLiftTors_Chart_worker"),vFixedParams);
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
							printf("Lift %ld had a chart issue\n",workid);
							liftsOK = 0;
						}
						else
						{
        			gel(Ulifts,workid) = gel(done,1);
        			gel(Clifts,workid) = gel(done,2);
						}
      		}
    		}
    		mt_queue_end(&pt);
				if(liftsOK==0)
        { /* This chart does not work. Take the next one, reset data, and restart */
         	printf("Changing chart\n");
					P0++; /* New chart */
          printf("P0=%lu\n",P0);
          if(P0>nZ+g-d0)
            pari_err(e_MISC,"Run out of charts while computing coords of 0");
          P0_tested = 0;
          c0 = NULL; /* Coords of 0 must be recomputed */
          av3 = av2;
          continue; /* Try again with this new chart */
        }
				Ktors = matkerpadic(Clifts,T,pe21,p,e21); /* Find comb with coord = 0 */
    		n = lg(Ktors)-1;
    		if(n!=1)
    		{ /* l-tors is étale, so this can only happen if Chart is not diffeo - > change chart */
      		printf("Dim ker tors = %ld (expected 1), changing charts\n",n);
      		printf("nZ=%lu, g=%lu, d0=%lu\n",nZ,g,d0);
					P0++; /* New chart */
					printf("P0=%lu\n",P0);
					if(P0>nZ+g-d0)
            pari_err(e_MISC,"Run out of charts while computing coords of 0");
					P0_tested = 0;
					c0 = NULL; /* Coords of 0 must be recomputed */
					av3 = av2;
      		continue; /* Try again with this new chart */
    		}
    		Ktors = gel(Ktors,1);
    		red = gel(Ktors,1);
    		for(i=2;i<=g+1;i++)
    		{
      		red = ZX_add(red,gel(Ktors,i));
    		}
    		if(ZX_is0mod(red,p)) /* TODO can this happen ? why, or why not ? */
				{	printf("Sum of Ktors is zero!\n"); continue;}
    		Ktors = FqC_Fq_mul(Ktors,ZpXQ_inv(red,T,p,e2),T,pe2); /* Normalise so that sum = 1 */
				W = NULL; /* If done, return updated W; else update U. */
				for(i=1;i<=g+1;i++) gel(Ulifts,i) = FqM_Fq_mul(gel(Ulifts,i),gel(Ktors,i),T,pe2);
        U2 = gel(Ulifts,1);
        for(i=2;i<=g+1;i++) U2 = FpXM_add(U2,gel(Ulifts,i),pe2);
				U2 = gerepileupto(av3,U2);
				/* But first check if really l-tors, as the chart might not be injective ! */
    		if(P0_tested == 0)
				{
					if(DEBUGLEVEL) pari_printf("Checking %Ps-tors\n",l);
					W = PicInflate_U(J2,U2,NULL);
					avtesttors = avma;
					testtors = PicIsZero_val(J2,PicMul(J2,W,l,0));
					avma = avtesttors;
					if(testtors<e2)
          {
            printf("Not actually l-torsion!!! Changing charts\n");
            P0++;
            c0 = NULL;
						av3 = av2;
            continue;
          }
					P0_tested = 1;
    		}
				if(e2 == efin)
				{ /* Already done ? */
					if(W == NULL) /* Update W, if not already done, and return it */
						W = PicInflate_U(J2,U2,NULL);
					return gerepileupto(av,W);
				}
				else
				{	
					/* Update U -> ready for next iteration */
					U = U2;
					break;
				}
			}
		}
		/* END LIFTING */
    e1 = e2;
		pe1 = pe2;
		if(c0)
			gerepileall(av1,4,&U,&pe1,&c0,&P1);
		else
			gerepileall(av1,2,&U,&pe1);
  }
}

/* TorsSpace */

ulong c2i(GEN c, ulong l)
{ /* coords mod l -> integer */
	ulong i,d,n;
	d = lg(c)-1;
	i = 0;
	for(n=1;n<=d;n++)
	{
		i *= l;
		i += (c[n]%l);
	}
	return i?i:upowuu(l,d);
}

GEN i2c(ulong i, ulong l, ulong d)
{ /* integer -> coords mod l */
	GEN c;
	ulong n;
	c = cgetg(d+1,t_VECSMALL);
	for(n=1;n<=d;n++)
	{
		c[d+1-n] = i%l;
		i /= l;
	}
	return c;
}

ulong Chordi(ulong i1, ulong i2, ulong l, ulong d)
{ /* Negative of sum mod l, in terms of integers */
	pari_sp av = avma;
	GEN c1,c2,c3;
	ulong n;
	c1 = i2c(i1,l,d);
	c2 = i2c(i2,l,d);
	c3 = cgetg(d+1,t_VECSMALL);
	for(n=1;n<=d;n++)
		c3[n] = (2*l-(c1[n]+c2[n]))%l;
	n = c2i(c3,l);
	avma = av;
	return n;
}

ulong ActOni(GEN m, ulong i, ulong l)
{ /* Matrix action mod l, in terms of integers */
	pari_sp av = avma;
	GEN c;
	ulong d;
	d = lg(m)-1;
	c = i2c(i,l,d);
	c = Flm_Flc_mul(m,c,l);
	i = c2i(c,l);
	avma = av;
	return i;
}

GEN TorsSpaceFrob_worker(GEN W1, GEN X1, GEN W2, GEN X2, GEN J)
{
	pari_sp av = avma;
	GEN W;
	ulong x1,x2;
	x1 = itou(X1);
	if(W2==gen_0)
	{
		W = PicNeg(J,W1,0);
		W = PicFrobPow(J,W,x1);
		return gerepileupto(av,W);
	}
	x2 = itou(X2);
	W1 = PicFrobPow(J,W1,x1);
	W2 = PicFrobPow(J,W2,x2);
	W = PicChord(J,W1,W2,0);
  return gerepileupto(av,W);
}

GEN M2Flm(GEN A, ulong l, ulong m, ulong n)
{ /* Reduce m*n matrix A mod l -> vec of vecsmalls */
	GEN a;
	ulong j,k;
	a = cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    gel(a,j) = cgetg(m+1,t_VECSMALL);
    for(k=1;k<=m;k++)
      gel(a,j)[k] = itos(liftint(gcoeff(A,k,j)));
  }
	return a;
}

GEN TorsSpaceFrobEval(GEN J, GEN gens, GEN cgens, ulong l, GEN matFrob, GEN matAuts)
{
	pari_sp av = avma;
	ulong d,ld,ndone,ngens,nmodF,newmodF,new,ntodo,i,j,k,m,n,ij,ik,xj,xk,x,nAuts,a;
	GEN vJ,vW,VmodF,ImodF,ZmodF,ImodF2,done,mfrob,mauts,c,todo,W,Wj,Wk;
	struct pari_mt pt;
	GEN worker,res;
  long pending;

	d = lg(matFrob)-1; // Dim of rep
	ld = upowuu(l,d);
	VmodF = cgetg(ld+1,t_VEC); // list of W's mod Frob
	ImodF = cgetg(ld+1,t_VECSMALL); // list of indices of these W's
	done = cgetg(ld+1,t_VEC); // All space: each entry is either
	// NULL: we don't have this pt yet
	// gen_m1: we will get this pt by applying Auts and Frob
	// Vecmall([n,m]): this pt is Frob^m * VmodF[n]
	// Vecsmall([0,0]): this is the origin
	for(n=1;n<ld;n++) // Initalise
		gel(done,n) = NULL;
	gel(done,ld) = mkvecsmall2(0,0);
	ndone = 1; // Number of pts; we stop when this reaches ld
	nmodF = 0; // Number of pts mod Frob
	ngens = lg(gens)-1;
	// Prepare cloure for parallel code
	vJ = cgetg(2,t_VEC);
  gel(vJ,1) = J;
	worker = snm_closure(is_entry("TorsSpaceFrob_worker"),vJ);
	// matFrob and matAuts, version Flm
	mfrob = M2Flm(matFrob,l,d,d);
	nAuts = lg(matAuts);
	mauts = cgetg(nAuts,t_VEC);
	for(a=1;a<nAuts;a++) gel(mauts,a) = M2Flm(gel(matAuts,a),l,d,d);
	// Now we are ready to begin
	// We will always keep done closed under Frob
	
	// Throw in generators and their Frob orbits
	c = cgetg(d+1,t_VECSMALL);
	for(n=1;n<=ngens;n++)
	{
		nmodF++; // new Frob orbit
		gel(VmodF,nmodF) = gel(gens,n); // store W in VmodF
		for(i=1;i<=d;i++) // Convert coords into index
			c[i] = itou(gmael(cgens,n,i));
		ImodF[nmodF] = i = c2i(c,l);
		gel(done,i) = mkvecsmall2(nmodF,0); // store [nmodF,0] in done[i]
		ndone++; // got new pt
		for(x=1;;x++) // go through Frob orbit
		{
			i = ActOni(mfrob,i,l); // Move index by Frob
			if(gel(done,i)) break; // end of orbit?
			gel(done,i) = mkvecsmall2(nmodF,x); // Record [nmodF,x], meaning x-th translate of this Frob orbit, in done
			ndone++; // got new pt
		}
	}
	// Loop until everything is covered
	todo = cgetg(ld,t_VEC); // list of operations to be executed in parallel; used later
	while(ndone<ld)
	{
		printf("Main loop, touched %lu/%lu\n",ndone,ld);
		// Use Auts as much as possible
		do
		{
			newmodF = 0; // number of new Fob orbs we get at this iteration. If it's still 0 in the end, we are done with Auts.
			for(i=1;i<=nmodF;i++) // Try to apply to all pts mod Frob...
			{ // TODO only new orbits need to be checked
				j = ImodF[i];
				for(a=1;a<nAuts;a++) // ... all auts
				{
					k = ActOni(gel(mauts,a),j,l);
					W = gel(done,k);
					if(W==NULL || W==gen_m1) // does this yield a new pt, and therefore a new Frob orbit?
					{
						W = gel(VmodF,i); // this new pt, before Aut
						W = PicAut(J,W,a); // after Aut
						nmodF++; // new Frob orbit
						newmodF++; // new Frob orbit at this iteration
						gel(VmodF,nmodF) = W; // record representative of Frob orbit
						ImodF[nmodF] = k; // and its index
						gel(done,k) = mkvecsmall2(nmodF,0); // store [nmodF,0] in done
						ndone++; // new pt
						for(x=1;;x++) // go through Frob orb
						{
				      k = ActOni(mfrob,k,l); // Move index by Frob
							W = gel(done,k);
      				if(W && W!=gen_m1) break; // end of orbit?
      				gel(done,k) = mkvecsmall2(nmodF,x); // Record [nmodF,x], meaning x-th translate of this Frob orbit, in done
      				ndone++; // new pt
    				}
					}
				}
			}
			//printf("Applying auts gave %lu new Frob orbits\n",newmodF);
		} while(newmodF);
		if(nAuts>1) printf("Done with auts, now touched %lu/%lu\n",ndone,ld);
		if(ndone==ld) break; // Are we done?
		// TODO gerepile?
		// Now use group law
		// Prepare list of operations, we will run them in parallel later
		ntodo = 0;
		for(j=1;j<ld;j++)
		{
			for(k=j;k<=ld;k++)
			{
				if(gel(done,j)&&gel(done,k)&&gel(done,j)!=gen_m1&&gel(done,k)!=gen_m1) // Loop over pair of known pts
				{
					i = Chordi(j,k,l,d);
					if(gel(done,i)==NULL) // Do we already know their chord?
					{
						// Record the computation that needs to be done
						ij = gel(done,j)[1];
						xj = gel(done,j)[2];
						ik = gel(done,k)[1];
						xk = gel(done,k)[2];
						Wj = ij?gel(VmodF,ij):gen_0;
						Wk = ik?gel(VmodF,ik):gen_0;
						ntodo++;
						gel(todo,ntodo) = mkvec2(mkvecn(4,Wj,utoi(xj),Wk,utoi(xk)),utoi(i));
						// Mark that we are about to get this Frob orbit...
						while(gel(done,i)==NULL)
						{
							gel(done,i) = gen_m1;
							i = ActOni(mfrob,i,l);
						}
						// ...and all it translates by auts
						do
				    {
      				new = 0; // number of new pts we get at this iteration. If it's still 0 in the end, we are done with Auts.
      				for(m=1;m<=ld;m++) // Try to apply to all pts...
      				{
								if(gel(done,m)==NULL) continue; // ... that we already have or will have ...
        				for(a=1;a<nAuts;a++) // ... all auts
        				{
          				n = ActOni(gel(mauts,a),m,l);
          				while(gel(done,n)==NULL) // will this yield a new pt, and therefore a new Frob orbit?
          				{
										gel(done,n) = gen_m1;
										new++;
										n = ActOni(mfrob,n,l);
									}
								}
            	}
    				} while(new);
					}
				}
			}
		}
		// Execute operations in J in parallel
		printf("Computing %lu new points\n",ntodo);
		mt_queue_start_lim(&pt,worker,ntodo);
	  for(n=1;n<=ntodo||pending;n++)
  	{
			if(n<=ntodo) mt_queue_submit(&pt,itos(gmael(todo,n,2)),gmael(todo,n,1));
			else mt_queue_submit(&pt,0,NULL);
    	res = mt_queue_get(&pt,(long*)&i,&pending);
    	if(res)
			{
				nmodF++;
				// Record new Frob orbit
				gel(VmodF,nmodF) = res;
				ImodF[nmodF] = i;
				// Mark the orbit as known
				for(x=0;gel(done,i)==gen_m1;x++)
				{
					gel(done,i) = mkvecsmall2(nmodF,x);
					ndone++;
					i = ActOni(mfrob,i,l);
				}
			}
  	}
  	mt_queue_end(&pt);
	}

	printf("Evaluating %lu points\n",nmodF);
	vW = cgetg(2,t_VEC);
	ZmodF = cgetg(nmodF+1,t_VEC);
	worker = snm_closure(is_entry("RREval_worker"),vJ);
	mt_queue_start_lim(&pt,worker,nmodF);
	for(n=1;n<=nmodF||pending;n++)
	{
		if(n<=nmodF)
		{
			gel(vW,1) = gel(VmodF,n);
			mt_queue_submit(&pt,n,vW);
		}
		else mt_queue_submit(&pt,0,NULL);
		res = mt_queue_get(&pt,(long*)&i,&pending);
		if(res)
			gel(ZmodF,i) = res; // TODO gerepile
	}
	mt_queue_end(&pt);

	ImodF2 = cgetg(nmodF+1,t_VECSMALL);
	for(n=1;n<=nmodF;n++) ImodF2[n] = ImodF[n];
	res = mkvec2(ZmodF,ImodF2);
	return gerepilecopy(av,res); // TODO do not copy
}

GEN PolExpID(GEN Z, GEN T, GEN pe) /* bestappr of prod(x-z), z in Z */
{
  pari_sp av;
  GEN res,f;
	res = cgetg(4,t_VEC);
	av = avma;
  f = FqV_roots_to_pol(Z,T,pe,0);
  if(poldegree(f,varn(T))>0) pari_err(e_MISC,"Irrational coefficient: %Ps",f);
  f = simplify_shallow(f);
  f = gmodulo(f,pe);
	f = gerepileupto(av,f);
	gel(res,2) = f;
	gel(res,3) = bestappr(f,NULL);
	gel(res,1) = gmodulo(gmodulo(Z,T),pe);
	return res;
}

GEN OnePol(GEN N, GEN D, GEN ImodF, GEN Jfrobmat, ulong l, GEN QqFrobMat, GEN T, GEN pe)
{ /* Actually returns a vector of n1*n2 pols (all elem. symm. fns) */
  pari_sp av = avma, av1;
  GEN R,Z,F,Fi,z;
  ulong d,ld,j,k,n,i1,i2,i;
  long n1,n2,n12;
  n = lg(N);
  RgM_dimensions(gel(N,1),&n2,&n1);
  /* N, D vectors of length n-1 of n2*n1 matrices
   * N[i]/D[i] = value at pt indexed by ImodF[i]
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
        gel(Z,i) = Fq_mul(gmael3(N,k,i1,i2),gmael3(D,k,i1,i2),T,pe);
        i++;
      }
    }
    gel(R,k) = FqV_roots_to_pol(Z,T,pe,0);
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
        z = Frob(z,QqFrobMat,T,pe);
      }
    }
    Fi = PolExpID(Z,T,pe);
    if(n12>1) Fi = gerepileupto(av1,Fi);
    gel(F,i+1) = Fi;
  }
  return gerepileupto(av,F);
}

GEN AllPols(GEN Z, ulong l, GEN JFrobMat, GEN QqFrobMat, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma, avj;
  GEN F,ImodF,Jfrobmat,Ft,F1,f,pols,args;
  ulong d,nF,lF,npols,n,i,j,j0,i1,i2,m,k;
	int All0;
  long n1,n2,n12;
  struct pari_mt pt;
  GEN worker,done;
  long pending,workid;

	F = gel(Z,1);
	ImodF = gel(Z,2);
	d = lg(JFrobMat)-1;
  Jfrobmat = cgetg(d+1,t_MAT); /* JFrobMat, version Flm */
  for(j=1;j<=d;j++)
  {
    gel(Jfrobmat,j) = cgetg(d+1,t_VECSMALL);
    for(k=1;k<=d;k++)
      gel(Jfrobmat,j)[k] = itos(liftint(gcoeff(JFrobMat,k,j)));
  }
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
		if(All0) avma = avj; /* Drop this j */
    else j0++;
  }
	printf("Reducing lF from %lu to %lu\n",lF-1,j0-1);
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
          if(ZX_is0mod(f,p))
          {
            gel(F1,i) = NULL;
            npols--;
            i2=n2+1;i1=n1+1;j=nF;
          }
          else
            gmael4(F1,i,j,i1,i2) = ZpXQ_inv(f,T,p,e); /* TODO do it later in case we give up this i */
        }
      }
    }
  }
  pending = 0;
  worker = strtofunction("OnePol");
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
        gel(pols,m) = gel(done,k);
        m++;
      }
    }
  }
  mt_queue_end(&pt);
  return gerepileupto(av,pols);
}

/* Frey-Rueck pairing over Fq */

GEN FindSuppl(GEN W, ulong nS, GEN V, GEN Vbis, GEN T, GEN p, GEN pe)
/* /!\ Shallow */
/* Look for suppl of W of dim nS in V*Vbis, or in V if Vbis=NULL */
{
	pari_sp av1,av = avma;
	GEN S,v1,v2,col;
	ulong i,j,nW,nZ;
	nW = lg(W)-1;
	nZ = lg(gel(V,1))-1;
	S = cgetg(nS+nW+1,t_MAT);
	av1 = avma;
	do
	{
		avma = av1;
		if(Vbis)
		{
			for(j=1;j<=nS;j++)
			{
				col = cgetg(nZ+1,t_COL);
				v1 = RandVec_1(V,pe);
				v2 = RandVec_1(Vbis,pe);
				for(i=1;i<=nZ;i++) gel(col,i) = Fq_mul(gel(v1,i),gel(v2,i),T,pe);
				gel(S,j) = col;
			}
		}
		else
		{
			for(j=1;j<=nS;j++) gel(S,j) = RandVec_1(V,pe);
		}
		for(j=1;j<=nW;j++) gel(S,j+nS) = gel(W,j);
	}while(FqM_rank(S,T,p)<nS+nW);
	if(Vbis) S = gerepilecopy(av,S);
	return S;
}

GEN detratio(GEN K, GEN T, GEN p, long e, GEN pe)
{ /* K=(K1|K2) -> det(K2)/det(K1) */
	pari_sp av = avma;
	GEN K1,K2,col1,col2;
	ulong d0,i,j;
	d0 = lg(K)-1;
	K1 = cgetg(d0+1,t_MAT);
	K2 = cgetg(d0+1,t_MAT);
	for(j=1;j<=d0;j++)
	{
		col1 = cgetg(d0+1,t_COL);
		col2 = cgetg(d0+1,t_COL);
		for(i=1;i<=d0;i++)
		{
			gel(col1,i) = gcoeff(K,i,j);
			gel(col2,i) = gcoeff(K,d0+i,j);
		}
		gel(K1,j) = col1;
		gel(K2,j) = col2;
	}
	if(e==1)
		return gerepileupto(av,Fq_div(FqM_det(K2,T,p),FqM_det(K1,T,p),T,p));
	/* TODO? */
	pari_err(e_IMPL,"case e>1");
	/* return gerepileupto(av,Fq_mul(ZpXQM_det(K2,T,p,e),ZpXQ_inv(ZpXQM_det(K1,T,p,e),T,p,e),T,pe));*/
	return NULL;
}

GEN PicNorm(GEN J, GEN F1, GEN F2, GEN WE, ulong n)
{ /* F1,F2 in V_n, WE = V(-E) -> F1/F2(E) */
	pari_sp av = avma;
	ulong g,d0,nS,nZ,nVn2;
	ulong i,j;
	long e;
	GEN V,Vn,T,p,pe;
	GEN WEVn,S,SS,M1,M2,M;

	g = Jgetg(J);
	d0 = Jgetd0(J);
	V = JgetV(J,2);
	JgetTpe(J,&T,&pe,&p,&e);
	d0 = Jgetd0(J);
	g = Jgetg(J);
	nVn2 = (n+2)*d0+1-g; /* dim V_{n+2} = L((n+2)*D0) */
	nS = lg(V)-lg(WE); /* codim WE in V = deg E */
	nZ = lg(gel(V,1))-1;
	Vn = JgetV(J,n);

	WEVn = DivAdd(Vn,WE,nVn2-nS,T,p,e,pe,0); /* Vn*WE = V_{n+2}(-E) */
	S = FindSuppl(WE,nS,V,NULL,T,p,pe); /* V = V(-E) + S, dim S = nS */
	SS = FindSuppl(WEVn,nS,V,Vn,T,p,pe); /* V_{n+2} = V_{n+2}(-E) + S, dim SS = nS */

	M = cgetg(nS+nVn2+1,t_MAT);
	for(j=1;j<=nS;j++)
	{
		gel(M,j) = cgetg(nZ+1,t_COL);
		for(i=1;i<=nZ;i++)
			gcoeff(M,i,j) = Fq_mul(gcoeff(S,i,j),gel(F1,i),T,pe);
	}
	for(j=1;j<=nVn2;j++) gel(M,nS+j) = gel(SS,j);
	M1 = detratio(matkerpadic(M,T,pe,p,e),T,p,e,pe);
	if(ZX_is0mod(M1,p))
	{
		if(DEBUGLEVEL) err_printf("PicNorm: F1 has zeros on D, giving up\n");
		avma = av;
		return NULL;
	}

	for(j=1;j<=nS;j++)
	{
		for(i=1;i<=nZ;i++)
			gcoeff(M,i,j) = Fq_mul(gcoeff(S,i,j),gel(F2,i),T,pe);
	}
	M2 = detratio(matkerpadic(M,T,pe,p,e),T,p,e,pe);
	if(ZX_is0mod(M2,p))
	{
		if(DEBUGLEVEL) err_printf("PicNorm: F2 has zeros on D, giving up\n");
		avma = av;
		return NULL;
	}
	
	return gerepileupto(av,ZpXQ_div(M1,M2,T,pe,p,e)); /* TODO can save divisions by taking detratios together */
}

GEN PicFreyRuckMulti1(GEN J, GEN Wtors, GEN l, GEN Wtest, GEN W0, GEN F1, GEN F2, GEN F3, GEN C)
/* Pair the l-tors pt Wtors against the pts in Wtest */
{
	pari_sp av = avma;
	GEN WtorsM,Fq1,H,col,WA,WB,res,s,N;
	GEN T,p,pe,V1,KV1;
	long e;
	ulong nC,ntest;
	ulong c,d,i,j;
	ulong n=0;
	GEN Fn=NULL;
	
	JgetTpe(J,&T,&pe,&p,&e);
	Fq1 = pol_1(varn(T));
	V1 = JgetV(J,1);
	KV1 = JgetKV(J,1);
	nC = lg(C);
	ntest = lg(Wtest);
	WtorsM = cgetg(nC,t_VEC);
	gel(WtorsM,1) = Wtors;
	H = zeromatcopy(ntest-1,nC-1);
	gel(H,1) = cgetg(ntest,t_COL);
	for(d=1;d<ntest;d++) gcoeff(H,d,1) = Fq1;
	for(c=2;c<nC;c++)
	{
		i = gmael(C,c,2)[1];
		j = gmael(C,c,2)[2];
		if(i)
		{
			WA = gel(WtorsM,i);
			if(j)
			{
				WB = gel(WtorsM,j);
				res = PicChord(J,WA,WB,3);
				n = 3;
				Fn = F3;
			}
			else
			{
				res = PicNeg(J,WA,3);
				n = 2;
				Fn = F2;
			}
		}
		else
		{
			if(j==0) pari_err(e_MISC,"Two zeros in Frey-Ruck AddFlip chain, not supposed to happen!");
			WB = gel(WtorsM,j);
			res = PicNeg(J,WB,3);
			n = 2;
			Fn = F2;
		}
		gel(WtorsM,c) = gel(res,1);
		s = gel(res,2); /* in Vn, n=2 or 3 as above */
		col = cgetg(ntest,t_COL);
		for(d=1;d<ntest;d++)
		{
			N = PicNorm(J,s,Fn,gel(Wtest,d),n);
			if(N==NULL)
			{
				av = avma;
				return NULL;
			}
			gel(col,d) = Fq_mul(N,gcoeff(H,d,i),T,pe);
			if(j) gel(col,d) = Fq_mul(gel(col,d),gcoeff(H,d,j),T,pe);
			gel(col,d) = ZpXQ_inv(gel(col,d),T,p,e);
		}
		N = PicNorm(J,s,Fn,W0,n);
		if(N==NULL)
    {
      av = avma;
      return NULL;
    }
		gel(H,c) = FqC_Fq_mul(col,N,T,pe);
	}
	/* WtorsM[nC-1] ~ 0, find section that makes this lin equiv happen */
	s = DivSub(V1,gel(WtorsM,nC-1),KV1,1,T,p,e,pe,2);
	s = gel(s,1);
	col = gel(H,nC-1);
	for(d=1;d<ntest;d++)
	{
		N = PicNorm(J,s,F1,gel(Wtest,d),1);
		if(N==NULL)
    {
      av = avma;
      return NULL;
    }
		gel(col,d) = Fq_mul(gel(col,d),N,T,pe);
	}
	N = PicNorm(J,s,F1,W0,1);
	if(N==NULL)
  {
    av = avma;
    return NULL;
  }
	col = FqC_Fq_mul(col,ZpXQ_inv(N,T,p,e),T,pe);
	return gerepileupto(av,col);
}

GEN PicFreyRuckMulti(GEN J, GEN Wtors, GEN l, GEN Wtest, GEN W0, GEN C)
/* Pair the l-tors pt Wtors against the pts in Wtest */
{
	pari_sp av = avma,av1;
	GEN res=NULL,Wtors1=Wtors,Wtest1,W01=W0,V1,T,pe,F1,F2,F3;
	ulong ntest,i,nZ;
	ntest = lg(Wtest);
	T = JgetT(J);
	pe = Jgetpe(J);
	V1 = JgetV(J,1);
	Wtest1 = cgetg(ntest,t_VEC);
	F1 = gel(V1,1);
	nZ = lg(F1);
	F2 = cgetg(nZ,t_COL);
	F3 = cgetg(nZ,t_COL);
	av1 = avma;
	for(i=1;i<ntest;i++)
		gel(Wtest1,i) = gel(Wtest,i);
	for(i=1;i<nZ;i++)
	{
		gel(F2,i) = Fq_mul(gel(F1,i),gel(F1,i),T,pe);
		gel(F3,i) = Fq_mul(gel(F2,i),gel(F1,i),T,pe);
	}

	for(;;)
	{
		res = PicFreyRuckMulti1(J,Wtors1,l,Wtest1,W01,F1,F2,F3,C);
		if(res) return gerepileupto(av,res);
		if(DEBUGLEVEL) err_printf("Error in Frey-Ruck, retrying\n");
		avma = av1;
		Wtors1 = PicNeg(J,Wtors,1);
		W01 = PicNeg(J,W0,1);
		for(i=1;i<ntest;i++)
			gel(Wtest1,i) = PicNeg(J,gel(Wtest,i),1);
		F1 = RandVec_1(V1,pe);
		for(i=1;i<nZ;i++)
  	{
    	gel(F2,i) = Fq_mul(gel(F1,i),gel(F1,i),T,pe);
    	gel(F3,i) = Fq_mul(gel(F2,i),gel(F1,i),T,pe);
  	}
	}
}

GEN Fq_zeta_l(GEN T, GEN p, GEN l)
{ /* Random primitive l-th root of 1 in Fq */
	pari_sp av = avma;
	GEN q,q1,m,z;
	q = powiu(p,degree(T));
  q1 = subii(q,gen_1);
  if(!gequal0(modii(q1,l))) pari_err(e_MISC,"No l-th roots of 1");
  m = divii(q1,l);
  z = gener_FpXQ(T,p,NULL);
  z = Fq_pow(z,m,T,p);
	return gerepileupto(av,z);
}

GEN Fq_mu_l_log(GEN x, GEN z, GEN T, GEN p, GEN l)
{ /* (Very basic) discrete log in mu_l(Fq) */
	pari_sp av = avma;
	ulong n = 0;
	GEN q,q1,m,zn,y;
  q = powiu(p,degree(T));
  q1 = subii(q,gen_1);
  m = divii(q1,l);
	y = Fq_pow(x,m,T,p);
  zn = gen_1;
  while(!gequal(y,zn))
  {
    zn = Fq_mul(zn,z,T,p);
    n++;
  }
  return gerepileupto(av,utoi(n));
}

