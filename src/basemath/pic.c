#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_pic
#define lgJ 17

void timers_printf(const char* msg1, const char* msg2, pari_timer* pCPU, pari_timer* pW)
{ printf("%s: Time %s: CPU %s, real %s\n",msg1,msg2,gp_format_time(timer_delay(pCPU)),gp_format_time(walltimer_delay(pW))); }

/* Linear algebra */

long ZX_is0mod(GEN x, GEN p)
{
  pari_sp av = avma;
  GEN red;
  long res;
  red = (typ(x)==t_POL?FpX_red(x,p):Fp_red(x,p));
  res = gequal0(red);
	/* signe(red) */
  avma = av;
  return res;
	/* return gc_bool(av,...); */
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
{ /* shallowconcat1? */
  ulong n,m,i,j=1;
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

GEN col2mat(GEN C, ulong m, ulong n)
{
  GEN A,Aj;
  ulong i=1,j=1;
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
10: Lp, charpoly of Frob_p on J; 0 if unkown
11: V = [V1,V2,V3,M,I] where Vn = H0(n*B) (Having a nice basis of V2 improves the evaluation map), vecsmall I of row indices, and matrix M translation the I-rows into coords on basis of V2
12: KV = [KV1,KV2,KV3], where KVn = equation matrix for Vn
13: W0 = f*V1 for some f in V1, subspace of V2 representing the origin
14: EvalData [U1,U2,MU]: pair of subspaces Ui of the form V2(-E) with E effective of degree d0-g, used for construction of eval map, then matrix MU such that v in V should be taken to M*(v_I) for evaluation, where I is as in 11; if MU==gen_0, use M from 11 instead.
15: If B=O_X(D0), vector Z of points at which the sections are evaluated; else []
16: FrobCyc, permutation describing the action of Frob on Z
17: Auts, vector of pairs [P,n], P permutation describing the action of Aut on Z, n nonzero if this Auts acts a [n] on J, n=0 else

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
GEN JgetE(GEN J) {return gel(J,7);}
GEN Jgetpe(GEN J) {return gel(J,8);}
GEN JgetFrobMat(GEN J) {return gel(J,9);}
GEN JgetLp(GEN J) {return gel(J,10);}
GEN JgetV(GEN J, ulong n) {return gmael(J,11,n);}
GEN JgetV_all(GEN J) {return gel(J,11);}
GEN JgetKV(GEN J, ulong n) {return gmael(J,12,n);}
GEN JgetKV_all(GEN J) {return gel(J,12);}
GEN JgetW0(GEN J) {return gel(J,13);}
GEN JgetEvalData(GEN J) {return gel(J,14);}
GEN JgetZ(GEN J) {return gel(J,15);}
GEN JgetFrobCyc(GEN J) {return gel(J,16);}
GEN JgetAutData(GEN J) {return gel(J,17);}
GEN JgetAutCyc(GEN J, ulong n)
{
	GEN A = gel(J,17);
	if(n>=lg(A))
		pari_err(e_MISC,"This automorphism is not present");
	return gmael(A,n,1);
}
GEN JgetAutKnown(GEN J, ulong n) {return gmael3(J,17,n,2);}

void JgetTpe(GEN J, GEN* T, GEN* pe, GEN* p, long* e)
{
  *T = gel(J,5);
  *p = gel(J,6);
  *e = itos(gel(J,7));
  *pe = gel(J,8);
}

GEN JacRed(GEN J, ulong e)
{
  pari_sp av = avma;
  GEN Je,p,pe,Ui,Uei,MU;
  ulong i,j,n;
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
	gel(Je,10) = gcopy(gel(J,10));
  gel(Je,11) = cgetg(6,t_VEC);
  for(i=1;i<=4;i++) gmael(Je,11,i) = FpXM_red(gmael(J,11,i),pe);
	gmael(Je,11,5) = gcopy(gmael(J,11,5));
  gel(Je,12) = cgetg(4,t_VEC);
  for(i=1;i<=3;i++) gmael(Je,12,i) = FpXM_red(gmael(J,12,i),pe);
  gel(Je,13) = FpXM_red(JgetW0(J),pe);
	if(gequal0(gel(J,14)))
	{
		gel(Je,14) = gen_0;
	}
	else
	{
  	gel(Je,14) = cgetg(4,t_VEC);
		for(i=1;i<=2;i++)
		{
			Ui = gmael(J,14,i);
			n = lg(Ui);
			gmael(Je,14,i) = Uei = cgetg(n,t_VEC);
			for(j=1;j<n;j++)
				gel(Uei,j) = FpXM_red(gel(Ui,j),pe);
		}
		MU = gmael(J,14,3);
		gmael(Je,14,3) = typ(MU)==t_INT ? gen_0 : FpXM_red(MU,pe);
	}
  gel(Je,15) = FpXT_red(JgetZ(J),pe);
  gel(Je,16) = gcopy(JgetFrobCyc(J));
  gel(Je,17) = gcopy(JgetAutData(J));
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

GEN DivAdd(GEN WA, GEN WB, ulong d, GEN T, GEN p, GEN pe, ulong excess)
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
    if(DEBUGLEVEL>=4) err_printf("divadd(%lu/%lu)",r,d);
    excess++;
    avma = av;
  }
}

GEN DivAdd1(GEN WA, GEN WB, ulong d, GEN T, GEN pe, GEN p, ulong excess, long flag)
{ /* Mult RR spaces WA and WB.
		 Takes d+excess products WA[u]*WB[v] for random u,v.
		 If flag is set, also returns the list of [u,v]. */
	pari_sp av = avma, av1;
	GEN res,WAB,uv,s,t,st,J;
	ulong nA,nB,nZ,j,P,u,v,r;
	nA = lg(WA)-1;
	nB = lg(WB)-1;
	nZ = lg(gel(WA,1));
  res = cgetg(3,t_VEC);
	av1 = avma;
	while(1)
  {
  	gel(res,1) = WAB = cgetg(d+excess+1,t_MAT);
	  gel(res,2) = uv = cgetg(d+excess+1,t_VEC);
    for(j=1;j<=d+excess;j++)
    {
			gel(uv,j) = cgetg(3,t_VECSMALL);
			gel(uv,j)[1] = u = random_Fl(nA)+1;
			s = gel(WA,u);
			gel(uv,j)[2] = v = random_Fl(nB)+1;
			t = gel(WB,v);
			gel(WAB,j) = st = cgetg(nZ,t_VEC);
      for(P=1;P<nZ;P++)
        gel(st,P) = Fq_mul(gel(s,P),gel(t,P),T,pe);
    }
		J = gel(FqM_indexrank(WAB,T,p),2);
    r = lg(J)-1;
    if(r==d)
		{
			setlg(WAB,r+1);
			setlg(uv,r+1);
			for(j=1;j<=d;j++)
			{
				gel(WAB,j) = gel(WAB,J[j]);
				gel(uv,j) = gel(uv,J[j]);
			}
			setlg(WAB,r+1);
			setlg(uv,r+1);
      return gerepilecopy(av,flag?res:WAB);
		}
    if(DEBUGLEVEL>=4) err_printf("divadd1(%lu/%lu)",r,d);
    excess++;
    avma = av1;
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
    if(DEBUGLEVEL>=4) err_printf("divsub(%lu/%lu)",r,d);
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

int PicMember(GEN J, GEN W)
{
	long e;
	ulong v;
	e = Jgete(J);
	v = PicMember_val(J,W);
	if(v==e) return 1;
	return 0;
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

int PicEq(GEN J, GEN WA, GEN WB)
{
  long e;
  ulong v;
  e = Jgete(J);
  v = PicEq_val(J,WA,WB);
  if(v==e) return 1;
  return 0;
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

int PicIsZero(GEN J, GEN W)
{
	long e;
	ulong v;
	e = Jgete(J);
	v = PicIsZero_val(J,W);
	if(v==e) return 1;
	return 0;
}

ulong PicIsTors_val(GEN J, GEN W, GEN F)
{
	return PicIsZero_val(J,PicFrobPoly(J,W,F));
}

int PicIsTors(GEN J, GEN W, GEN F)
{
  return PicIsZero(J,PicFrobPoly(J,W,F));
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
  WAWB = DivAdd(WA,WB,2*d0+1-g,T,p,pe,0);
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
  if(DEBUGLEVEL>=2)
  {
    if(flag&2)
      pari_printf("PicMul : Mul by %Ps in %lu steps\n",n,nC-2);
    else
      pari_printf("PicMul : Mul by ±%Ps in %lu steps\n",n,nC-2);
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

GEN PicTorsOrd(GEN J, GEN W, GEN l, long flag)
{
/*Given that W is an l-power torsion point of J,
finds v s.t. the order of W is l^v,
and returns [+-l^(v-1)W, v]*/
	// TODO deal with sign in a better way
  pari_sp av = avma;
  GEN lW;
  ulong e,v;

  e = Jgete(J);
  lW = W;
  for(v=0;PicIsZero_val(J,lW)<e;v++)
  {
    W = lW;
    lW = PicMul(J,W,l,flag);
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

	if(gequal0(F))
		return gcopy(JgetW0(J));
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

  Cyc = JgetAutCyc(J,nAut);
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
      if(DEBUGLEVEL>=5) printf("FnsEvalAt_Rescale: Good, no relation\n");
      return gerepileupto(av,S);
    }
    if(DEBUGLEVEL>=5) pari_printf("FnsEvalAt_Rescale: Found %ld relations, eliminating and re-evaluating\n",nK-1);
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

GEN RRspaceEval(GEN L, GEN vars, GEN pts, GEN T, GEN pe, GEN p, long e)
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
		res = cgetg(2,t_VEC);
		gel(res,1) = FnsEvalAt_Rescale(L,pts,vars,T,p,e,pe);
    return res;
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
          if(i) P = CurveApplyAut(gmael(Auts,i,1),P,vars,T,pe,p,e);
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

GEN PicInit(GEN f, GEN Auts, ulong g, ulong d0, GEN L, GEN bad, GEN p, ulong a, long e, GEN Lp)
{
  pari_sp av = avma;
  long t;
  ulong nZ,nV2,nAuts,n,nOP,m,i,j;
  GEN vars,pe,T,FrobMat,Z,P,FrobCyc,AutData,OP,V1,V2,W0,V,M,I,KV,U,params,L12,J;
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

  if(DEBUGLEVEL>=2) printf("PicInit: Finding points\n");
  n = 0; /* current #pts */
  Z = cgetg(1,t_VEC); /* list of pts */
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
  /* Loop until we have enough pts */
  while(n<nZ)
  {
    /* Get new point */
    P = CurveRandPt(f,T,p,e,bad);
    /* Is it new mod p ? */
    if(FindMod(P,Z,n,p,0)) continue;
    if(DEBUGLEVEL>=3) printf("PicInit: Got new pt\n");
    /* Compute closure under Frob and Auts */
    OP = CurveAutFrobClosure(P,Auts,vars,FrobMat,T,pe,p,e);
    nOP = lg(gel(OP,1))-1; /* # new pts */
    if(DEBUGLEVEL>=3) printf("PicInit: Got closure of size %lu\n",nOP);
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
      gmael(AutData,i,1) = gconcat(gmael(AutData,i,1),gmael(OP,3,i));
    /* Update # pts */
    n += nOP;
  }

  if(DEBUGLEVEL>=2) printf("PicInit: Evaluating rational functions\n");
	V = cgetg(6,t_VEC);
  gel(V,1) = V1 = FnsEvalAt_Rescale(gel(L,1),Z,vars,T,p,e,pe);
  gel(V,2) = V2 = FnsEvalAt_Rescale(gel(L,2),Z,vars,T,p,e,pe);
  gel(V,3) = DivAdd(V1,V2,3*d0+1-g,T,p,pe,0);
	gel(V,5) = I = gel(FqM_indexrank(V2,T,p),1); /* Rows of V2 forming invertible block */
  /* That invertible block */
	nV2 = ((d0+1)<<1)-g;
  M = cgetg(nV2,t_MAT);
  for(j=1;j<nV2;j++)
  {
    gel(M,j) = cgetg(nV2,t_COL);
    for(i=1;i<nV2;i++)
      gcoeff(M,i,j) = gcoeff(V2,I[i],j);
  }
  gel(V,4) = ZpXQMinv(M,T,pe,p,e);
  W0 = V1;
	if(DEBUGLEVEL>=2) printf("PicInit: Computing equation matrices\n");
  KV = cgetg(4,t_VEC);
  E = stoi(e);
  worker = strtofunction("_mateqnpadic");
  mt_queue_start_lim(&pt,worker,3);
  for(k=1;k<=3||pending;k++)
  {
    mt_queue_submit(&pt,k,k<=3?mkvecn(5,gel(V,k),T,pe,p,E):NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done) gel(KV,workid) = done;
  }
  mt_queue_end(&pt);
	if(DEBUGLEVEL>=2) printf("PicInit: Constructing evaluation maps\n");
	L12 = gel(L,3);
	if(gequal0(L12)) U = gen_0;
	else
	{
  	params = cgetg(8,t_VEC);
  	gel(params,2) = vars;
  	gel(params,3) = Z;
  	gel(params,4) = T;
  	gel(params,5) = pe;
  	gel(params,6) = p;
  	gel(params,7) = E;
  	U = cgetg(4,t_VEC);
  	worker = strtofunction("_RRspace_eval");
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
    	if(done) gel(U,workid) = done;
		}
  	mt_queue_end(&pt);
		gel(U,3) = gen_0;
  }
	if(Lp==NULL) Lp = gen_0;
  J = mkvecn(lgJ,f,stoi(g),stoi(d0),L,T,p,E,pe,FrobMat,Lp,V,KV,W0,U,Z,FrobCyc,AutData);
  return gerepilecopy(av,J);
}

GEN JacLift(GEN J, ulong e2)
{
  pari_sp av = avma, avZ;
  GEN J2,T,p,pe2,f,vars,L,FrobCyc,FrobMat2;
  long g,d0;
  GEN Z,Z2,V,W0,KV,P,x,y,fx,U,V2,I,M,params;
  ulong nZ,i,j,nV2;
  struct pari_mt pt;
  GEN worker,done,E2;
  long pending,k,workid;
  if(Jgete(J)>=e2)
  {
    pari_warn(warner,"Current accuracy already higher than required in JacLift, not changing anything");
    return gcopy(J);
  }
  f = Jgetf(J);
  if(gequal0(f))
    pari_err(e_MISC,"Cannot increase accuracy for this Jacobian (missing equation)");
  L = JgetL(J);
  if(lg(L)!=4)
    pari_err(e_MISC,"Cannot increase accuracy for this Jacobian (missing RR spaces)");
  Z = JgetZ(J);
  if(lg(Z)==1)
    pari_err(e_MISC,"Cannot increase accuracy for this Jacobian (missing points)");
	if(typ(gel(J,14))==t_VEC && typ(gmael(J,14,3))!=t_INT)
    pari_err(e_MISC,"Cannot increase accuracy for this Jacobian (missing information about evaluation map)");
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
	gel(J2,10) = gel(J,10); /* Lp */

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
  V = cgetg(6,t_VEC);
  KV = cgetg(4,t_VEC);
	params = cgetg(8,t_VEC);
	gel(params,2) = vars;
	gel(params,3) = Z2;
	gel(params,4) = T;
	gel(params,5) = pe2;
	gel(params,6) = p;
	gel(params,7) = E2;
  worker = strtofunction("_RRspace_eval");
  if(gequal0(gel(L,3)))
	{
		U = gen_0;
		mt_queue_start_lim(&pt,worker,2);
    for(k=1;k<=2||pending;k++)
    {
      if(k<=2)
      {
        gel(params,1) = gel(L,k);
        mt_queue_submit(&pt,k,params);
      }
      else mt_queue_submit(&pt,0,NULL);
      done = mt_queue_get(&pt,&workid,&pending);
      if(done)
				gel(V,workid) = gel(done,1);
    }
  	mt_queue_end(&pt);
	}
	else
	{
  	U = cgetg(4,t_VEC);
		mt_queue_start_lim(&pt,worker,4);
  	for(k=1;k<=4||pending;k++)
  	{
			if(k<=4)
			{
				gel(params,1) = k<=2 ? gmael(L,3,k) : gel(L,k-2);
				mt_queue_submit(&pt,k,params);
			}
			else mt_queue_submit(&pt,0,NULL);
    	done = mt_queue_get(&pt,&workid,&pending);
    	if(done)
    	{
      	if(workid<=2) gel(U,workid) = done;
      	else gel(V,workid-2) = gel(done,1);
    	}
  	}
 		mt_queue_end(&pt);
		gel(U,3) = gen_0;
	}
	I = gel(V,5) = gmael(J,11,5);
  nV2 = lg(V2=gel(V,2));
  M = cgetg(nV2,t_MAT);
  for(j=1;j<nV2;j++)
  {
    gel(M,j) = cgetg(nV2,t_COL);
    for(i=1;i<nV2;i++)
      gcoeff(M,i,j) = gcoeff(V2,I[i],j);
  }
  gel(V,4) = ZpXQMinv(M,T,pe2,p,e2);
	gel(V,3) = DivAdd(gel(V,1),gel(V,2),3*d0+1-g,T,p,pe2,0);
  W0 = gel(V,1); /* TODO can it happen that W0 != V1 even though all data is present? */
	setlg(params,6);
	gel(params,2) = T;
	gel(params,3) = pe2;
	gel(params,4) = p;
	gel(params,5) = E2;
  worker = strtofunction("_mateqnpadic");
  mt_queue_start_lim(&pt,worker,3);
  for(k=1;k<=3||pending;k++)
  {
		if(k<=3)
		{
			gel(params,1) = gel(V,k);
			mt_queue_submit(&pt,k,params);
		}
		else mt_queue_submit(&pt,0,NULL);
    done = mt_queue_get(&pt,&workid,&pending);
    if(done) gel(KV,workid) = done;
  }
  mt_queue_end(&pt);
  gel(J2,11) = V;
  gel(J2,12) = KV;
  gel(J2,13) = W0;
  gel(J2,14) = U;
  gel(J2,15) = Z2;
  gel(J2,16) = JgetFrobCyc(J);
  gel(J2,17) = JgetAutData(J);
  return gerepilecopy(av,J2);
}

GEN PicSetPrec(GEN J, long e2)
{
	long e = Jgete(J);
	if(e==e2)
		return gcopy(J);
	if(e2<e)
		return JacRed(J,e2);
	return JacLift(J,e2);
}

GEN PicEval(GEN J, GEN W)
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
    S1 = DivAdd(W,gel(U1,i1),2*d0+1,T,p,pe,0); /* L(4D0-D-E1) */
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
      S2 = DivAdd(S1,gel(U2,i2),2*d0+1,T,p,pe,0); /* L(4D0-E1-E2-ED) */
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
	GEN T,pe,p;
	long e;
	GEN GW,K,U,X,I,M;
	ulong i,j,m;

	JgetTpe(J,&T,&pe,&p,&e);
	GW = PicDeflate(J,W,nIGS); /* IGS of W */
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
	U = FqM_mul(M,K,T,pe);
	return gerepileupto(av,U);
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

GEN PicLiftTors(GEN J, GEN W, GEN l, long eini)
{
  pari_sp av=avma,av1,av2,av3,avrho,avtesttors;
	GEN T,p,V;
  long efin,e1,e2,e21,efin2,mask;
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

	if(eini==0)
	{
		eini = PicMember_val(J,W);
		J1 = JacRed(J,eini);
		eini = PicIsTors_val(J1,W,l);
		avma = av;
	}
	JgetTpe(J,&T,&pefin,&p,&efin);
	if(eini >= efin) return gcopy(W);
	
	mask = quadratic_prec_mask(efin); /* Best scheme to reach prec efin */
  e1 = e2 = 1;
  for(;;) /* Determine where to start */
  {
    e2<<=1;
    if(mask&1) e2--;
    mask>>=1;
    if(e2>eini) break;
    e1 = e2;
  }
	e1 = eini;

	g = Jgetg(J);
  d0 = Jgetd0(J);
  V = JgetV(J,2);
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

	av1 = avma; /* Use to collect garbage at each iteration */
	J1 = JacRed(J,e1);
	U = PicDeflate_U(J1,W,nGW); /* IGS of W1 // basis of V */
	U = gerepileupto(av1,U);
	pe1 = e1==1? p : powiu(p,e1);

	r = 3*d0+1-g; /* Wanted rank of GWV */
	/* Main loop */
  for(;;)
  {
		e21 = e2-e1;
		pe21 = e21==e1 ? pe1 : powiu(p,e21);
    if(DEBUGLEVEL) pari_printf("piclifttors: Lifting %Ps-torsion point from prec O(%Ps^%lu) to O(%Ps^%lu)\n",l,p,e1,p,e2);
    J2 = e2<efin ? JacRed(J,e2) : J;
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
		worker = snm_closure(is_entry("_PicLift_worker"),vFixedParams);
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
		if(DEBUGLEVEL>=3||(lg(KM)==1)) printf("picliftors: dim ker lift: %ld\n",lg(KM)-1);
		if(cmpii(pe21,powiu(l,g+1))<=0)
  	{
			av2 = avma;
    	if(DEBUGLEVEL>=2) printf("piclifttors by mul\n");
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
			if(DEBUGLEVEL>=2) printf("piclifttors by chart\n");
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
						if(DEBUGLEVEL>=2) printf("piclifttors: Computing coords of 0, P0=%lu\n",P0);
						c0 = PicChart(J,JgetW0(J),P0,NULL);
						if(c0) break;
						P0++;
						if(P0>nZ+g-d0)
							pari_err(e_MISC,"piclifttors: Run out of charts while computing coords of 0");
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
      	worker = snm_closure(is_entry("_PicLiftTors_Chart_worker"),vFixedParams);
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
							if(DEBUGLEVEL>=3) printf("piclifttors: Lift %ld had a chart issue\n",workid);
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
         	if(DEBUGLEVEL>=3) printf("piclifttors: Changing chart\n");
					P0++; /* New chart */
          printf("P0=%lu\n",P0);
          if(P0>nZ+g-d0)
            pari_err(e_MISC,"piclifttors: run out of charts while computing coords of 0");
          P0_tested = 0;
          c0 = NULL; /* Coords of 0 must be recomputed */
          av3 = av2;
          continue; /* Try again with this new chart */
        }
				Ktors = matkerpadic(Clifts,T,pe21,p,e21); /* Find comb with coord = 0 */
    		n = lg(Ktors)-1;
    		if(n!=1)
    		{ /* l-tors is étale, so this can only happen if Chart is not diffeo - > change chart */
					P0++; /* New chart */
      		if(DEBUGLEVEL>=3)
					{
						printf("piclifttors: Dim ker tors = %ld (expected 1), changing charts\n",n);
      			if(DEBUGLEVEL>=5)
							printf("nZ=%lu, g=%lu, d0=%lu\nP0=%lu\n",nZ,g,d0,P0);
					}
					P0++; /* New chart */
					if(P0>nZ+g-d0)
            pari_err(e_MISC,"piclifttors: run out of charts while computing coords of 0");
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
				{
					if(DEBUGLEVEL>=3) printf("piclifttors: Sum of Ktors is zero!\n");
					continue;
				}
    		Ktors = FqC_Fq_mul(Ktors,ZpXQ_inv(red,T,p,e2),T,pe2); /* Normalise so that sum = 1 */
				W = NULL; /* If done, return updated W; else update U. */
				for(i=1;i<=g+1;i++) gel(Ulifts,i) = FqM_Fq_mul(gel(Ulifts,i),gel(Ktors,i),T,pe2);
        U2 = gel(Ulifts,1);
        for(i=2;i<=g+1;i++) U2 = FpXM_add(U2,gel(Ulifts,i),pe2);
				U2 = gerepileupto(av3,U2);
				/* But first check if really l-tors, as the chart might not be injective ! */
    		if(P0_tested == 0)
				{
					if(DEBUGLEVEL>=3) pari_printf("piclifttors: Checking %Ps-tors\n",l);
					W = PicInflate_U(J2,U2,NULL);
					avtesttors = avma;
					testtors = PicIsZero_val(J2,PicMul(J2,W,l,0));
					avma = avtesttors;
					if(testtors<e2)
          {
            if(DEBUGLEVEL>=3) printf("Not actually l-torsion!!! Changing charts\n");
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
		e2<<=1;
		if(mask&1) e2--;
		mask>>=1;
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
		i += umodsu(c[n],l);
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

ulong mulOni(long k,ulong i, ulong l, ulong d)
{ /* Scalar multiplication by k in terms of integers */
	pari_sp av = avma;
	GEN c;
	ulong n;
	c = i2c(i,l,d);
	for(n=1;n<=d;n++)
		c[n] *= k;
	i = c2i(c,l);
	avma = av;
	return i;
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
      gel(a,j)[k] = umodiu(liftint(gcoeff(A,k,j)),l);
  }
	return a;
}

GEN PicTorsSpaceFrobEval(GEN J, GEN gens, GEN cgens, ulong l, GEN matFrob, GEN matAuts)
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
	for(n=1;n<ld;n++) // Initialise
		gel(done,n) = NULL;
	gel(done,ld) = mkvecsmall2(0,0);
	ndone = 1; // Number of pts; we stop when this reaches ld
	nmodF = 0; // Number of pts mod Frob
	ngens = lg(gens)-1;
	// Prepare closure for parallel code
	vJ = cgetg(2,t_VEC);
  gel(vJ,1) = J;
	worker = snm_closure(is_entry("_TorsSpaceFrob_worker"),vJ);
	// matFrob and matAuts, version Flm
	mfrob = M2Flm(matFrob,l,d,d);
	nAuts = lg(matAuts);
	mauts = cgetg(nAuts,t_VEC);
	for(a=1;a<nAuts;a++) gel(mauts,a) = M2Flm(gel(matAuts,a),l,d,d);
	// Now we are ready to begin
	// We will always keep done closed under Frob
	
	// Throw in generators and their Frob orbits
	for(n=1;n<=ngens;n++)
	{
		nmodF++; // new Frob orbit
		gel(VmodF,nmodF) = gel(gens,n); // store W in VmodF
		c = gel(cgens,n); // get its coordinates
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
		if(DEBUGLEVEL) printf("TorsSpaceFrob: Main loop, touched %lu/%lu\n",ndone,ld);
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
		if(DEBUGLEVEL>=2 && nAuts>1) printf("TorsSpaceFrob: done with auts, now touched %lu/%lu\n",ndone,ld);
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
		if(DEBUGLEVEL>=2) printf("TorsSpaceFrob: computing %lu new points\n",ntodo);
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

	if(DEBUGLEVEL) printf("TorsSpaceFrob: Evaluating %lu points\n",nmodF);
	vW = cgetg(2,t_VEC);
	ZmodF = cgetg(nmodF+1,t_VEC);
	worker = snm_closure(is_entry("_PicEval_worker"),vJ);
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
  pari_sp av=avma;
  GEN f;
  f = FqV_roots_to_pol(Z,T,pe,0);
  if(poldegree(f,varn(T))>0) pari_err(e_MISC,"Irrational coefficient: %Ps",f);
  f = simplify_shallow(f);
  f = gmodulo(f,pe);
	f = bestappr(f,NULL);
	return gerepileupto(av,f);
}

GEN OnePol(GEN N, GEN D, GEN ImodF, GEN Jfrobmat, ulong l, GEN QqFrobMat, GEN T, GEN pe)
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
		/* Multiple roots? */
		Z1 = gen_indexsort_uniq(Z,(void*)&cmp_universal,&cmp_nodata);
		if(lg(Z1)<lg(Z))
		{
			avma = av1;
    	Fi = gen_0;
		}
		else
		{
			Fi = PolExpID(Z,T,pe);
			if(typ(Fi)!=t_VEC)
				Fi = gerepilecopy(av1,mkvec2(Fi,Z));
			else
			{ /* Bestappr failed */
				avma = av1;
				Fi = gen_m1;
			}
		}
    gel(F,i+1) = Fi;
  }
  return gerepileupto(av,F);
}

GEN AllPols(GEN J, GEN Z, ulong l, GEN JFrobMat)
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
		if(All0) avma = avj; /* Drop this j */
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
	nmult = nfail = 0;
  worker = strtofunction("_OnePol");
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

	WEVn = DivAdd(Vn,WE,nVn2-nS,T,p,pe,0); /* Vn*WE = V_{n+2}(-E) */
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
		if(DEBUGLEVEL>=3) err_printf("PicNorm: F1 has zeros on D, giving up\n");
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
		if(DEBUGLEVEL>=3) err_printf("PicNorm: F2 has zeros on D, giving up\n");
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
		if(DEBUGLEVEL>=3) err_printf("Error in Frey-Ruck, retrying\n");
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

GEN PicTorsPairingInit(GEN J, GEN l)
{
	GEN res,T,p,W0;
	T = JgetT(J);
	p = Jgetp(J);
	W0 = JgetW0(J);
	res = cgetg(5,t_VEC);
	gel(res,1) = gcopy(l);
	gel(res,2) = Fq_zeta_l(T,p,l);
	gel(res,3) = AddFlipChain(l,0);
	gel(res,4) = PicChord(J,W0,W0,1); /* Non-trivial version of origin */
	return res;
}

GEN PicTorsPairing(GEN J, GEN FRparams, GEN W, GEN LinTests)
{
  pari_sp av = avma;
  GEN T,p,l,AddC,W0,z,fr,res,worker,done;
  ulong n,i;
	long pending,j,workid;
	struct pari_mt pt;
	if(typ(W)==t_VEC)
	{ /* Case of multiple tors pts */
		//printf("Into MultiPairing\n");
		n = lg(W);
		res = cgetg(n,typ(LinTests)==t_MAT?t_VEC:t_MAT);
		pending = 0;
  	worker = strtofunction("_PicTorsPairing");
  	mt_queue_start_lim(&pt,worker,n-1);
  	for(j=1;j<n||pending;j++)
  	{
    	mt_queue_submit(&pt,j,j<n?mkvecn(4,J,FRparams,gel(W,j),LinTests):NULL);
    	done = mt_queue_get(&pt,&workid,&pending);
    	if(done) gel(res,workid) = done;
  	}
  	mt_queue_end(&pt);
		return gerepilecopy(av,res);
	}
	if(typ(LinTests)!=t_VEC)
	{ /* Case of only 1 pt */
		res = PicTorsPairing(J,FRparams,W,mkvec(LinTests));
		return gerepilecopy(av,gel(res,1));
	}
	//printf("Into Pairing\n");
  T = JgetT(J);
  p = Jgetp(J);
	l = gel(FRparams,1);
  z = gel(FRparams,2);
  AddC = gel(FRparams,3);
  W0 = gel(FRparams,4);
  fr = PicFreyRuckMulti(J,W,l,LinTests,W0,AddC);
  n = lg(fr);
  res = cgetg(n,t_COL);
  for(i=1;i<n;i++)
    gel(res,i) = Fq_mu_l_log(gel(fr,i),z,T,p,l);
  return gerepileupto(av,res);
}

GEN PicTorsPairing_Modl(GEN J, GEN FRparams, GEN W, GEN LinTests)
{
	pari_sp av = avma;
	GEN l,res;
	l = gel(FRparams,1);
	res = PicTorsPairing(J,FRparams,W,LinTests);
	return gerepilecopy(av,gmodulo(res,l));
}

// Zeta functions

GEN ZetaFromPointCount(GEN N, ulong p, ulong g)
{
	pari_sp av = avma;
	GEN Z,L,Pi;
	ulong i;
	Z = cgetg(g+2,t_SER);
	Z[1] = 0;
  setsigne(Z,1);
  setvarn(Z,0);
  setvalp(Z,1);
  for(i=1;i<=g;i++) gel(Z,i+1) = gdiv(stoi(N[i]),utoi(i));
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

GEN PlaneZeta(GEN f, ulong p)
{
	pari_sp av = avma, av1;
	ulong d1,d2,df,g,a,pa,i,ix,m,n;
	GEN P,Pa,N,t,T,vars,Mf,x,fx,f00,L;

	vars = variables_vecsmall(f);
  d1 = poldegree(f,vars[1]);
  d2 = poldegree(f,vars[2]);
  if(d1>d2) df = d1;
  else df = d2;
  g = (df-1)*(df-2);
  g = g/2;
  t = varlower("t",vars[2]);
	Mf = RgXX_to_RgM(f,df+1);
	f00 = cgetg(df+3,t_POL);
	f00[1] = 0;
	setsigne(f00,1);
	setvarn(f00,0);
	for(i=0;i<=df;i++)
	{
		gel(f00,i+2) = gcoeff(Mf,i+1,df+1-i);
	}
	P = utoi(p);

	N = cgetg(g+1,t_VECSMALL); /* Point counts */
	x = cgetg(g+1,t_VEC);
	for(i=1;i<=g;i++) gel(x,i) = gen_0;
	Pa = gen_1;
	for(a=1;a<=g;a++) /* Count C(F_{p^a}) */
	{
		if(a==1) T = t;
		else T=liftint(ffinit(P,a,varn(t)));
		n = 0;
		Pa = mulii(Pa,P);
		pa = itou(Pa); /* pa = p^a = q, detects overflows */
		av1 = avma;
		for(ix=0;ix<pa;ix++) /* Loop over F_q */
		{
			avma = av1;
			m = ix;
			for(i=1;i<=a;i++)
			{
				gel(x,i) = utoi(m%p);
				m = m/p;
			}
			fx = poleval(f,gtopolyrev(x,varn(T)));
			n += lg(polrootsmod(fx,mkvec2(T,P)))-1;
		}
		if(itou(gel(f00,df+2))%p == 0) n++;
		n += lg(polrootsmod(f00,mkvec2(T,P)))-1;
		N[a] = n;
	}
	L = ZetaFromPointCount(N,p,g);
	return gerepileupto(av,L);
}

GEN SuperZeta(GEN f, ulong m, ulong p) /* y^m = f(x), assumes f sqfree and gcd(deg(f),m)=1 */
{
	pari_sp av = avma, av1;
	GEN N,P,Pa,x,T,t,fx,L;
	ulong d,g,a,pa,ix,i,n,mx,e1,e2;

	d = degree(f);
	g = (m-1)*(d-1);
	g = g/2;

	P = utoi(p);
	t = varlower("t",gvar(f));
  N = cgetg(g+1,t_VECSMALL); /* Point counts */
  x = cgetg(g+1,t_VEC); /* Value of x in Fq */
  for(i=1;i<=g;i++) gel(x,i) = gen_0;
  Pa = gen_1;

  for(a=1;a<=g;a++) /* Count C(F_{p^a}) */
  {
		Pa = mulii(Pa,P);
    pa = itou(Pa); /* pa = p^a = q, detects overflows */
		e1 = ugcd(pa-1,m);
		if(e1==1)
		{ /* y -> y^m is bijective on Fq so point counting is trivial */
			N[a] = pa+1;
			continue;
		}
		e2 = (pa-1)/e1; /* x in Fq* is an m-th power iff. x^e2==1, in which case it has e1 m-th roots */
    if(a==1) T = t;
    else T=liftint(ffinit(P,a,varn(t)));
    n = 1; /* Point at oo */
    av1 = avma;
    for(ix=0;ix<pa;ix++) /* Loop over Fq */
    {
      avma = av1;
      mx = ix;
      for(i=1;i<=a;i++)
      {
        gel(x,i) = utoi(mx%p);
        mx = mx/p;
      }
      fx = poleval(f,gmodulo(gmodulo(gtopolyrev(x,varn(T)),P),T));
			fx = liftall(fx);
			if(gequal0(fx))
			{
				n++;
			}
			else
			{
				fx = Fq_powu(fx,e2,T,P);
				if(gequal1(fx))
					n += e1;
			}
    }
    N[a] = n;
  }
	L = ZetaFromPointCount(N,p,g);
	return gerepileupto(av,L);
}

/* Tests: Is this point on that curve? */

long PtIsOnSuperellCurve(GEN f, ulong m, GEN P)
{
	pari_sp av = avma;
	long res;
	res = gequal(gpowgs(gel(P,2),m),poleval(f,gel(P,1)));
	avma = av;
	return res;
}

long PtIsOnHyperellCurve(GEN F, GEN P)
{
	pari_sp av = avma;
	GEN x,y,y2,f,h,fx;
	long res;

	x = gel(P,1);
	y = gel(P,2);
	if(typ(F)==t_VEC)
	{
		f = gel(F,1);
		h = gel(F,2);
		y2 = poleval(h,x);
		y2 = gadd(y2,y);
		y2 = gmul(y2,y);
		fx = poleval(f,x);
	}
	else
	{
		y2 = gsqr(y);
		fx = poleval(F,x);
	}
	res = gequal(y2,fx);
	avma = av;
	return res;
}

long TotalDegree(GEN F)
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

GEN PolHomogenise(GEN f, GEN z, long D)
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

long PtIsOnPlaneCurve(GEN F, GEN P)
{
	pari_sp av = avma;
	GEN vars, val;
	long res,nvars;

	vars = variables_vecsmall(F);
	nvars = lg(vars);
	if(lg(P) > nvars)
		F = PolHomogenise(F,gel(P,nvars),-1);
	val = gsubst(F,vars[1],gel(P,1));
	val = gsubst(val,vars[2],gel(P,2));
	if(nvars==4)
	{
		if(lg(P)==4)
			val = gsubst(val,vars[3],gel(P,3));
		else
			val = gsubst(val,vars[3],gen_1);
	}
	res = gequal0(val);
	avma = av;
	return res;
}

// RR spaces, easy cases

GEN HyperRR(ulong n, ulong g, GEN u, GEN v, GEN x, GEN y)
{ /* L(n*OO - {u(x)=0, y=v(x)}) on hyperell y²=f_{2g+2}(x) */
	pari_sp av = avma;
	GEN L;
	ulong a,b,i;
	a = n+1-degree(u);
	b = n-g;
	L = cgetg(a+b+1,t_VEC);
	gel(L,1) = gcopy(u);
	for(i=2;i<=a;i++)
		gel(L,i) = gmul(gel(L,i-1),x);
	gel(L,a+1) = gsub(y,v);
	for(i=2;i<=b;i++)
		gel(L,a+i) = gmul(gel(L,a+i-1),x);
	return gerepileupto(av,L);
}

GEN HyperRRdata(GEN f, GEN P12)
{ /* RR data needed to initialise Jacobian J of C:y²=f(x).
		 P12 must be a vector of two points on C which are not conj by hyperell invol.
		 P12 is used to construst a map J -> A1. If P12=NULL, this map is not constructed. */
	pari_sp av = avma;
	GEN h,x,y,xshift,P1,P2,x1,y1,x2,y2,L,L1,L2,eqn,Auts,res;
	ulong d,g;
	if(P12)
	{
		P1 = gel(P12,1);
		if(PtIsOnHyperellCurve(f,P1)!=1)
			pari_err(e_MISC,"the point %Ps is not on the hyperelliptic curve defined by %Ps",P1,f);
		x1 = gel(P1,1);
		y1 = gel(P1,2);
		P2 = gel(P12,2);
    if(PtIsOnHyperellCurve(f,P2)!=1)
      pari_err(e_MISC,"the point %Ps is not on the hyperelliptic curve defined by %Ps",P2,f);
    x2 = gel(P2,1);
    y2 = gel(P2,2);
	}
	else x1=x2=y1=y2=NULL; /* Prevent compiler from freaking out */
	if(typ(f)==t_VEC)
	{
		h = gel(f,2);
		f = gel(f,1);
		f = gadd(gmul(f,stoi(4)),gsqr(h));
		if(P12)
		{
			y1 = gadd(gmul(y1,gen_2),poleval(h,x1));
			y2 = gadd(gmul(y2,gen_2),poleval(h,x2));
		}
	}
	f = gcopy(f);
	setvarn(f,0); /* Make var = x */
	d = degree(f);
	if(d%2)
	{ /* f has odd degree, change model */
		xshift = deg1pol_shallow(gen_1,gen_1,0);
		while(1)
		{
			if(gequal0(gel(f,2))==0)
			{
				if(P12)
				{
					if(gequal0(x1)==0 && gequal0(x2)==0)
					{
						break;
					}
				}
				else
				{
					break;
				}
			}
			f = poleval(f,xshift); /* f(x+1) */
			if(P12)
			{
				x1 = gsub(x1,gen_1);
				x2 = gsub(x2,gen_1);
			}
		}
		f = RgX_shift(polrecip(f),1); /* x^{d+1}*f(1/x) */
		d++;
		if(P12)
		{
			x1 = ginv(x1);
			x2 = ginv(x2);
			y1 = gdiv(y1,gpowgs(x1,d/2));
			y2 = gdiv(y2,gpowgs(x2,d/2));
		}
	}
	g = d/2-1;
	x = pol_x(0);
	y = pol_x(1);
	L = cgetg(4,t_VEC);
	gel(L,1) = HyperRR(g+1,g,gen_1,gen_0,x,y);
	gel(L,2) = HyperRR(d,g,gen_1,gen_0,x,y);
	if(P12)
  {
		if(g%2)
		{
			L1 = HyperRR(3*(g+1)/2,g,gsub(x,x1),y1,x,y);
			L2 = HyperRR(3*(g+1)/2,g,gsub(x,x2),y2,x,y);
		}
		else
		{
			L1 = HyperRR(3*g/2+2,g,gmul(gsub(x,x1),gsub(x,x2)),gdiv(gadd(gmul(gsub(y2,y1),x),gsub(gmul(y1,x2),gmul(y2,x1))),gsub(x2,x1)),x,y);
			L2 = HyperRR(3*g/2+1,g,gen_1,gen_0,x,y);
		}
		gel(L,3) = mkvec2(L1,L2);
  }
  else gel(L,3) = gen_0;
	eqn = gsub(gsqr(y),f);
	Auts = cgetg(2,t_VEC);
	gel(Auts,1) = cgetg(3,t_VEC);
	gmael(Auts,1,1) = mkvecn(3,x,gneg(y),gen_1); /* Hyperell invol */
	gmael(Auts,1,2) = gen_m1; /* Action on J */
	res = mkvecn(5,eqn,Auts,utoi(g),utoi(d),L);
	return gerepilecopy(av,res);
}

GEN HyperPicInit(GEN f, GEN p, ulong a, long e, GEN P12)
{
	pari_sp av = avma;
	GEN J,Lp,RRdata,bad;
	Lp = hyperellcharpoly(gmodulo(f,p));
	RRdata = HyperRRdata(f,P12);
	bad = pol_x(1); /* y */
	J = PicInit(gel(RRdata,1),gel(RRdata,2),itou(gel(RRdata,3)),itou(gel(RRdata,4)),gel(RRdata,5),bad,p,a,e,Lp);
	return gerepileupto(av,J);
}

GEN SuperRR(ulong n, ulong d, ulong m, GEN x, GEN y)
{ /* L(n*OO) on y^m=f_d(x)
		 assuming fsqfree and (m,d)=1
		 so deg x = m, deg y = d
		 -> x^a*y^b for m*a+b*d<=n */
	pari_sp av = avma;
	GEN yb,xayb,L;
	ulong A,B,a,b,i;
	B = n/d;
	if(B >= m)
		B = m-1;
	L = cgetg(1+(1+n/m)*(1+B),t_VEC);
	i = 1;
	for(b=0;b<=B;b++)
	{
		A = (n-d*b)/m;
		if(b==0)
			yb = gen_1;
		else
			yb = gmul(yb,y);
		gel(L,i++) = yb;
		for(a=1;a<=A;a++)
		{
			xayb = gmul(gel(L,i-1),x);
	    gel(L,i++) = xayb;
		}
	}
	setlg(L,i);
	return gerepilecopy(av,L);
}

GEN SuperRRdata(GEN f, ulong m, GEN P)
{
	pari_sp av = avma;
	ulong d,g,d0;
	GEN x,y,L,L2,E2,Auts,eqn,res;

	if(issquarefree(f)==0)
		pari_err(e_MISC,"%Ps is not squarefree",f);
	d = degree(f);
	if(ugcd(m,d)>1)
		pari_err(e_IMPL,"%lu and the degree of %Ps are not coprime",m,f);
	if(P)
	{
		if(PtIsOnSuperellCurve(f,m,P)==0)
			pari_err(e_MISC,"%Ps is not on this superelliptic curve",P);
	}
	g = ((d-1)*(m-1))/2;
	d0 = 2*g+1;
	x = pol_x(0);
	y = pol_x(1);
	L = cgetg(4,t_VEC);
	gel(L,1) = SuperRR(d0,d,m,x,y);
	gel(L,2) = SuperRR(2*d0,d,m,x,y);
	if(P)
	{
		gel(L,3) = cgetg(3,t_VEC);
		gmael(L,3,1) = SuperRR(d0+g,d,m,x,y);
		L2 = SuperRR(d0+g+1,d,m,x,y);
		E2 = gsubst(gsubst(L2,0,gel(P,1)),1,gel(P,2));
		gmael(L,3,2) = gmul(L2,ker(gtomat(E2)));
	}
	else gel(L,3) = gen_0;
	if(m%2)
	{
		Auts = cgetg(1,t_VEC);
	}
	else
	{
		Auts = cgetg(2,t_VEC);
	  gel(Auts,1) = cgetg(3,t_VEC);
	  gmael(Auts,1,1) = mkvecn(3,x,gneg(y),gen_1); /* Hyperell invol */
	  gmael(Auts,1,2) = gen_m1; /* Action on J */
	}
	f = gcopy(f);
	setvarn(f,0);
	eqn = gsub(gpowgs(y,m),f);
	res = mkvecn(5,eqn,Auts,utoi(g),utoi(d0),L);
	return gerepilecopy(av,res);
}

GEN SuperPicInit(GEN f, ulong m, GEN p, ulong a, long e, GEN P)
{
  pari_sp av = avma;
  GEN J,Lp,RRdata,bad;
	Lp = SuperZeta(f,m,itou(p));
  RRdata = SuperRRdata(f,m,P);
	bad = pol_x(1); /* y */
  J = PicInit(gel(RRdata,1),gel(RRdata,2),itou(gel(RRdata,3)),itou(gel(RRdata,4)),gel(RRdata,5),bad,p,a,e,Lp);
  return gerepileupto(av,J);
}

GEN SmoothRR(ulong n, ulong d, GEN x, GEN y)
{ /* L(n*OO) on smooth plane curve of deg d: x^a*y^b for a+b<=n */
	pari_sp av = avma;
  GEN yb,xayb,L;
  ulong A,B,a,b,i;
  B = n;
  if(B >= d)
    B = d-1;
  L = cgetg(1+(B+1)*(n+1)-(B*(B+1))/2,t_VEC);
  i = 1;
  for(b=0;b<=B;b++)
  {
    A = n-b;
    if(b==0)
      yb = gen_1;
    else
      yb = gmul(yb,y);
    gel(L,i++) = yb;
    for(a=1;a<=A;a++)
    {
      xayb = gmul(gel(L,i-1),x);
      gel(L,i++) = xayb;
    }
  }
  return gerepileupto(av,L);
}

int SmoothIsGeneric(GEN f, ulong d, GEN p, long x, long y, GEN P)
{ /* Coeff of x^d and y^d must be nonzero, and none of the pts in P at infty */
	pari_sp av = avma;
	ulong i,j,n;
	if(gequal0(modii(polcoef_i(f,d,x),p)))
	{
		avma = av;
		return 0;
	}
	if(gequal0(modii(polcoef_i(f,d,y),p)))
  {
    avma = av;
    return 0;
  }
	avma = av;
	if(P==NULL) return 1;
	for(i=1;i<=2;i++)
	{
		n = lg(gel(P,i));
		for(j=1;j<n;j++)
		{
			if(gequal0(modii(gmael3(P,i,j,3),p)))
    		return 0;
		}
	}
	return 1;
}

GEN SmoothGeneric(GEN f0, ulong d, GEN pr, GEN P0)
{
	pari_sp av = avma;
	GEN f,A,Vars,vars,xy1,uvw,u,v,w,P,p,B,B2,C,ci,cij;
	ulong i,j,n,b,b2;
	
	P = gen_0;
	Vars = variables_vec(f0);
	vars = variables_vecsmall(f0);
	if(lg(Vars)==4)
		f0 = gsubst(f0,vars[3],gen_1); /* Dehomogenise */
	if(P0)
	{ /* Switch to proj coords */
		P0 = gcopy(P0);
		for(i=1;i<=2;i++)
  	{
    	n = lg(gel(P0,i));
    	for(j=1;j<n;j++)
    	{
      	if(lg(gmael(P0,i,j))==3)
				{
        	p = cgetg(4,t_VEC);
					gel(p,1) = gmael3(P0,i,j,1);
					gel(p,2) = gmael3(P0,i,j,2);
					gel(p,3) = gen_1;
					gmael(P0,i,j) = p;
				}
			}
    }
		P = gcopy(P0);
  }
	xy1 = cgetg(4,t_COL);
	gel(xy1,1) = gel(Vars,1);
	gel(xy1,2) = gel(Vars,2);
	gel(xy1,3) = gen_1;
	f = f0;
	A = cgetg(4,t_MAT);
	for(i=1;i<=3;i++)
		gel(A,i) = cgetg(4,t_COL);
	b=1;
	for(b2=1;;b2++)
	{
		if(b2==10)
		{
			b2 = 0;
			b++;
		}
		if(SmoothIsGeneric(f,d,pr,vars[1],vars[2],P0?P:NULL)) break;
		/* get random change of vars */
		B = utoi(b);
		B2 = utoi(2*b+1);
		do
		{
			for(j=1;j<=3;j++)
			{
				C = gel(A,j);
				for(i=1;i<=3;i++)
					gel(C,i) = subii(genrand(B2),B);
			}
		} while(gequal0(modii(ZM_det(A),pr)));
		uvw = gmul(A,xy1); /* change of vars */
		u = gel(uvw,1); v = gel(uvw,2); w = gel(uvw,3);
		f = gen_0;
		for(i=0;i<=d;i++)
		{
			ci = polcoef_i(f0,i,vars[1]);
			for(j=0;j<=d;j++)
			{
				cij = polcoef_i(ci,j,vars[2]);
				f = gadd(f,gmul(gmul(cij,gpowgs(w,d-i-j)),gmul(gpowgs(u,i),gpowgs(v,j))));
			}
		}
		if(P0)
		{
			A = shallowtrans(RgM_inv(A));
			for(i=1;i<=2;i++)
			{
				n = lg(gel(P0,i));
				for(j=1;j<n;j++)
				{
					p = gmael(P0,i,j);
					p = gmul(p,A);
					p = gdiv(p,content0(p,NULL));
					gmael(P,i,j) = p;
				}
			}
		}
	}
	if(P0)
	{
		/* Switch to affine coordinates */
		for(i=1;i<=2;i++)
  	{
    	n = lg(gel(P0,i));
    	for(j=1;j<n;j++)
			{
    		p = gmael(P,i,j);
				gmael(P,i,j) = mkvec2(gdiv(gel(p,1),gel(p,3)),gdiv(gel(p,2),gel(p,3)));
    	}
		}	
	}
	return gerepilecopy(av,mkvec2(f,P));
}

GEN SmoothRRdata(GEN f, GEN p, GEN P)
{
	pari_sp av = avma;
	ulong d,i,j,n,g,d0,m;
	long lx,ly;
	GEN res,vars,x,y,L,M,MP;

	d = TotalDegree(f);
  if(d<=2)
    pari_err(e_MISC,"This curve has genus zero");
	if(P)
	{
		for(i=1;i<=2;i++)
    {
      n = lg(gel(P,i));
			if(d%2)
			{
				if(n!=d)
					pari_err(e_MISC,"For smooth curves of degree %lu, please provide two distinct vectors of %lu distinct points",d,d-1);
			}
			else
			{
        if(n!=d/2)
          pari_err(e_MISC,"For smooth curves of degree %lu, please provide two distinct vectors of %lu distinct points",d,d/2-1);
      }
      for(j=1;j<n;j++)
      {
        if(PtIsOnPlaneCurve(f,gmael(P,i,j))==0)
					pari_err(e_MISC,"The point %Ps is not on this curve",gmael(P,i,j));
			}
    }
	}
	res = SmoothGeneric(f,d,p,P);
	f = gel(res,1);
	vars = variables_vec(f);
	x = gel(vars,1);
	y = gel(vars,2);
	if(P) P = gel(res,2);
	g = ((d-1)*(d-2))/2;
	d0 = (d-2)*d;
	L = cgetg(4,t_VEC);
	gel(L,1) = SmoothRR(d-2,d,x,y);
	gel(L,2) = SmoothRR(2*(d-2),d,x,y);
	if(P)
	{
		vars = variables_vecsmall(f);
		lx = vars[1]; ly = vars[2];
		gel(L,3) = cgetg(3,t_VEC);
		if(d%2) m = (3*d-5)/2;
		else m = 3*(d/2-1);
		M = SmoothRR(m,d,x,y);
		for(i=1;i<=2;i++)
		{
			n = lg(gel(P,i));
			MP = cgetg(n,t_COL);
			for(j=1;j<n;j++)
				gel(MP,j) = gsubst(gsubst(M,lx,gmael3(P,i,j,1)),ly,gmael3(P,i,j,2));
			gmael(L,3,i) = gmul(M,ker(matconcat(MP)));
		}
	}
	else gel(L,3) = gen_0;
	res = mkvecn(5,f,cgetg(1,t_VEC),utoi(g),utoi(d0),L);
	return gerepilecopy(av,res);
}

GEN SmoothPicInit(GEN f, GEN p, ulong a, long e, GEN P)
{
	pari_sp av = avma;
  GEN J,Lp,RRdata;
  RRdata = SmoothRRdata(f,p,P);
	Lp = PlaneZeta(gel(RRdata,1),itou(p));
  J = PicInit(gel(RRdata,1),gel(RRdata,2),itou(gel(RRdata,3)),itou(gel(RRdata,4)),gel(RRdata,5),gen_1,p,a,e,Lp);
  return gerepileupto(av,J);
}

// TorsGen

GEN PicRandTors(GEN J, GEN l, GEN Chi, GEN Phi, GEN seed, long returnlpow)
{ /* Random pt in J[l].
		 If Chi, get pt in J[l,Chi].
		 If Phi, Phi is a cyclo pol | x^a-1, get pt in J[Phi] (smaller card -> faster mul).
		 If seed, set randseed.
		 If return lpow, return [W,o,T,B] where W has order l^o, T=l^(o-1)*W in J[l], B in Ann_Z[x] T. */
	pari_sp av = avma;
	GEN Lp,J1,A,B,W,N,M,Psi,fa,lv,res,T,o;
	ulong a,v,d;
	if(Jgete(J)>1)
	{
		J1 = JacRed(J,1);
		T = PicRandTors(J1,l,Chi,Phi,seed,0);
		T = PicLiftTors(J,T,l,1);
		return gerepileupto(av,T);
	}
	Lp = JgetLp(J);
	if(gequal0(Lp))
		pari_err(e_MISC,"this Jacobian does not contain its local L factor which is required for point counting");
	if(Chi && gequal0(Chi)) Chi = NULL;
	if(Phi && gequal0(Phi)) Phi = NULL;
	a = degree(JgetT(J));
	A = cgetg(a+3,t_POL); /* x^a-1 */
	A[1] = 0;
	setsigne(A,1);
	setvarn(A,0);
	gel(A,2) = gen_m1;
	gel(A,a+2) = gen_1;
	for(v=1;v<a;v++)
		gel(A,v+2) = gen_0;
	B = A;
	W = PicRand(J,seed);
	if(Phi)
	{ /* Project onto J[Phi] */
		W = PicFrobPoly(J,W,RgX_div(B,Phi));
		A = B = Phi;
	}
	N = ZX_resultant(Lp,B); /* Order of submodule we work in */
	v = Z_pvalrem(N,l,&M);
	if(v==0)
		pari_err(e_MISC,"No %Ps-torsion",l);
	W = PicMul(J,W,M,0); /* Project onto l^oo part, main bottleneck! */
	B = FpX_gcd(Lp,B,l); /* [l^...]W in J[l,B] */
	if(Chi)
	{
		Chi = FpX_gcd(Chi,B,l);
		Psi = FpX_div(B,Chi,l);
		d = degree(Psi);
		if(d)
		{
			Psi = FpX_normalize(Psi,l);
			if(v>1)
			{ /* Lift Psi mod l^v as a factor of A */
				fa = mkvec2(Psi,FpX_div(A,Psi,l));
				fa = polhensellift(A,fa,l,v);
				Psi = gel(fa,1);
			}
			lv = powis(l,v);
			Psi = FpX_center_i(Psi,lv,shifti(lv,-1));
			W = PicFrobPoly(J,W,Psi); /* Project onto J[Chi] */
		}
	}
	res = PicTorsOrd(J,W,l,2); /*[T,o], W of order l^o, T=[l^(o-1)]W */
	o = gel(res,2);
	if(gequal0(o))
	{
		if(DEBUGLEVEL>=2)
			pari_printf("PicRandTorsPt got zero (Phi=%Ps)\n",Phi?Phi:gen_0);
		return gen_0;
	}
	T = gel(res,1);
	if(returnlpow==0)
	{
		return gerepileupto(av,T);
	}
	if(Chi)
		B = FpX_normalize(Chi,l);
	res = mkvecn(4,W,o,T,B);
	return gerepilecopy(av,res);
}

GEN VecExtend1_shallow(GEN V, GEN X)
{
	ulong n,i;
	GEN W;
	n = lg(V);
	W = cgetg(n+1,t_VEC);
	for(i=1;i<n;i++)
		gel(W,i) = gel(V,i);
	gel(W,n) = X;
	return W;
}

GEN VecSmallExtend1_shallow(GEN V, long x)
{
  ulong n,i;
  GEN W;
  n = lg(V);
  W = cgetg(n+1,t_VECSMALL);
  for(i=1;i<n;i++)
    W[i] = V[i];
  W[n] = x;
  return W;
}

GEN Fp_Long2ShortRel(GEN A, GEN p)
{ /* [a1,..,an,b] -> -1/b * [a1,..,an] */
	GEN B,b,p1;
	ulong n,i;
	n = lg(A)-1;
	B = cgetg(n,t_VEC);
	if(n>1)
	{
		b = gel(A,n);
		b = Fp_inv(b,p);
		b = negi(b);
		p1 = shifti(p,-1);
		for(i=1;i<n;i++)
			gel(B,i) = Fp_center(Fp_mul(gel(A,i),b,p),p,p1);
	}
	return B;
}

GEN PicTors_UpdatePairings(GEN J, GEN FRparams, GEN BT, GEN R, GEN Tnew, GEN TnewPairings, int* replace)
{
  /* BT contains d=#BT pts of J[l]
     Tnew pt of J[l]
     Assume that the matrix R = <BT[j]|LinTests[i]> has rank d. (H)
     If Tnew lies in the span of BT, set replace to -1,
		 and return coeffs of a lin dep relation between Tnew on BT.
		 If Tnew is indep of BT, let R2 = [BT,Tnew|LinTests2] of rank d+1,
		 and LinTests2 is either exactly equal to LinTests,
		 in which case replace is set to 0 and we return R2,
		 or differs from LinTests at exactly one place,
		 in which case replace is set to this index and we return [R2,NewTest].
  */
	pari_sp av=avma, avK;
	GEN l,R2,KR2,KR,BT2,NewTest,Rnew;
	ulong d,nTests,j,rk;
	int i;
	l = gel(FRparams,1);
	d = lg(R);
	R2 = cgetg(d+1,t_MAT); /* Right append new pairings to old pairings */
	for(j=1;j<d;j++)
		gel(R2,j) = gel(R,j);
	nTests = lg(TnewPairings);
	gel(R2,d) = cgetg(nTests,t_COL);
	for(i=1;i<nTests;i++)
		gcoeff(R2,i,d) = gel(TnewPairings,i);
	avK = avma;
	KR2 = FpM_ker(R2,l); /* Look for relations */
	rk = lg(KR2);
	if(rk>2) /* Not supposed to happen by (H) */
		pari_err(e_MISC,"Bug in PicTors_UpdatePairings, please report");
	if(rk==1) /* No relation? */
	{
		if(DEBUGLEVEL>=3) printf("UpdatePairings: good, no relation.\n");
		avma = avK;
		*replace = 0;
		return R2;
	}
	KR2 = gel(KR2,1); /* Possibile relation */
	if(DEBUGLEVEL>=3) pari_printf("UpdatePairings: found pseudo-relation %Ps.\n",KR2);
	KR = Fp_Long2ShortRel(KR2,l);
	if(PicEq(J,Tnew,PicLC(J,KR,BT)))
	{ /* The relation really holds */
		if(DEBUGLEVEL>=3) printf("UpdatePairings: the pseudo-relation actually holds.\n");
		*replace = -1;
		return gerepileupto(av,KR2);
	}
	/* The relation does not actually hold -> our Tests are not independent. */
	if(DEBUGLEVEL>=3) printf("UpdatePairings: the pseudo-relation does not hold, changing LinTests.\n");
	BT2 = VecExtend1_shallow(BT,Tnew);
	avK = avma;
	do
	{
		avma = avK;
		NewTest = PicChord(J,PicRand(J,NULL),PicRand(J,NULL),1);
		Rnew = PicTorsPairing(J,FRparams,BT2,NewTest);
		if(DEBUGLEVEL>=4) pari_printf("UpdatePairings: the new test gives pairings %Ps.\n",Rnew);
	} while(gequal0(FpV_FpC_mul(Rnew,KR2,l))); /* Find new test which disproves this fake relation */
	/* Now we have d+1 forms of rank d; find one we can drop */
	KR2 = FpM_ker(shallowtrans(R2),l); /* Relation between forms */
	KR2 = gel(KR2,1);
	for(i=1;gequal0(gel(KR2,i));i++) {}
	for(j=1;j<=d;j++)
		gcoeff(R2,i,j) = gel(Rnew,j);
	if(DEBUGLEVEL>=3) pari_printf("UpdatePairings: dropping test %lu; now R=%Ps.\n",i,R2);
	*replace = i;
	return gerepilecopy(av,mkvec2(R2,NewTest));
}

GEN FpM_GuessLastColFromCharpoly(GEN A, GEN chi, GEN p)
{
	pari_sp av = avma;
	ulong n,i,j;
	GEN x,B,chi0,M,u;
	n = lg(A)-1;
	A = gcopy(A);
	for(i=1;i<=n;i++)
		gcoeff(A,i,n) = gen_0;
	gcoeff(A,n,n) = Fp_neg(addii(gtrace(A),gel(chi,n+1)),p);
	chi0 = FpX_sub(chi,FpM_charpoly(A,p),p);
	x = pol_x(0);
	B = adjsafe(gsub(x,A));
	M = cgetg(n+1,t_MAT);
	for(j=1;j<n;j++)
	{
		gel(M,j) = cgetg(n,t_COL);
		for(i=1;i<n;i++)
			gcoeff(M,i,j) = polcoef(gcoeff(B,n,j),i-1,0);
	}
	gel(M,n) = cgetg(n,t_COL);
	for(i=1;i<n;i++)
		gcoeff(M,i,n) = polcoef(chi0,i-1,0);
	M = FpM_ker(M,p);
	if(lg(M)!=2)
	{
		if(DEBUGLEVEL>=3) printf("Unable to guess last column from charpoly.\n");
		avma = av;
		return NULL;
	}
	u = Fp_inv(gcoeff(M,n,1),p);
	for(i=1;i<n;i++)
		gcoeff(A,i,n) = Fp_mul(gcoeff(M,i,1),u,p);
	return gerepilecopy(av,A);
}

GEN PicTorsGetAutMats(GEN J, GEN B, GEN FRparams, GEN LinTests, GEN R)
{
	pari_sp av = avma;
	ulong nAuts,d,i;
	GEN l,mats,Ri,k;
	l = gel(FRparams,1);
	R = FpM_inv(R,l);
	nAuts = lg(JgetAutData(J));
	d = lg(B)-1;
	mats = cgetg(nAuts,t_VEC);
	for(i=1;i<nAuts;i++)
	{
		k = JgetAutKnown(J,i);
		if(gequal0(k))
		{
			Ri = PicTorsPairing(J,FRparams,B,LinTests);
			gel(mats,i) = FpM_mul(R,Ri,l);
		}
		else
			gel(mats,i) = gmul(k,matid(d));
	}
	return gerepilecopy(av,mats);
}

GEN PicTorsBasis_worker(GEN J, GEN l, GEN Chi, GEN Phi, GEN FRparams, GEN Lintests, GEN LinTestsNames, GEN seed)
{
	pari_sp av = avma;
	GEN res,W,o,T,B,Pairings;

	res = PicRandTors(J,l,Chi,Phi,seed,1);
	if(gequal0(res)) return res;
	W = gel(res,1);
	o = gel(res,2);
	T = gel(res,3);
	B = gel(res,4);
	Pairings = PicTorsPairing(J,FRparams,T,Lintests);
	res = mkvecn(6,W,o,T,B,Pairings,LinTestsNames);
	return gerepilecopy(av,res);
}

GEN PicRefreshPairings(GEN J, GEN FRparams, GEN T, GEN Pairings, GEN UsedNames, GEN Want, GEN WantNames)
{ /* We have [T,u] for u in Used, but we want [T,w] for w in Want. Get that without recomputing anything that we already have. */
	pari_sp av = avma;
	ulong nUsed,nWant,i,j,k;
	GEN res,todo,todoindex,NewPairings;

	nUsed = lg(UsedNames);
	nWant = lg(Want);
	res = cgetg(nWant,t_COL);
	todo = cgetg(nWant,t_VEC);
	todoindex = cgetg(nWant,t_VECSMALL);
	k = 1;
	for(i=1;i<nWant;i++)
	{ /* Do we already have [T,Want[i]] somewhere? */
		gel(res,i) = NULL; /* For now, no */
		for(j=1;j<nUsed;j++)
		{
			if(WantNames[i]==UsedNames[j])
			{
				gel(res,i) = gel(Pairings,j);
				break;
			}
		}
		if(gel(res,i)==NULL) /* Have not found it? */
		{ /* Then we'll have to compute it. Store this info for later */
			gel(todo,k) = gel(Want,i);
			todoindex[k] = i;
			k++;
		}
	}
	/* OK, do we need to compute any new pairings? */
	if(DEBUGLEVEL>=2) printf("PicRefreshPairings: %lu pairings need to be refreshed\n",k-1);
	if(k>1)
	{
		setlg(todo,k);
		NewPairings = PicTorsPairing(J,FRparams,T,todo);
		for(j=1;j<k;j++)
		{
			gel(res,todoindex[j]) = gel(NewPairings,j);
		}
	}
	return gerepilecopy(av,res);
}

void FpM_ConcatRelBlock(GEN* pA, ulong n, GEN rel, GEN p)
{
	GEN A,B;
	ulong m,i,j;

	if(n==0) return;
	A = *pA;
	m = lg(A);
	*pA = B = cgetg(m+n,t_MAT);
	for(j=1;j<m+n-1;j++)
		gel(B,j) = cgetg(m+n,t_COL);
	for(j=1;j<m;j++)
	{
		for(i=1;i<m+n;i++)
			gcoeff(B,i,j) = i<m?gcoeff(A,i,j):gen_0;
	}
	for(j=m;j<m+n-1;j++)
	{
		for(i=1;i<m+n;i++)
			gcoeff(B,i,j) = i==j+1?gen_1:gen_0;
	}
	if(rel)
		gel(B,m+n-1) = Fp_Long2ShortRel(rel,p);
	else
	{
		gel(B,m+n-1) = cgetg(m+n,t_COL);
		for(i=1;i<m+n;i++)
			gcoeff(B,i,m+n-1) = gen_0;
	}
	*pA = B;
}

void PicTorsBasis_UsePt(GEN J, GEN Pt, GEN Chi, ulong d, ulong* pr, GEN* pBW, GEN* pBo, GEN* pBT, GEN* pmatFrob, GEN FRparams, GEN* pmatPairings, GEN* pLinTests, GEN* pLinTestsNames, ulong* pNewTestName)
{ /* Generate as much as possible from this point. Returns nothing, modifies its pointer arguments */
	GEN W,T,B,Tpairings,UsedTestsNames,rel,res,l;
	ulong o,dB,iFrob,i;
	long m;
	int replace;
	l = gel(FRparams,1);
	W = gel(Pt,1);
  o = itou(gel(Pt,2));
  T = gel(Pt,3);
  B = gel(Pt,4);
  dB = gequal0(B)?0:degree(B);
	if(DEBUGLEVEL>=2) pari_printf("Bound B = %Ps\n",B);
  Tpairings = gel(Pt,5);
  UsedTestsNames = gel(Pt,6);
  /* Make sure pairings are current */
	if(DEBUGLEVEL>=2) printf("PicTorsBasis: Refreshing pairings\n");
  Tpairings = PicRefreshPairings(J,FRparams,T,Tpairings,UsedTestsNames,*pLinTests,*pLinTestsNames);
	rel = NULL;
  for(iFrob=0;;iFrob++)
  {
		if(DEBUGLEVEL) printf("PicTorsBasis: Working on %luth iterate under Frob\n",iFrob);
		res = PicTors_UpdatePairings(J,FRparams,*pBT,*pmatPairings,T,Tpairings,&replace);
		if(replace==-1)
		{ /* T is dependent on BT */
			rel = res;
			if(DEBUGLEVEL) pari_printf("PicTorsBasis: This point is linearly dependent on the previous ones: %Ps\n",rel);
			break;
		}
		/* T is independent on BT */
		(*pr)++;
		if(DEBUGLEVEL) printf("PicTorsBasis: This point is independent from the previous ones; now r=%lu\n",*pr);
		*pBW = VecExtend1_shallow(*pBW,W);
		*pBo = VecSmallExtend1_shallow(*pBo,o);
		*pBT = VecExtend1_shallow(*pBT,T);
		if(replace)
		{
			if(DEBUGLEVEL>=2) printf("PicTorsBasis: Form %d had to be changed\n",replace);
			*pmatPairings = gel(res,1);
			gel(*pLinTests,replace) = gel(res,2);
			(*pLinTestsNames)[replace] = (*pNewTestName)++;
		}
		else
			*pmatPairings = res;
		/* Apply Frob and iterate, unless B tells us that we won't get anything new, or we are done */
		if(dB && iFrob+1==dB)
		{
			if(DEBUGLEVEL) printf("PicTorsBasis: Reached bound\n");
			rel = cgetg(*pr+2,t_COL);
			for(i=1;i<=*pr-dB;i++)
				gel(rel,i) = gen_0;
			for(i=0;i<=dB;i++)
				gel(rel,(*pr+1+i)-dB) = gel(B,i+2);
			iFrob = dB;
			break;
		}
		if(*pr==d)
    { /* We are done. We know matFrob except its last column, we try to guess it. */
			if(DEBUGLEVEL) printf("PicTorsBasis: Attempting to guess last column of the matrix of Frob\n");
      FpM_ConcatRelBlock(pmatFrob,iFrob+1,NULL,l);
      res = FpM_GuessLastColFromCharpoly(*pmatFrob,Chi,l);
      if(res)
      { /* Success! */
				if(DEBUGLEVEL) printf("PicTorsBasis: Last column successfully guessed\n");
        gel(*pmatFrob,d) = gel(res,d);
        return;
      }
      /* Failure, we must resort to pairings */
			if(DEBUGLEVEL) printf("PicTorsBasis: Unable to guess last column, resorting to pairings\n");
      Tpairings = PicTorsPairing(J,FRparams,PicFrob(J,gel(*pBT,d)),*pLinTests);
      gel(*pmatFrob,d) = FpM_FpC_gauss(*pmatPairings,Tpairings,l);
      return;
    }
		if(DEBUGLEVEL) printf("PicTorsBasis: Applying Frob\n");
		W = PicFrob(J,W);
		T = PicFrob(J,T);
		Tpairings = PicTorsPairing(J,FRparams,T,*pLinTests);
  }
	/* Use rel to fill in matFrob */
	FpM_ConcatRelBlock(pmatFrob,iFrob,rel,l);
	if(*pr==d) return;
	/* Try to use rel to find a new torsion point */
	if(o==1) return;
	if(DEBUGLEVEL) pari_printf("PicTorsBasis: Attempting division of the relation %Ps, Bo=%Ps, o=%lu\n",rel,*pBo,o);
	m = o;
	for(i=1;i<lg(rel)-1;i++)
	{
		if(gequal0(gel(rel,i))) continue;
		if(m > (*pBo)[i])
			m = (*pBo)[i];
		if(m<=1) return;
	}
	for(i=1;i<=*pr;i++)
	{
		if(gequal0(gel(rel,i))) continue;
		gel(rel,i) = mulii(gel(rel,i),powis(l,(*pBo)[i]-m));
	}
	gel(rel,1+*pr) = mulii(gel(rel,1+*pr),powis(l,o-m));
	W = PicLC(J,rel,VecExtend1_shallow(*pBW,W));
	T = PicTorsOrd(J,W,l,2);
	if(DEBUGLEVEL) pari_printf("Division of the relation yields point of order %Ps^%Ps\n",l,gel(T,2));
	if(gequal0(gel(T,2))) return;
	Tpairings = PicTorsPairing(J,FRparams,gel(T,1),*pLinTests);
	Pt = mkvecn(6,W,gel(T,2),gel(T,1),gen_0,Tpairings,*pLinTestsNames);
	PicTorsBasis_UsePt(J,Pt,Chi,d,pr,pBW,pBo,pBT,pmatFrob,FRparams,pmatPairings,pLinTests,pLinTestsNames,pNewTestName);
}

GEN PicTorsBasis(GEN J, GEN l, GEN Chi)
{
	/* Computes a basis B of the subspace T of J[l] on which Frob acts with charpoly Chi
     Assumes Lp = charpoly(Frob|J), so Chi | Lp
     If Chi==NULL, then we take T=J[l]
     Also computes the matrix M of Frob and list of matrices MA of Auts w.r.t B, and returns the vector [B,M,MA] */
  /* TODO use auts that are not known to be scalars */
	pari_sp av = avma;
  GEN Lp,Diva,Phi,phi,ChiT,BW,Bo,BT,matFrob,FRparams,LinTests,LinTestsNames,matPairings,Batch,Pt,res;
  ulong a,r,d,i,j,nPhi,iPhi,nBatch,iBatch,NewTestName;
	struct pari_mt pt;
  GEN worker,done;
  long pending,workid;

	Lp = JgetLp(J);
	if(gequal0(Lp))
		pari_err(e_MISC,"This Jacobian does not contain its local L factor, which is required for point counting");
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
      if(degree(FpX_gcd(phi,Chi?Chi:Lp,l)))
        gel(Phi,++j) = phi;
    }
    nPhi = j;
		if(nPhi==0) Phi=NULL;
  }
  else Phi=NULL;
	
	if(Chi)
	{
		d = degree(Chi); /* dim T */
		ChiT = Chi;
	}
	else
	{
		d = degree(Lp);
		Chi = gen_0;
		ChiT = Lp;
	}
	r = 0; /* dim we have so far */
	BW = BT = cgetg(1,t_VEC);
	Bo = cgetg(1,t_VECSMALL);
	matFrob = matPairings = cgetg(1,t_MAT);
	FRparams = PicTorsPairingInit(J,l);
  LinTests = cgetg(d+1,t_VEC); /* pts to take pairings with */
	LinTestsNames = cgetg(d+1,t_VECSMALL); /* Name them with integers */
	for(i=1;i<=d;i++)
	{
		gel(LinTests,i) = PicChord(J,PicRand(J,NULL),PicRand(J,NULL),1); /* Random pt, well-mixed so as not throw off Pairings */
		LinTestsNames[i] = i;
	}
	NewTestName = d+1;

	nBatch = (mt_nbthreads()+1)/2;//TODO
	worker = strtofunction("_PicTorsBasis_worker");
	Batch = cgetg(nBatch+1,t_VEC);
	for(iPhi=1;;)
	{
		if(DEBUGLEVEL) printf("PicTorsBasis: Generating new batch of %lu torsion points\n",nBatch);
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
		for(i=1;i<=nBatch && r<d;i++)
		{
			if(DEBUGLEVEL) printf("PicTorsBasis: Got dimension r=%lu out of d=%lu, moving on to point %lu of batch\n",r,d,i);
			Pt = gel(Batch,i);
			if(gequal0(Pt))
			{
				if(DEBUGLEVEL>=2) printf("PicTorsBasis: This point is zero, moving on to the next one\n");
				continue;
			}
			PicTorsBasis_UsePt(J,Pt,ChiT,d,&r,&BW,&Bo,&BT,&matFrob,FRparams,&matPairings,&LinTests,&LinTestsNames,&NewTestName);
		}
		if(r==d) break;
	}
	res = cgetg(4,t_VEC);
	gel(res,1) = BT;
	gel(res,2) = matFrob;
	gel(res,3) = PicTorsGetAutMats(J,BT,FRparams,LinTests,matPairings);
	return gerepilecopy(av,res);
}

/* GalRep */

GEN FpX_root_order_bound(GEN f, GEN p)
{ /* Bounds on order of FpM whose charpoly is f */
	pari_sp av = avma;
	GEN fa,x,g,fad,a,pu,b;
	ulong n,e,d,dg,i;
	fa = FpX_factor(f,p);
	n = lg(gel(fa,1)); /* Number of factors */
	x = pol_x(varn(f));
	d = 0;
	fad = NULL;
	a = gen_1;
	pu = gen_1;
	for(i=1;i<n;i++)
	{
		g = gmael(fa,1,i);
		e = gel(fa,2)[i];
		dg = degpol(g);
		if(dg!=d)
		{
			d = dg;
			fad = factor_pn_1(p,d);
		}
		a = lcmii(a,FpXQ_order(x,fad,g,p));
		while(cmpiu(pu,e)==-1)
			pu = mulii(pu,p);
	}
	b = mulii(a,pu);
	return gerepilecopy(av,mkvec2(a,b));
}

GEN PicTors_FrobGen(GEN J, GEN l, GEN B, GEN MFrob)
{ /* Let B be an Fl-basis of a Galois-stable subspace T of J[l]
		 and MFrob the matrix of Frob on B.
		 Finds minimal generating set G of T as an Fl[Frob]-module.
		 Returns [G,CG,M] where CG are the coordinates of G
		 and M is the rational canonical form of MFrob. */
	/* TODO use Auts? */
	pari_sp av = avma, av1;
	GEN M,Q,piv,G,CG,res;
	ulong n,d,k,i;
	d = lg(B);
	M = RgM_Frobenius(gmodulo(MFrob,l),0,&Q,&piv);
	Q = centerlift(RgM_inv(Q));
	res = cgetg(4,t_VEC);
	M = centerlift(M);
  if(DEBUGLEVEL)
  {
		av1 = avma;
    pari_printf("The matrix of Frob_%Ps is\n",Jgetp(J));
    printp(mkvec(M));
		avma = av1;
  }
	gel(res,3) = M;
	n = lg(piv);
	gel(res,1) = G = cgetg(n,t_VEC);
	gel(res,2) = CG = cgetg(n,t_VEC);
	for(k=1;k<n;k++)
	{
		gel(G,k) = PicLC(J,gel(Q,piv[k]),B);
		gel(CG,k) = cgetg(d,t_VECSMALL);
		for(i=1;i<d;i++)
			gel(CG,k)[i] = itos(gcoeff(Q,i,piv[k]));
	}
	return gerepileupto(av,res);
}

GEN PicTorsGalRep_from_basis(GEN J, GEN J1, GEN l, GEN B)
{
	pari_sp av = avma;
	pari_timer WT,CPUT;
	GEN C,MFrob,MAuts,Z,AF,best,c,cbest;
	long e1,e2; /* Prec before and after lift */
	ulong ul,n,i,d;
	long sbest,s;
	int comp;
  if(DEBUGLEVEL)
  {
    walltimer_start(&WT);
    timer_start(&CPUT);
  }
	ul = itou(l);
	MFrob = gel(B,2);
	MAuts = gel(B,3);
	B = gel(B,1);
	d = lg(B)-1; /* dim */
	B = PicTors_FrobGen(J1,l,B,MFrob);
	//return gerepilecopy(av,tmp);
	C = gel(B,2);
	B = gel(B,1);
	n = lg(B); /* Number of generators */
	e1 = 1;
	e2 = Jgete(J);
	for(;;)
	{ /* Loop until accuracy high enough to get result */
		if(DEBUGLEVEL) pari_printf("pictorsgalrep: Hensel-lifting %lu %Ps-torsion points\n",n-1,l);
		/* TODO parallel version */
		for(i=1;i<n;i++)
			gel(B,i) = PicLiftTors(J,gel(B,i),l,e1);
		e1 = e2;
		if(DEBUGLEVEL)
		{
			timers_printf("pictorsgalrep","lift",&CPUT,&WT);
			printf("pictorsgalrep: Evaluating all points\n");
		}
		Z = PicTorsSpaceFrobEval(J,B,C,ul,MFrob,MAuts);
		if(DEBUGLEVEL)
		{
			timers_printf("pictorsgalrep","TorsSpaceEval",&CPUT,&WT);
			printf("pictorsgalrep: Getting polynomials\n");
		}
		AF = AllPols(J,Z,ul,MFrob);
		if(DEBUGLEVEL) timers_printf("pictorsgalrep","polynomials",&CPUT,&WT);
		if(lg(AF)>1) break; /* Success! */
		if(DEBUGLEVEL) pari_printf("pictorsgalrep: unable to determine representation at accuracy O(%Ps^%ld); doubling accuracy and retrying\n",Jgetp(J),Jgete(J));
		e2 *= 2;
		J = PicSetPrec(J,e2);
		if(DEBUGLEVEL) timers_printf("pictorsgalrep","JacLift",&CPUT,&WT);
	}
	n = lg(AF);
	best = gel(AF,1);
	sbest = gsizebyte(gel(best,1));
	cbest = Q_denom(gel(best,1));
	for(i=2;i<n;i++)
	{
		c = Q_denom(gmael(AF,i,1));
		comp = cmpii(c,cbest);
		s = gsizebyte(gmael(AF,i,1));
		if(comp<0 || (comp==0 && s<sbest))
		{
			best = gel(AF,i);
			cbest = c;
			sbest = s;
		}
	}
	return gerepilecopy(av,mkvecn(7,gel(best,1),l,utoi(d),gel(best,2),JgetT(J),Jgetp(J),JgetE(J)));
}

GEN PicTorsGalRep(GEN J, GEN l, GEN chi)
{
	pari_sp av = avma;
  pari_timer WT,CPUT;
	GEN J1,B,R;
	if(DEBUGLEVEL)
  {
    walltimer_start(&WT);
    timer_start(&CPUT);
  	pari_printf("pictorsgalrep: Getting basis of rep space over F_%Ps^%lu\n",Jgetp(J),degpol(JgetT(J)));
	}
	J1 = PicSetPrec(J,1);
	B = PicTorsBasis(J1,l,chi);
	if(DEBUGLEVEL) timers_printf("pictorsgalrep","basis",&CPUT,&WT);
	R = PicTorsGalRep_from_basis(J,J1,l,B);
	return gerepileupto(av,R);
}

GEN ProjGalRep_aux(GEN f, GEN Z, ulong l, ulong d, ulong ld, GEN T, GEN p, long e, GEN pe, ulong m)
{ /* Projectivisation of Gal rep */
  pari_sp av = avma;
  GEN z,done,PZ,PV,PF,Z2,U;
  ulong i,j,k,n;
  if(m>1)
  {
    U = pol_x(0);
    U = gpowgs(U,m);
    U = ZX_Z_mul(U,utoi(m+1));
    U = genrand(U);
    if(DEBUGLEVEL) pari_printf("ProjGalRep: Using U=%Ps\n",U);
  }
  else U = NULL;
  done = cgetg(ld,t_VECSMALL);
  PZ = cgetg(ld,t_VEC);
  PV = cgetg(ld,t_VEC);
	for(;;)
  { /* Increase accuracy until PF is identified */
  	for(i=1;i<ld;i++) done[i] = 0;
  	n = 0; /* Number of roots */
  	for(i=1;i<ld;i++)
  	{
    	if(done[i]) continue;
    	n++;
    	z = U ? FqX_eval(U,gel(Z,i),T,pe) : gel(Z,i);
    	for(k=2;k<l;k++)
    	{
      	j = mulOni(k,i,l,d);
      	done[j] = 1;
      	z = gadd(z, U ? FqX_eval(U,gel(Z,j),T,pe) : gel(Z,j));
    	}
    	gel(PZ,n) = z;
    	gel(PV,n) = i2c(i,l,d);
  	}
  	setlg(PZ,n+1);
  	/* Multiple roots ? TODO no need to recheck after increasing accuracy */
  	if(lg(gen_indexsort_uniq(PZ,(void*)&cmp_universal,&cmp_nodata))<lg(PZ))
  	{
    	avma = av;
    	return ProjGalRep_aux(f,Z,l,d,ld,T,p,e,pe,m+1);
  	}
  	setlg(PV,n+1);
    PF = PolExpID(PZ,T,pe);
    if(typ(PF)!=t_VEC)
      break;
    e <<= 1;
    if(DEBUGLEVEL) pari_printf("ProjGalRep: Increasing accuracy to O(%Ps^%ld)\n",p,e);
    Z2 = cgetg(ld,t_VEC);
    for(i=1;i<ld;i++)
    { /* TODO could parallelise this, but is that really useful? */
      /* NB in general, f has coeffs in Q, and roots not all distinxt mod p! */
			printf("Lifting root %ld\n",i);
      z = gel(Z,i);
      z = gadd(gmodulo(z,T),zeropadic(p,e));
      z = padicappr(f,z);
      for(j=1;j<lg(z);j++)
      {
        gel(z,j) = liftall(gel(z,j));
        if(gequal(FpX_red(gel(z,j),pe),gel(Z,i)))
        {
          gel(Z2,i) = gel(z,j);
          break;
        }
      }
    }
    pe = sqri(pe);
    Z = Z2;
  }
  return gerepilecopy(av,mkvecn(4,PF,PZ,PV,stoi(e)));
}

GEN ProjGalRep(GEN R)
{ /* Projectivisation of Gal rep */
	pari_sp av = avma;
	GEN f,Z,T,p,pe,L,D,res;
	ulong l,d,ld;
	long e;
	f = gel(R,1);
	f = primpart(f);
	L = gel(R,2);
	D = gel(R,3);
	Z = gel(R,4);
	T = gel(R,5);
	p = gel(R,6);
	e = itos(gel(R,7));
	pe = powis(p,e);
	l = itou(L);
	d = itou(D);
	ld = upowuu(l,d);
	res = ProjGalRep_aux(f,Z,l,d,ld,T,p,e,pe,1);
	return gerepilecopy(av,mkvecn(8,gel(res,1),L,D,gel(res,2),gel(res,3),T,p,gel(res,4)));
}

GEN HyperGalRep(GEN f, GEN l, GEN p, ulong e, GEN P, GEN chi, ulong force_a)
{
	/* Computes the Galois representation afforded by
   the piece of l-torsion of the Jacobian
   of the hyperelliptic curve C:y²=f(x)
   (in case f=[P,Q], the curve C:y²+Q(x)*y=P(x))
   on which Frob_p has charpoly chi
   (chi=0 means take all the l-torsion)
   by working at p-adic accuracy O(p^e).
   P must be a pair of points of C
   which are not conjugate under the hyperelliptic involution.
   If chi is nonzero,
   we must have chi || (Lp mod l)
   where Lp is the local L factor at p.*/
	pari_sp av = avma;
	GEN Lp, RRdata, J, R;
	ulong a;
	RRdata = HyperRRdata(f,P);
	Lp = hyperellcharpoly(gmodulo(f,p));
	a = force_a ? force_a : itou(gel(FpX_root_order_bound(Lp,l),2));
  J = PicInit(gel(RRdata,1),gel(RRdata,2),itou(gel(RRdata,3)),itou(gel(RRdata,4)),gel(RRdata,5),pol_x(1),p,a,e,Lp);
	R = PicTorsGalRep(J,l,chi);
	return gerepileupto(av,R);
}

GEN SuperGalRep(GEN f, ulong m, GEN l, GEN p, ulong e, GEN P, GEN chi, ulong force_a)
{
  /* Computes the Galois representation afforded by
   the piece of l-torsion of the Jacobian
   of the superelliptic curve C:y^m=f(x)
   on which Frob_p has charpoly chi
   (chi=0 means take all the l-torsion)
   by working at p-adic accuracy O(p^e).
   P must be a point of C.
   If chi is nonzero,
   we must have chi || (Lp mod l)
   where Lp is the local L factor at p.*/
  pari_sp av = avma;
  GEN RRdata, Lp, J, R;
  ulong a;
	RRdata = SuperRRdata(f,m,P);
  Lp = SuperZeta(f,m,itou(p));
  a = force_a ? force_a : itou(gel(FpX_root_order_bound(Lp,l),2));
  J = PicInit(gel(RRdata,1),gel(RRdata,2),itou(gel(RRdata,3)),itou(gel(RRdata,4)),gel(RRdata,5),pol_x(1),p,a,e,Lp);
  R = PicTorsGalRep(J,l,chi);
  return gerepileupto(av,R);
}

GEN SmoothGalRep(GEN f, GEN l, GEN p, ulong e, GEN P, GEN chi, ulong force_a)
{
  /* Computes the Galois representation afforded by
   the piece of l-torsion of the Jacobian
   of the smooth plane curve C:f(x,y)=0
   on which Frob_p has charpoly chi
   (chi=0 means take all the l-torsion)
   by working at p-adic accuracy O(p^e).
   P must be 
   If chi is nonzero,
   we must have chi || (Lp mod l)
   where Lp is the local L factor at p.*/
  pari_sp av = avma;
  GEN RRdata, Lp, J, R;
  ulong a;
	RRdata = SmoothRRdata(f,p,P);
	Lp = PlaneZeta(gel(RRdata,1),itou(p));
  a = force_a ? force_a : itou(gel(FpX_root_order_bound(Lp,l),2));
  J = PicInit(gel(RRdata,1),gel(RRdata,2),itou(gel(RRdata,3)),itou(gel(RRdata,4)),gel(RRdata,5),gen_1,p,a,e,Lp);
	R = PicTorsGalRep(J,l,chi);
  return gerepileupto(av,R);
}
