#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_pic

/* Modular curves */

/* Z/NZ */

ulong ZNnorm(long x, ulong N)
{ /* Z/NZ <-> {1,..,N} */
  x = umodsu(x,N);
  return x?x:N;
}

ulong ZNneg(long x, ulong N)
{
  ulong y;
  y = umodsu(x,N);
  return y?N-y:N;
}

/*GEN RgM_Coef_mod(GEN A, GEN v)
{
  long N;
  long i,j;

  N = lg(A)-1;
  i = smodis(gel(v,1),N);
  j = smodis(gel(v,2),N);
  return gcoeff(A,i?i:N,j?j:N);
}*/

long zM_coef_mod(GEN A, GEN v)
{
  long N,i,j;
  N = lg(A)-1;
  i = umodsu(v[1],N);
  j = umodsu(v[2],N);
  return gel(A,j?j:N)[i?i:N];
}

GEN ZNXspan(GEN S, ulong N)
{ /* Span of S in (Z/NZ)* */
  pari_sp av = avma;
  GEN S1,H1,charf,H;
  ulong nS,s,n1,n,i,j,h;
  /* Trivial case */
  if(lg(S)==1)
    return mkvecsmall(1);
  nS = lg(S)-1;
  s = umodiu(gel(S,nS),N);
  S1 = gcopy(S);
  setlg(S1,nS); /* Drop last */
  H1 = ZNXspan(S1,N); /* Recurse */
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

ulong VecSmallFind(GEN V, long x)
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

GEN ZNX_Hlist(GEN S, ulong N)
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
		S1 = cgetg(nS+1,t_VEC); /* S and -1 */
		for(i=1;i<nS;i++)
			gel(S1,i) = gel(S,i);
		gel(S1,nS) = gen_m1;
		H = ZNXspan(S1,N);
		nH = lg(H);
	}
	H1 = cgetg(nH,t_VECSMALL);
	for(i=1;2*H[i]<=N;i++)
		H1[i] = H[i];
	setlg(H1,i);
	return gerepilecopy(av,mkvec2(H,H1));
}

/* GammaH(N) */

GEN SL2Zlift(GEN M)
{ /* Finds M' in SL2(Z), M'=M mod det(M)-1 */
	pari_sp av = avma;
	GEN SNF,U,V,D,a,b,ab,M2;
	SNF = matsnf0(M,1); /* U*M*V = D = diag(a,b), so det M = ab */
	U = gel(SNF,1);
	V = gel(SNF,2);
	D = gel(SNF,3);
	a = gcoeff(D,1,1);
	b = gcoeff(D,2,2);
	/* [a, ab-1; 1-ab, b+(1-ab)b] = [1,-1;1-b,b]*[1,0;1-a,1]*[1,b;0,1] in SL2(Z) */
	ab = mulii(a,b);
	M2 = cgetg(3,t_MAT);
	gel(M2,1) = cgetg(3,t_COL);
	gel(M2,2) = cgetg(3,t_COL);
	gcoeff(M2,1,1) = a;
	gcoeff(M2,1,2) = subiu(ab,1);
	gcoeff(M2,2,1) = negi(gcoeff(M2,1,2));
	gcoeff(M2,2,2) = mulii(b,addiu(gcoeff(M2,2,1),1));
	U = SL2_inv_shallow(U);
	V = SL2_inv_shallow(V);
	M2 = ZM_mul(U,M2);
	M2 = ZM_mul(M2,V);
	return gerepileupto(av,M2);
}

GEN Bot2SL2Z(GEN Bot, ulong n)
{ /* Finds [*,*;c';d'] in SL2(Z) with c~c', d~d' mod N */
	pari_sp av = avma;
	GEN N,c,d,u,v,g,M;
	N = utoi(n);
	c = stoi(Bot[1]);
	d = stoi(Bot[2]);
	g = bezout(c,d,&u,&v);
	M = cgetg(3,t_MAT); /* [vg^-1, -ug^-1; c,d ] */
  gel(M,1) = cgetg(3,t_COL);
  gel(M,2) = cgetg(3,t_COL);
	g = Fp_inv(g,N);
	gcoeff(M,1,1) = Fp_mul(v,g,N);
	gcoeff(M,1,2) = negi(Fp_mul(u,g,N));
	gcoeff(M,2,1) = c;
	gcoeff(M,2,2) = d;
	M = SL2Zlift(M);
	return gerepileupto(av,M);
}

/*GEN GammaHCuspData(GEN s, ulong N, GEN H, ulong* pwidth)
{  (c,d) -> [a,b;c,d],width 
	ulong c,g,a,w;
	GEN M;
	c = umodiu(,N);
	g = ugcd((c*c),N);
	g = N/g;
	M = Bot2SL2Z(s,N);
	a = umodiu(gcoeff(M,1,1),N);
	for(w=g;VecSmallFind(H,(1+a*c*w)%N)==0;w+=g) {}
	*pwidth = w;
	return M;
}*/

GEN ZNZ2primH(ulong N, GEN H)
{ /* Find all (u,v) s.t. gcd(u,v,N)=1 / H. Also returns maps for representatives */
	pari_sp av = avma;
	GEN A,tag;
	ulong nH,n,u,v,i,h;
	A = cgetg(N*N,t_VEC);
	n = 0;
	tag = cgetg(N,t_VEC);
	for(v=1;v<=N;v++)
	{
		gel(tag,v) = cgetg(N,t_VECSMALL);
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

GEN GammaHCusps(ulong N, GEN H)
{
	/* * Reps (c,d) of all cusps of GammaH
     * Galois orbits
     * Vector of indices of cusps such that there is M = [*,*;c,d] in SL(2,Z) such that f|M has rat coefs for all f def/Q
     * Matrices [*,*;c,d] in SL(2,Z), satifying above condition if possible
     * Galois orbits
     * Widths
     * Tags: (c',d') -> index of equivalent representative
  */
	pari_sp av = avma;
	ulong c,d,i,x,h,g,g2,w,nCusp,nH,nGalOrb,nOrb,nQqexp,N2,acg2;
	GEN Cusps,cd,CuspsGal,GalOrb,Qqexp,Mats,M,M1,Widths,tag;
	int Q;
	printf("Init\n");
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
	nOrb = nQqexp = 1;
	for(c=0;c<N;c++) /* c in Z/NZ */
	{
		printf("c=%lu\n",c);
		g = ugcd(c,N);
		g2 = N/ugcd(c*c,N);
		printf("g=%lu, g2=%lu\n",g,g2);
		GalOrb = cgetg(N+1,t_VEC); /* Two cusps are Galois-conj iff. they have the same c mod H */
		nGalOrb = 1;
		for(d=0;d<g;d++)
		{ /*d in (Z/cZ)* */
			printf("d=%lu\n",d);
			if(ugcd(d,g)>1) continue;
			if(gel(tag,d?d:N)[c?c:N]) continue;
			/* Record cusp */
			gel(Cusps,++nCusp) = cd = mkvecsmall2(c,d);
			pari_printf("Cusp %lu: %Ps\n",nCusp,cd);
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
			pari_printf("tags: %Ps\n",tag);
			M = Bot2SL2Z(cd,N); /* [a,b;c,d], the other choices are [1,i;0,1]*M */
			pari_printf("M=%Ps\n",M);
			/* Qqexp iff can choose t so that for all invertible x, ad(x-1)+1 in H */
			M1 = gcopy(M);
			for(i=0;i<N;i++)
			{
				Q = 1;
				for(x=2;x<N;x++)
				{
					if(ugcd(x,N)>1) continue;
					if((2*umodiu(gcoeff(M,2,1),N)*umodiu(gcoeff(M,2,2),N))%N)
					{
						Q = 0;
						break;
					}
					if((VecSmallFind(H,umodiu(gcoeff(M,1,1),N)*umodiu(gcoeff(M,2,2),N)*(x-1)+1)%N)==0)
					{
						Q = 0;
						break;
					}
				}
				if(Q) break;
				gcoeff(M,1,2) = addii(gcoeff(M,1,1),gcoeff(M,1,2));
				gcoeff(M,2,2) = addii(gcoeff(M,2,1),gcoeff(M,2,2));
			}
			if(Q)
			{
				printf("Q\n");
				Qqexp[nQqexp++] = nCusp;
				gel(Mats,nCusp) = M;
			}
			else gel(Mats,nCusp) = M1;
			/* Compute width: g2 * min w such that 1+acg2w in H */
			acg2 = umodiu(muliu(muliu(gcoeff(M,1,1),c),g2),N);
			for(w=1;VecSmallFind(H,(1+acg2*w)%N)==0;w++) {}
			Widths[nCusp] = g2*w;
			printf("Width %lu\n",g2*w);
		}
		if(nGalOrb>1)
		{ /* Record GalOrb if non-empty */
			setlg(GalOrb,nGalOrb);
			pari_printf("Orb %lu: %Ps\n",nOrb,GalOrb);
			gel(CuspsGal,nOrb++) = GalOrb;
		}
	}
	nCusp++;
	setlg(Cusps,nCusp);
	setlg(Mats,nCusp);
	setlg(Widths,nCusp);
	setlg(CuspsGal,nOrb);
	setlg(Qqexp,nQqexp);
	CuspsGal = gen_sort_shallow(CuspsGal,NULL,&sort_lg_rev);
	return gerepilecopy(av,mkvecn(6,Cusps,CuspsGal,Qqexp,Mats,Widths,tag));
}

GEN GammaHCusps_GalDiam_orbits(long y, GEN Cusps, GEN CuspsGal, GEN tags)
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

GEN GammaHmodN(ulong n, GEN H)
{ /* reps of GammaH(N) / Gamma(N) in SL2(Z) */
	pari_sp av = avma;
	ulong nH,h,x,j;
	GEN N,G,Mh;
	nH = lg(H)-1;
	G = cgetg(nH*n+1,t_VEC);
	N = utoi(n);
	j = 1;
	Mh = cgetg(3,t_MAT);
	gel(Mh,1) = cgetg(3,t_COL);
	gel(Mh,2) = cgetg(3,t_COL);
	for(h=1;h<=nH;h++)
	{
		gcoeff(Mh,1,1) = utoi(H[h]);
		gcoeff(Mh,2,2) = Fp_inv(gcoeff(Mh,1,1),N);
		gcoeff(Mh,1,2) = gcoeff(Mh,2,1) = gen_0;
		Mh = SL2Zlift(Mh);
		gel(G,j++) = gcopy(Mh);
		for(x=1;x<n;x++)
		{
			gcoeff(Mh,1,1) = addii(gcoeff(Mh,1,1),gcoeff(Mh,2,1));
      gcoeff(Mh,1,2) = addii(gcoeff(Mh,1,2),gcoeff(Mh,2,2));
			gel(G,j++) = gcopy(Mh);
		}
	}
	return gerepilecopy(av,G);
}
