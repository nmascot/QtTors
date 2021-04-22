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

GEN RgM_coef_mod(GEN A, GEN v)
{
  long N,i,j;
  N = lg(A)-1;
  i = umodsu(v[1],N);
  j = umodsu(v[2],N);
  return gcoeff(A,i?i:N,j?j:N);
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

GEN XH_decomp(ulong N, GEN H)
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
		if(DEBUGLEVEL>=3) printf("S2(Gamma0) has dim %lu\n",d);
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
        if(DEBUGLEVEL>=2) pari_printf("Dropping chi=%Ps because %lu not in Ker.\n",chi,H[j]);
        chi = NULL;
        break;
      }
    }
    if(chi==NULL) continue;
    gel(N2chi,3) = Gchi = mkvec2(G,chi);
    /*d = mfcuspdim(N,2,Gchi); */
    S = mfinit(N2chi,1);
    d = MF_get_dim(S);
		if(DEBUGLEVEL>=3) printf("dim %lu\n",d);
    if(d==0)
    {
      if(DEBUGLEVEL>=2) pari_printf("Dropping chi=%Ps because dim S2(chi)=0.\n",chi);
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

GEN LMod_worker(GEN p, GEN Gchi, GEN S, long t, GEN Z, GEN zo, GEN MZ)
{
	pari_sp av = avma;
	GEN epsp,L1,Tp,Xp,res;
	epsp = chareval(gel(Gchi,1),gel(Gchi,2),p,zo);
	L1 = mkpoln(3,gen_1,gneg(pol_x(1)),gmul(p,epsp)); /* x²-yx+p*eps(p)(t) */
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

GEN ModCrv_charpoly_multi(ulong N, GEN H, GEN Vecp)
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

GEN elladd_padic(GEN a4, GEN P, GEN Q, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma, av0;
  GEN P0,xP,yP,xQ,yQ,dx,dy,l,m,xR,yR,R;

  P0 = mkvec(gen_0); /* [0] */
  av0 = avma;
  if(gequal(P,P0))
  {
    avma = av;
    return Q;
  }
  if(gequal(Q,P0))
  {
    avma = av;
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
      avma = av0;
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

GEN FpEll_y2_from_Fqx(GEN a4, GEN a6, GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN y;
  y = Fq_sqr(x,T,p); // x²
  y = ZX_Z_add(y,a4); // x²+a4
  y = Fq_mul(y,x,T,p); // x³+a4*x
  y = ZX_Z_add(y,a6); // x³+a4*x+a6
  return gerepileupto(av,y);
}

ulong FpX_split_deg(GEN F, GEN p)
{ /* Smallest d s.t. all roots in GF(p^d), i.e. x^p^d = x mod F */
	pari_sp av = avma;
	GEN x,y;
	ulong i;
	x = pol_x(varn(F));
	y = FpX_Frobenius(F,p);
	for(i=1;!gequal(y,x);i++)
		y = Fq_pow(y,p,F,p);
	avma = av;
	return i;
}

GEN Fp_elldivpol_lv(GEN a4, GEN a6, ulong l, ulong v, GEN p)
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

ulong EllTorsIsSplit_lv(GEN a4, GEN a6, ulong l, ulong v, GEN p, ulong d, GEN T, GEN q2)
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
		avma = av;
		return 0;
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
				avma = av;
				return 0;
			}
		}
	}
	avma = av;
	printf("%lu^%lu->deg %lu\n",l,v,r);
	return r;
}

ulong EllTorsIsSplit(GEN a4, GEN a6, ulong N, GEN p, ulong d, GEN T, GEN q, GEN q2)
{ /* returns [Fp(E[N]/+-1):Fp] if E[N] defined over Fp^d, else returns 0 */
	pari_sp av = avma;
	GEN ap,chiE,nu,nud,NE,g,fa;
	ulong M,l,v,pl,i,r,c,nfa;
	ap = subii(addiu(p,1),Fp_ellcard(a4,a6,p));
  chiE = mkpoln(3,gen_1,negi(ap),p); /* x²-ap*x+p */
  nu = polsym(chiE,d);
  nud = gel(nu,d+1); /* alpha^d+beta^d */
  NE = subii(addiu(q,1),nud); /* #E(Fq) */
  if(umodiu(NE,N*N))
	{ /* Must have N² | #E(Fq) */
		printf("N2\n");
		avma = av;
		return 0;
	}
  g = subii(sqri(ap),muliu(p,4)); /* ap²-4p */
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
			avma = av;
			return 0;
		}
  }
  /* M = Cofactor supported by primes l such that Frobp ss on E[l] */
  if(M>1)
  {
    if(DEBUGLEVEL) printf("EllSplitTors: Checking whether Frob^%lu trivial on E[%lu].\n",d,M);
    if(umodiu(nud,M)!=(2%M))
    {
      if(DEBUGLEVEL) printf("EllSplitTors: Frob^%lu nontrivial on E[%lu].\n",d,M);
      avma = av;
			return 0;
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
		{
			avma = av;
			return 0;
		}
	printf("%lu^%lu: Had %lu, got %lu -> %lu\n",l,v,c,r,ulcm(c,r));
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
	printf("%lu^%lu: Had %lu, got %lu -> %lu\n",l,v,c,r,ulcm(c,r));
					c = ulcm(c,r);
					break;
				}
			}
		}
		else
		{
			r = EllTorsIsSplit_lv(a4,a6,l,v,p,d,T,q2);
   	 	if(r==0)
    	{
      	avma = av;
        return 0;
    	}
	printf("%lu^%lu: Had %lu, got %lu -> %lu\n",l,v,c,r,ulcm(c,r));
			c = ulcm(c,r);
		}
	}
	avma = av;
	return c;
}

GEN EllSplitTors(ulong N, GEN p, GEN T, GEN Badj)
{ /* Look for E/Fp such that E[N] def / Fp^d and j not in Badj */
	pari_sp av = avma;
	ulong d,nBad,i,r;
	GEN q,q2,a4,a6,D,j;
	d = degpol(T);
	if(Fl_powu(umodiu(p,N),d,N)!=1)
		pari_err(e_MISC,"Impossible by Weil pairing");
	nBad = lg(Badj);
	q = powiu(p,d);
	q2 = subiu(q,1);
	q2 = shifti(q2,-1);
	for(;;)
	{
		if(DEBUGLEVEL) printf("EllSplitTors: Trying new curve.\n");
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
				a4 = a6 = NULL;
				break;
			}
		}
		if(a4==NULL) continue;
		r = EllTorsIsSplit(a4,a6,N,p,d,T,q,q2);
		if(r==d)
			return gerepilecopy(av,mkvec2(a4,a6));
		if(DEBUGLEVEL)
		{
			if(r==0) printf("EllSplitTors: Unsuitable curve.\n");
			else printf("EllSplitTors: E[%lu]/-1 defined in degree %lu<%lu.\n",N,r,d);
		}
	}
}

GEN EllTorsBasis_lv(GEN a4, GEN a6, GEN A4, ulong l, ulong v, GEN T, GEN p, GEN D)
{ /* l,v -> Basis [P,Q] of E[l^v] over Fq, plus its Weil pairing, and mat of Frob */
	pari_sp av = avma;
	GEN lv1,lv,X,P,Q,x,z,z1,FP,FQ,M;
	ulong nX,iP,iQ;
	if(DEBUGLEVEL) printf("Getting basis of E[%lu^%lu]\n",l,v);
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

GEN ZqE_LiftTorsPt(GEN a4, GEN a6, GEN P, GEN D, GEN T, GEN pe, GEN p, long e)
{
	pari_sp av = avma;
	GEN x,y,y2;
	x = gel(P,1);
	y = gel(P,2);
	x = ZpX_ZpXQ_liftroot(D,x,T,p,e);
	y2 = FpEll_y2_from_Fqx(a4,a6,x,T,pe);
	y = ZpXQ_sqrtnlift(y2,gen_2,y,T,p,e);
	return gerepilecopy(av,mkvec2(x,y));
}

GEN EllWithTorsBasis(ulong N, GEN T, GEN pe, GEN p, long e, GEN Badj)
{ /* Find a4,a6 s.t. E[N] def/Fq and Fp(E[N]/-)=Fq. Returns a4,a6,P,Q,eN(P,Q),MFrob mod p^e. */
	pari_sp av = avma;
	GEN Fq1,a46,a4,a6,A4,P,Q,z,faN,M,D,B,Pi,Qi,zi;
	ulong nfaN,i,l,v,lv1,lv;
	a46 = EllSplitTors(N,p,T,Badj);
	a4 = gel(a46,1);
	a6 = gel(a46,2);
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
	return gerepilecopy(av,mkvecn(5,a46,P,Q,z,M));
}

GEN Ell_l2(GEN EN, GEN P, GEN Q, GEN T, GEN pe, GEN p, long e)
{
  P = RgM_coef_mod(EN,P);
  Q = RgM_coef_mod(EN,Q);
  return ZpXQ_div(ZX_sub(gel(Q,2),gel(P,2)),ZX_sub(gel(Q,1),gel(P,1)),T,pe,p,e);
}

GEN Ell_l1(GEN EN, GEN P, GEN Q, GEN T, GEN pe, GEN p, long e)
{
  pari_sp av = avma;
  ulong N,n;
  GEN S,nPQ;

  /* TODO methode Kamal addchain */
  printf("Into l1\n");
	N = lg(EN)-1;
	nPQ = gcopy(Q);
  S = Ell_l2(EN,P,nPQ,T,pe,p,e);
  for(n=1;n<N;n++)
  {
		nPQ[1] += P[1];
		nPQ[2] += P[2];
    S = ZX_add(S,Ell_l2(EN,P,nPQ,T,pe,p,e));
  }
  printf("Out of l1\n");
  return gerepileupto(av,S);
}

GEN EllMl1(GEN a4, ulong N, GEN P, GEN Q, ulong m, GEN T, GEN pe, GEN p, long e)
{
	pari_sp av = avma;
	GEN worker,done,E,EN,Ml1,params,v01,v10;
	ulong i,j,x,y;
	long pending,workid;
  struct pari_mt pt;
	E = stoi(e);
	/* Write down all N-torsion: : this is a naive level structure alpha : (Z/NZ)² ~ E[N] */
	EN = cgetg(N+1,t_MAT); /* [ m*i*P + j*Q ] */
	Ml1 = cgetg(N+1,t_MAT);
	for(j=1;j<=N;j++)
	{
		gel(EN,j) = cgetg(N+1,t_COL);
		gel(Ml1,j) = cgetg(N+1,t_COL);
	}
	gcoeff(EN,N,N) = gcoeff(Ml1,N,N) = gen_0;
	gcoeff(EN,m,N) = P;
	gcoeff(EN,N,1) = Q;
	/* Axes */
	for(x=2;x<N;x++)
	{
		gcoeff(EN,ZNnorm(m*x,N),N) = elladd_padic(a4,gcoeff(EN,ZNnorm(m*(x-1),N),N),P,T,pe,p,e);
		gcoeff(EN,N,x) = elladd_padic(a4,gcoeff(EN,N,x-1),Q,T,pe,p,e);
	}
	/* The rest */
	params = cgetg(8,t_VEC);
	gel(params,1) = a4;
	gel(params,4) = T;
	gel(params,5) = pe;
	gel(params,6) = p;
	gel(params,7) = E;
	worker = strtofunction("_elladd_padic");
  mt_queue_start_lim(&pt,worker,(N-1)*(N-1));
	pending = 0;
	for(x=1;x<N||pending;x++)
	{
		for(y=1;y<N;y++)
		{
			if(x<N)
			{
				gel(params,2) = gcoeff(EN,x,N);
				gel(params,3) = gcoeff(EN,N,y);
				printf("submitting add %lu %lu\n",x,y);
				mt_queue_submit(&pt,N*x+y,params);
			}
			else mt_queue_submit(&pt,N*x+y,NULL);
			done = mt_queue_get(&pt,&workid,&pending);
      if(done)
			{
				i = udivuu_rem(workid,N,&j);
				printf("got add %lu %lu\n",i,j);
				gcoeff(EN,i,j) = done;
			}
			if(x>=N) break;
		}
	}
	mt_queue_end(&pt);
	/* Ml1 */
	gel(params,1) = EN;
	v01 = mkvecsmall2(0,1);
	v10 = mkvecsmall2(1,0);
	worker = strtofunction("_Ell_l1");
  mt_queue_start_lim(&pt,worker,N*N-1);
	for(x=1;x<=N||pending;x++)
	{
		for(y=1;y<=N;y++)
		{
			if(x==N && y==N) continue;
			if(x<=N)
			{
				printf("submitting l1 %lu %lu\n",x,y);
				gel(params,2) = mkvecsmall2(x,y);
				gel(params,3) = y==N ? v01 : v10;
				mt_queue_submit(&pt,N*x+y,params);
			}
			else mt_queue_submit(&pt,N*x+y,NULL);
			done = mt_queue_get(&pt,&workid,&pending);
			if(done)
      {
        i = udivuu_rem(workid-1,N,&j);
				printf("got l1 %lu %lu\n",i,j+1);
        gcoeff(Ml1,i,j+1) = done;
      }
			if(x>N) break;
		}
	}
	mt_queue_end(&pt);
	return gerepilecopy(av,Ml1);
}

GEN GetMl1(ulong N, GEN Pts, GEN PtTags, GEN T, GEN p, long e, GEN zNpref, GEN Badj)
{
	pari_sp av = avma;
	GEN pe,E,a4,a6,P,Q,zN,M,Ml1,FP,PtsFrob;
	ulong m,nPts,i,a,b,c,d,x,y;
	pe = powis(p,e);
	E = EllWithTorsBasis(N,T,pe,p,e,Badj);
	a4 = gmael(E,1,1);
	a6 = gmael(E,1,2);
	P = gel(E,2);
	Q = gel(E,3);
	zN = gel(E,4);
	M = gel(E,5);
	pari_printf("E:y²+x³+%Psx+%Ps with accuracy O(%Ps^%ld) and residual degree %lu",a4,a6,p,e,degpol(T));
	/* Frob acts on E[N] by [a,c;b,d]
	 * => on pts, Frob([x,y]) = [x,y]*[a,b;c,d] = [a*x + c*y, b*x + d*y] */
	a = itou(gcoeff(M,1,1));
	b = itou(gcoeff(M,2,1));
	c = itou(gcoeff(M,1,2));
	d = itou(gcoeff(M,2,2));
	if(zNpref)
	{
		m = itou(Fq_log(zN,zNpref,utoi(N),T,p));
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
	return gerepilecopy(av,mkvecn(5,a4,a6,Ml1,PtsFrob,zN));
}
