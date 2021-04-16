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

GEN RGM_coef_mod(GEN A, GEN v)
{
  long N;
  long i,j;

  N = lg(A)-1;
  i = smodis(gel(v,1),N);
  j = smodis(gel(v,2),N);
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
