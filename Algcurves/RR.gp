install("RgXY_RgX_div","GGL");

AlgLagrange(a,d,b)= \\ a,b in K[t]/T, [K(a):K]=d | deg T
{ \\ Attempts to express b as a poly in a
  my(T,n,v,M,aj=1);
  T = a.mod;
  n = poldegree(T);
  v = variable(T);
  M = matrix(n,d+1);
  for(j=1,d,
    for(i=1,n,
      M[i,j] = polcoef(aj,i-1,v)
    );
    aj = liftpol(aj*a)
  );
  b = liftpol(b);
  for(i=1,n,
    M[i,d+1] = polcoef(b,i-1,v)
  );
  M = matker(M);
  if(#M==0,
    []
  ,
    Polrev(M[1..d,1]/-M[d+1,1])
  );
}

PtEq(P,Q)=
{
  my(k,m,L);
	if(type(P[1])=="t_VEC" || type(Q[1])=="t_VEC",return(P==Q));
  if(#P==3,
    \\ P homog
    if(P[3],
      \\ P homog not at oo
      if(#Q==3,
        \\ P homog not at oo, Q homog
        if(Q[3],
          \\ P homog not at oo, Q homog not at oo -> Dehomogenise
          PtEq([P[1],P[2]]/P[3],[Q[1],Q[2]]/Q[3])
        ,
          \\ P homog not at oo, Q at oo
          0
        )
      ,
        \\ P homog not at oo, Q affine
        PtEq([P[1],P[2]]/P[3],Q)
      )
    ,
      \\ P at oo
      if(#Q==2,
        \\ P at oo, Q affine
        0
      ,
        \\ P at oo, Q homog
        if(Q[3],
          \\ P at oo, Q homog not at oo
          0
        ,  
          \\ P at oo, Q at oo
          if(P[2],
            \\ P at oo not y=0, Q at oo
            if(Q[2],
              \\ P at oo not y=0, Q at oo not y=0 -> check x/y 
              subst(minpoly(P[1]/P[2],'x),'x,Q[1]/Q[2])==0
            ,
              \\ P at oo not y=0 Q at oo y=0
              0
            )
          ,
            \\ P at oo y=0, Q at oo
            Q[2]==0
          )
        )
      )
    )    
  ,
    \\ P affine
    if(#Q==3,
      \\ P affine, Q homog
      PtEq(Q,P)
    ,
      \\ P,Q affine
      if(type(P[1])=="t_POLMOD",
        \\ P alg
        if(type(Q[1])=="t_POLMOD",
          \\ P,Q alg, now the fun starts TODO char p
          k = 0;
          while(1,
            m = minpoly(P[1]+k*P[2],'x);
            L = AlgLagrange(P[1]+k*P[2],poldegree(m),P[2]); \\ attempt to express yP as poly in xP + k yP
            if(L===[],k++;next);
            return(subst(m,'x,Q[1]+k*Q[2])==0 && subst(L,'x,Q[1]+k*Q[2])==Q[2])
          )
        ,
          \\ P alg, Q rat
          P == Q
        )
      ,
        \\ P rat
        P == Q
      )
    )
  );
}    
    

/* Format divisor: [.., [n,P], .. ] *
n integer, P either
regular point (affine or proj): [x,y], [x,y,z]
or
sing branch: [[k]] meaning sing branch k
or
TODO finite branch already found in D0
or TODO canonical divisor: [[0]]
*/

RRrecord0(D0,U,nP,P,B0,f,p,x,t,a)=
{ \\ D0 vec of [U,aU,BU,mU]
  my(aU,BU,mU,iU,eP);
  \\print("Recording U=",U);
  for(i=1,#D0,
    if(D0[i][1]==U,
      [U,aU,BU,mU] = D0[i];
      iU = i;
      \\print("Found at ",iU);
      break
    );
  );
  if(iU==0,
    \\print("Not found");
    \\ This U was not already in D0, so we'll add it
    aU = 0;
    \\ Do we already know the branches?
    for(i=1,#B0,
      if(B0[i][1]==U, \\ Yes
        BU = B0[i][2];
        break
      )
    );
    if(BU==0, \\ No, so compute them
      BU = BranchesAbove(f,subst(U,x,a),p,x,t,a);
      if(BU==0,error("Unable to handle this characterisitic"));
    );
    mU = vector(#BU);
    D0 = concat(D0,[[U,aU,BU,mU]]);
    iU = #D0;
  );
  \\ So now U is in D0
  \\print("Looking for P in BU");
  for(i=1,#BU, \\ Find P in BU (could be a reg pt or a branch)
    if( (type(P[1])!="t_VEC" && PtEq(BranchOrigin(BU[i][1]),P)) || (type(P[1])=="t_VEC" && BU[i][1]==P[1]),
      \\print("Found ",i);
      P = BU[i];
      mU[i] = nP; \\ Store mult
      break;
    )
  );
  eP = P[2];
  aU = max(aU,ceil(nP/eP)); \\ Update aU so aU*eP >= nP for all P above U
  D0[iU][2] = aU;
  D0[iU][4] = mU;
  \\print("End record");
  D0;
}

FindInBOO(BOO,b)=
{
	for(i=1,#BOO,
		if(BOO[i]==b,return(i));
	);
	error("Not found in BOO");
}

PtUB(P,F,B,B0,BOO,SB,lf)=
{ \\ P -> U,b,iOO. P can be coded in many different ways.
  my(tyP,U,b,BU,BP,lP,k1,k2,nOO=#BOO);
  tyP = type(P);
  if(tyP=="t_INT",
		[U,b] = SB[P][2..3]; \\ # of sing branch
		return([U,b,if(U,0,FindInBOO(BOO,b))]);
	);
  if(tyP=="t_VEC",
    lP = #P;
    if(lP==1,
      [k1,k2] = P[1]; \\ Branch in Crv structure. Meant to be used by auto Mak init only.
			U = B[k1][1];
			b = B[k1][2][k2];
		  return([U,b,if(U,0,k2)]);
    );
    if(lP==3 && type(P[1])=="t_VEC", \\ Raw branch, find it
      for(i=1,#SB,
        if(P==SB[i][3],
					[U,b] = SB[i][2..3];
		      return([U,b,if(U,0,FindInBOO(BOO,b))]);
				)
      );
      error("Unknown raw branch");
    );
    \\ P is a pt
    if(!PtIsOnCrv(F,P),error("Point ",P," is not on curve"));
    if(PtIsSing(F,P),error("Point ",P," is singular, specify branch number instead"));
    if(lP==2,
      P=[P[1],P[2],1]; \\ Homogenise
    );
    \\ Now P is a pt in homog coords
    if(P[3],
      \\ P is a finite pt
      U = minpoly(P[1]/P[3]);
      return([U,P[1..2]/P[3],0]);
    ,
      \\ P is at oo
      if(P[1],
        for(i=1,#BOO, \\ Find branch
          b = BOO[i];
          if(PtEq(BranchOrigin(b[1]),P),
            return([0,b,i]);
          )
        );
        error("Branch with origin ",P," not found");
      , \\ Annoying case: P=[0:1:0] -> don't know x
        \\ Look in finite branches first
        for(i=1,#B0,
          U = B0[i][1];
          if(Mod(lf,U),next); \\ Skip if U does not divide lf
          BU = B0[i][2];
          for(j=1,#BU,
            BP = BranchOrigin(BU[j][1]);
            if(BP[1]==0 && BP[3]==0, \\ Found
              return([U,BU[j],0]);
            )
          )
        );
        \\ Not found yet so it is at x=oo
        for(i=1,nOO,
          BP = BranchOrigin(BOO[i][1]);
          if(BP[1]==0 && BP[3]==0, \\ Found
            return([0,BOO[i],i]);
          )
        )
      );
    );
  );
  error("Point ",P," not understood");
}

RiemannRoch(C,D)=
{
  my(f,F,p,x,y,z,t,a,B,BOO,B0,SB,g,OC,OCden,dx,dy,mOO,D0,k,nP,P,U,BP,iOO,den,m0,aU,BU,mU,dden,dOO,mOO2,l,V,N,L,M,K,nOO,dOC,lf);
  if(type(D)=="t_VEC",
    D = Mat(D)
  );
  f = C[1];
  [f,F] = f;
  p = C[2];
  [x,y,z,t,a] = C[3];
  B = C[4]; \\ All branches
  BOO = B[1][2]; \\ All above x=oo
  nOO = #BOO;
  B0 = B[2..#B]; \\ All the others
  SB = C[5]; \\ All singular branches
  g = C[6];
  OC = C[8]; \\ Int closure
  [OC,OCden] = OC;
  dOC = poldegree(OCden);
  dx = poldegree(f,x);
  dy = poldegree(f,y);
  lf = polcoef(f,dy,y);
	\\ Begin parse D
  mOO = vector(nOO); \\ Multiplicities of D at brnaches at OO
  D0 = []; \\ Finite part of D
  for(i=1,#D~,
    [P,nP] = D[i,];
    [U,BP,iOO] = PtUB(P,F,B,B0,BOO,SB,lf); \\ Analyse P
		if(U,
			D0 = RRrecord0(D0,U,nP,BP,B0,f,p,x,t,a);
		,
			mOO[iOO] = nP;
		)
	);
  \\ D parsed. Compute den(x) so that den*L contained in OC; 
	\\ then adjust mOO and adjust and convert D0 into m0.
  den = 1;
  m0 = List();
  for(i=1,#D0,
    [U,aU,BU,mU] = D0[i];
    den *= U^aU;
    for(j=1,#BU,
      listput(m0,[mU[j]-aU*BU[j][2],BU[j]])
    )
  );
  m0 = Vec(m0);
  dden = poldegree(den);
  dOO = 0; \\ deg mOO
  for(i=1,nOO,
    mOO[i] += BOO[i][2] * dden;
    dOO += mOO[i] * poldegree(BOO[i][3]);
  );
  \\ Now inflate mOO by adding l*(x)_oo to D_oo (l=0,1,2,...) so dOO > 2g-2 -> dim RR predictable
  mOO2 = mOO;
  l = 0;
  if(dOO <= 2*g-2,
    l = ceil((2*g-1-dOO)/dy);
    mOO2 = vector(nOO,i,mOO[i]+l*BOO[i][2])
  );
  V = matrix(nOO,dy,i,j,ceil((BranchValuation(OC[j],BOO[i][1],x,y)+mOO2[i])/BOO[i][2])+dOC);
	\\ L in OC = sum_j K[x]*OC[j]
  N = vector(dy,j,vecmax(V[,j])); \\ Guess bounds on required powers of x for each j
  while(1, \\ Loop until powers of x are enough to recover full space
		\\print("Loop");
		\\print(N);
    L = List(); \\ List the x^i*OC[j]; hopefully they span a space containing L
    for(j=1,dy,
      for(i=0,N[j],
        listput(L,x^i*OC[j])
      )
    );
    L = Vec(L);
		\\ Get those with poles at x=oo no worse than mOO2
    M = vector(nOO,i,PolarBranchMat(L,OCden,BOO[i],-mOO2[i],x,y,t,a)); 
    K = matker(matconcat(M~));
    \\print("Got ",#K," expected ",dOO+l*dy+1-g);
    if(#K==dOO+l*dy+1-g,break);
    N = apply(n->n+dOO+l*dy+1-g-#K,N);
  );
  L = L*K;
  \\ Now enforce m0
  if(l,m0=concat(m0,vector(nOO,i,[mOO[i],BOO[i]])));
  if(#m0,
    M = vector(#m0,i,PolarBranchMat(L,OCden,m0[i][2],-m0[i][1],x,y,t,a));
    K = matker(matconcat(M~));
    L = L*K;
  );
  den *= OCden;
  L = apply(l->RgXY_RgX_div(l,den,dy),L);
	apply(l->l/content(l,1),L);
}

FonOC(C,f)=
{
  my(v,x,y,d,OC,Df,DO,F,c);
  v = C[3];
  x = v[1];
  y = v[2];
  d = poldegree(C[1][1],y);
  Df = denominator(f,x);
  f *= Df;
  OC = C[8];
  DO = OC[2];
  OC = OC[1];
  F = vector(d);
  forstep(i=d-1,0,-1,
    c = polcoef(f,i,y)/polcoef(OC[i+1],i,y);
    f -= c*OC[i+1];
    F[i+1] = c
  );
  F * (DO/Df);
}

FnNormalise(f,F,x,t)=subst(lift(Mod(subst(f,x,t),subst(F,x,t))),t,x); \\ put in K(x)[y]

FnDiv(C,f,Print)=
{
  my(p,x,y,z,t,a,SB,nSB,Of,Df,Nf,R,fa,D,U,BU,b,v,P,DNf);
  p = C[2];
  [x,y,z,t,a] = C[3];
  SB = C[4];
  nSB=#SB;
  f = FnNormalise(f,C[1][1],x,t);
  Of = FonOC(C,f);
  Df = denominator(content(Of,x));
  if(p, Df = Mod(Df,p));
  Nf = f*Df; \\ f = Nf(x,y) / Df(x), Nf has no finite poles
  DNf = denominator(Nf,x);
  Nf *= DNf;
  Df *= DNf;
  R = polresultant(C[1][1],Nf,y); \\ Any zeroes of f have x = a root of this
  fa = Vec(Set(concat(factor(R)[,1],factor(Df)[,1]))); \\ Interesting finite places
  D = List();
  for(i=1,#fa+1,
    U = if(i>#fa,0,fa[i]); \\ Try all these values of x, and then x=oo
    BU = 0;
    for(i=1,nSB, \\ Do we already know the branches for this value of x?
      if(SB[i][1]==U,
        BU = SB[i][2]; \\ Found
        break
      )
    );
    if(BU==0, \\ Not found, calculate them
      BU = BranchesAbove(C[1][1],subst(U,x,a),p,x,t,a);
      if(BU==0,error("Unable to handle this characterisitic"));
    );
    for(j=1,#BU, \\ Check valuation at all these branches
      b = BU[j];
      v = BranchValuation(f,b[1],x,y);
      if(v,
        P = BranchOrigin(b[1]);
        if(PtIsSing(C[1][2],P), \\ If P is singular, store it as a branch
          listput(D,[b[1..3],v])
        ,
          listput(D,[P,v])
        )
      )
    )
  );
  D = matconcat(vecsort(Vec(D),2,4)~); \\ Sort by multiplicities
  if(Print,
    DivPrint(D)
  ,
    D
  );
}

dxDiv(C,Print)=
{ \\ Divisor of dx
  my(f,p,x,y,z,t,a,SB,nSB,fa,D,U,BU,b,v,P);
  f = C[1][1];
  p = C[2];
  [x,y,z,t,a] = C[3];
  SB = C[4];
  nSB=#SB;
  fa = factor(if(p,poldisc(f,y),ZXY_disc(f,2)))[,1]; \\ Interesting finite places
  D = List();
  for(i=0,#fa,
    U = if(i,fa[i],0);
    BU = 0;
    for(i=1,nSB,
      if(SB[i][1]==U,
        BU = SB[i][2];
        break
      )
    );
    if(BU==0,
      BU = BranchesAbove(C[1][1],subst(U,x,a),p,x,t,a);
      if(BU==0,error("Unable to handle this characteristic"));
    );
    for(j=1,#BU,
      b = BU[j];
      v = b[2];
			v = if(U,v-1,-v-1);
      if(v,
        P = BranchOrigin(b[1]);
        if(PtIsSing(C[1][2],P),
          listput(D,[b[1..3],v])
        ,
          listput(D,[P,v])
        )
      )
    )
  );
  D = matconcat(vecsort(Vec(D),2,4)~);
  if(Print,
    DivPrint(D)
  ,
    D
  );
}

DiffDiv(C,f,Print)=
{
  my(D,D1,D2);
  D1 = FnDiv(C,f,0);
  D2 = dxDiv(C,0);
  D = BDivAdd(D1,D2);
  if(Print,
    DivPrint(D)
  ,
    D
  );
}

PtDeg(P)=
{
  my(x,y,a);
  if(type(P[1])=="t_VEC",
    poldegree(P[3]) \\ Branch
  ,
    x = P[1];
    y = P[2];
    if(#P==3,
      if(P[3],
        x /= P[3];
        y /= P[3];
      )
    );
    x = liftint(x);
    y = liftint(y);
    if(type(x)=="t_POLMOD",return(poldegree(x.mod)));
    if(type(y)=="t_POLMOD",return(poldegree(y.mod)));
    1
  );
}
    
PtSimplify(P,T,p,k)=
{ \\ P on Fp[t]/T actually def in deg k
	my(S,u,v);
	if(k==1,return(subst(liftpol(P),variable(T),0)));
	if(k==poldegree(T),return(P));
	S = ffinit(p,k,variable(T));
	u = polrootsmod(minpoly(P[1]),[S,p])[1];
	v = polrootsmod(minpoly(P[2]),[S,p]);
	for(i=1,#v,
		if(PtEq(P,[u,v[i]]),return([u,v[i]]))
	);
	error("Bug in PtSimplify");
}

DivDeg(D)=sum(i=1,#D~,D[i,2]*PtDeg(D[i,1]));
