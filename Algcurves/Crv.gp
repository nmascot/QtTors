Pol2Support(f)=
{
  my(x,y,S,fi);
  [x,y] = variables(f);
  S = List();
  for(i=0,poldegree(f,x),
    fi = polcoef(f,i,x);
    for(j=0,poldegree(fi),
      if(polcoef(fi,j),listput(S,[i,j]))
    )
  );
  Vec(S);
}

APeqns(f,z=z)=
{ \\ Affine + Proj eqns
  my(v,d);
  v=variables(f);
  d=TotalDegree(f);
  if(#v==2,
		z = if(z,z,varlower("z",v[2]));
		return([f,PolHomogenise(f,z,d)])
	);
  [subst(f,v[3],1),f];
}

PlaneEval(f,P)=
{
  my(r);
  r = subst(f,x,P[1]);
  r = subst(r,y,P[2]);
  if(#P==3,r=subst(r,'z,P[3]));
  r;
}

PtIsOnCrv(f,P)=
{
	my(r,v,x,y,z);
	v = variables(f);
	if(#P==3,
		if(#v==3,
			[x,y,z]=v;
			r = subst(f,x,P[1]);
			r = subst(r,y,P[2]);
			r = subst(r,z,P[3]);
			return(r==0)
		);
		if(P[3]==0,
			return(PtIsOnCrv(APeqns(f)[2],P))
		);
		P = [P[1],P[2]]/P[3]
	); \\ Now #P=2
	if(#v==3,
		z = v[3];
		f = subst(f,z,1)
	); \\ Now #v=2
	[x,y] = v;
	r = subst(f,x,P[1]);
	r = subst(r,y,P[2]);
	r==0;
}

PtIsSing(f,P)=
{
  my(v=variables(f),fx,fy,fz);
  if(#P==3,
		if(#v==2,f=APeqns(f)[2];v=variables(f));
  	if(substvec(deriv(f,v[1]),v,P),return(0));
  	if(substvec(deriv(f,v[2]),v,P),return(0));
  	substvec(deriv(f,v[3]),v,P)==0;
	,
		if(#v==3,f=APeqns(f)[1];v=v[1..2]);
    if(substvec(deriv(f,v[1]),v,P),return(0));
    substvec(deriv(f,v[2]),v,P)==0;
	);
}

\\ Deprecated
PtsOO(F,a)=
{
	my(x,y,z,f,P);
	[x,y,z] = variables(F);
	f = subst(F,z,0);
	P = List();
	if(subst(f,y,0)==0,
		listput(P,[1,0,0])
	);
	f = subst(f,y,1);
	f = factor(f)[,1];
	for(i=1,#f,
		fi = f[i];
		if(poldegree(fi)==1,
			listput(P,[PolRoot1(fi),1,0])
		,
		  listput(P,[Mod(a,subst(fi,x,a)),1,0])
		)
	);
	Vec(P);
}

/* Struct Crv:
[[x,y,z,t,a],p,f,F,[SingPt,Branches],BranchesOO,g,W1,?]
W1=[[w],d], where the w/d*dx form basis of holo diffs
*/

CrvInit(f0,z=z,t=t,a=a)=
{
	my(f,F,lf,x,y,z,p,B,SB,D,faD,U,BU,P,g,W1,OC);
	[f,F]=APeqns(f0,z); \\ Affine and proj eqns
	[x,y,z] = variables(F);
	D = poldisc(f,y);
  if(D==0,error("Vanishing discriminant. Non-reduced curve?"));
  D = gcd(D,deriv(D)); \\ Only keep repeated factors, TODO legitimate?
	\\dx = poldegree(f,x);
	\\dy = poldegree(f,y);
	t = if(t,t,varlower("t",z));
	a = if(a,a,varlower("a",t));
	p = PlaneEval(f,[0,0]);
  p = if(type(p)=="t_INTMOD",p.mod,0); \\ Characteristic
	B = List();
	SB = List();
	\\ Branches above x=oo
	BU = BranchesAbove(f,0,p,x,t,a);
	if(BU==0,return(0)); \\ Unable to Puiseux because char p
	BU = apply(b->b[1..3],BU);
  for(i=1,#BU,
    P = BranchOrigin(BU[i][1]);
    if(PtIsSing(F,P), \\ Record sing branches for holo diffs
      listput(SB,[P,U,BU[i]])
    )
  );
	listput(B,[0,BU]); \\ Record branches
	\\ Branches above D(x)=0 TODO only repeated factors?
	lf = polcoef(f,poldegree(f,y),y);
  if(poldegree(lf), \\ Non-monic,
    D = lcm(D,lf/gcd(lf,deriv(lf))) \\ Ensure we catch branch above [0:1:0]
  );
	faD = factor(D);
	for(i=1,#faD~,
		U = faD[i,1];
		BU = BranchesAbove(f,subst(U,x,a),p,x,t,a);
		if(BU==0,return(0)); \\ Unable to Puiseux because char p
		BU = apply(b->b[1..3],BU);
		for(i=1,#BU,
			P = BranchOrigin(BU[i][1]);
			if(PtIsSing(F,P), \\ Record sing branches for holo diffs
				listput(SB,[P,U,BU[i][1..3]])
			)
		);
		listput(B,[U,BU]); \\ Record branches
	);
	B = Vec(B);
	SB = Vec(SB);
	[g,W1] = HolomorphicDifferentials(f,SB,a,t);
	OC = IntClosure(f,B[2..#B],x,y,t,a);
	[[f,F],p,[x,y,z,t,a],B,SB,g,W1,OC];
}

