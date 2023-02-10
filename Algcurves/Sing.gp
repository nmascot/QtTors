\\ Deprecated
Sings(f0,a,p)=
{
	my(f,F,x,y,z,fx,fy,fz,D,faD,yD,A,DA,faDA,new,old,S=List(),P);
	[f,F] = if(type(f0)=="t_VEC",f0,APeqns(f0));
	[x,y,z] = variables(F);
	fx = deriv(f,x);
	fy = deriv(f,y);
	D = gcd([polresultant(fx,fy),polresultant(f,fx),polresultant(f,fy)]); \\ Finite sings have D(y)=0
	if(D==0,error("Vanishing discriminant. Non-reduced curve?"));
	if(poldegree(D),
		faD = factor(D);
		for(i=1,#faD~,
			D = subst(faD[i,1],y,a);
			if(poldegree(D)==1,
				yD = PolRoot1(D)
			,
				if(type(polcoef(D,0)) != "t_INTMOD" && poldegree(D)<=40,
					print("polredbest degree ",poldegree(D));
					[D,yD] = polredbest(D,1)
				,
					yD = Mod(a,D)
				)
			);
			if(poldegree(D)==0,next);
			DA = gcd(subst([f,fx,fy],y,yD)); \\ Finite sings with D(y)=0 have DA(x)=0
			if(poldegree(DA),
				faDA = factor(DA);
				for(j=1,#faDA~,
					[A,new,old] = AlgExtend(D,faDA[j,1],p);
					P = [new,subst(liftpol(yD),a,old),1]; \\ x,y guaranteeed to have same A
					if(poldegree(A)==1,P=liftpol(P));
					listput(S,P);
				)
			)
		)
	);
	fz = subst(deriv(F,z),z,0);
	f=subst(F,z,0);
	fx=deriv(f,x);
	fy=deriv(f,y);
	if(subst([fx,fy,fz],y,0)==0,
		listput(S,[1,0,0])
	);
	D = gcd(subst([fx,fy,fz],y,1));
	if(poldegree(D),
		faD = factor(D);
		for(i=1,#faD~,
			D = subst(faD[i,1],x,a);
			if(poldegree(D)==0,next);
			P = if(poldegree(D)>1,Mod(a,D),PolRoot1(D));
			listput(S,[P,1,0])
		)
	);
	Vec(S);
}

EqnLineJoin(P,Q)= \\ ax+by=c
{
	my([xP,yP]=P,[xQ,yQ]=Q,a,b,c,D);
	a = yP-yQ;
	b = xQ-xP;
	c = xP*yQ-yP*xQ;
	D = [a,b,-c];
	if(b<0,D=-D);
	D/content(D);
}

EqnLineEval(D,P)=D[1]*P[1]+D[2]*P[2]-D[3];

NewtonPolygon(f)=
{
	my(x,y,d,n,V,c,P,D,istart,iend);
	\\print("NewtonPoly ",f);
	[x,y] = variables(f);
	d = poldegree(f,y);
	V = List();
	for(i=0,d,
		c = polcoef(f,i,y);
		if(c==0,next);
		listput(V,[i,valuation(c,x)]);
	);
	V = Vec(V);
	\\print("Newtonpoly: vertices ",V);
	n = #V;
	P = List();
	D = EqnLineJoin(V[1],V[n]);
	istart = 1;
	iend = n;
	while(istart<iend,
		D = EqnLineJoin(V[istart],V[iend]);
		forstep(i=iend-1,istart+1,-1,
			if(EqnLineEval(D,V[i])<0,
				iend = i;
				D = EqnLineJoin(V[istart],V[iend]);
			);
		);
		listput(P,D);
		istart = iend;
		iend = n;
	);
	Vec(P);
}

/* Format branche retourné par Branches0:
A -> [B,e,G,aG]
où B def / G
aG = root of A in G
B = [P,Q,F] meaning
x = P(t), y = Q(t,z),
x = x0 + c*t^e + HOT (or x = c*t^-e + HOT if x0 = oo)
where z(0)=0 and F(t,z)=0 Newtonable

Plus tard, drop aG -> [[P,Q,F],e,G]
*/

Branches0(f,t,A,caract,flag)=
{ \\ Branches at x=0. Work over Q[a]/A. flag: only y(0)==0.
	my(branches=List(),x,y,a,dy,P,p,q,r,u,v,i0,j0,m,g,fag,G,B,b,aB,fB,c,d,rec,X,B1,b1,e,P1,Q1,F1);
	\\ Get Newton polygon
	[x,y] = variables(f);
	\\ f = sum_{i,j} a_{i,j} y^i x^j 
	a = variable(A);
	dy = poldegree(f,y);
	P = NewtonPolygon(f);
	for(iP=1,#P, \\ Loop over polygon
		[p,q,r] = P[iP]; \\ Segment pi+qj=r
		if(flag && p*q<=0, next);
		\\print("Branches0: segment ",[p,q,r]);
		\\ f = sum_{pi+qj=r} a_{i,j} y^i x^j + sum_{pi+qj>r} ... = f0 + HOT
		/*[u,v,] = gcdext(p,q); \\ pu+qv=1
		if(p>0 && v<0,
			u-=q; v += p;
		);
		print([[p,q],[u,v]]);*/
		\\[u,v,] = gcdext(-p,q);
		\\u = -u;
		\\[u,v,] = gcdext(-p,-q);
		\\u = -u;
		\\v = -v;
		\\print([[p,q],[u,v]]);
		[u,v,] = gcdext(p,q); \\ pu+qv=1
    /*while(p>0 && (u>0 || v<0),
      u-=q; v += p;
    );*/ \\ Try to arrange u<0, v>0
		\\print("Bezout for ",[p,q],": ",[u,v]);
		i0 = if(p,lift(Mod(r/p,q)),0); \\ Smallest i on pi+qj=r
		j0 = (r-p*i0)/q;
		m = floor((dy-i0)/q); \\ pi+qj=r, i0<=i<=dy <-> 0<=k<=m
		\\ f(b^-u*t^q,b^v*t^p) = t^r sum_{pi+qj=r} a_{i,j} b^k + HOT
		g = vector(m+1,k,polcoef(polcoef(f,j0-p*k+p,x),i0+k*q-q,y));
		g = polrecip(Pol(g)); \\ automatically drops extreme 0 terms
		if(caract && q>1,
      m = poldegree(g);
      if(m==1 && Mod(q,caract)==0,
        return(0); \\ Exception : Puiseux may not converge (TODO sure?) 
      )
    );
		fag = factor(g);
		\\print(liftall(g));
		\\print([p,q]);
		\\if(polcoef(g,poldegree(g)-1)==0 && abs(q)>1,print("A"));
		if(caract && q>1,
			m = poldegree(g);
			if(m==1 && Mod(q,caract)==0,
				print("Bad!");
				breakpoint();
			)
		);
		for(ig=1,#fag~, \\ Loop over factors
			G = fag[ig,1];
			\\print(G);
			[B,b,aB] = AlgExtend(A,G,caract); \\ Now work mod B(t), b(t) root of G, a=aB(t)
			\\print("Branches0: algext ",[A,G]," -> ",[B,b,aB]);
			fB = subst(liftpol(f),a,aB);
			\\print("b=",b);
			c = b^-u;
			d = b^v;
			\\ Change x=c*x^q, y=d*x^p*(1+y)
			fB = subst(subst(fB,x,c*x^q),y,d*x^p*(1+y))/x^r;
			if(poldegree(fB,x)==0,fB=x^0*y);
			if(polcoef(polcoef(fB,0,x),1,y), \\ Nonsingular?
				listput(branches,[[c*t^q,d*t^p*(1+y),subst(fB,x,t)],q,B,aB]);
			,
				rec = Branches0(fB,t,B,caract,1);
				if(rec==0,return(0));
				for(ir=1,#rec,
					[X,e,B1,b1] = rec[ir];
					[c,d,aB] = subst(liftpol([c,d,aB]),a,b1);
					[P1,Q1,F1] = X;
					X = [c*P1^q, d*P1^p*(1+Q1), F1];
					listput(branches,[X,e*q,B1,aB]);
				)
			)
		)
	);
  Vec(branches);
}

AlgContent(a)=
{
	my(X,c,n,v,fa,p);
	if(type(a)!="t_POLMOD",return(factor(a)));
	X = charpoly(a);
	v = variable(X);
	n = poldegree(X);
	c = denominator(content(X));
	X = subst(X,v,v/c)*c^n;
	fa = factor(content(x^n-X));
	for(i=1,#fa~,
		p = fa[i,1];
		v = valuation(polcoef(X,0),p)\n;
		for(j=1,n-1,
			Xj = polcoef(X,j);
			if(Xj==0,next);
			v = min(v,valuation(Xj,p)\(n-j));
		);
		fa[i,2] = v;
	);
	factor(factorback(fa)/c); \\ TODO avoid all these factos
}

BranchSimplify(B)=
{
	my(t,c,n,fac,v,B1);
	c = B[1][1]; \\ c*t^n;
	t = variable(c);
	n = poldegree(c);
	c = polcoef(c,n);
	fac = AlgContent(c);
	fac[,2] = round(fac[,2]/n);
	c = factorback(fac);
	B1 = subst(B[1],t,t/c);
	c = B1[3];
	B1[3] /= content(c,1);
	[B1,B[2],B[3]];
}

BranchesAbove(f,U,p,x,t,a)= \\ U(a), unless U=0
{
	my(fu,BU,u,U1,xB,AB);
	\\print(U);
	if(U==0,
		fu = polrecip(f);
  	BU = Branches0(fu,t,if(p,Mod(a,p),a),p,0);
		if(BU==0,return(0));
  	for(i=1,#BU,
    	BU[i][1][1] = 1/BU[i][1][1]; \\ Invert x
		)
	,
  	[u,U1] = RootRed(U); \\ Nice model
    fu = subst(f,x,x+u); \\ Shift x
    BU = Branches0(fu,t,U1,p,0); \\ All branches above U(x)=0
		if(BU==0,return(0));
    for(i=1,#BU,
      xB = subst(liftpol(u),a,BU[i][4])+BU[i][1][1]; \\ Shift x
			AB = BU[i][3]; \\ Field of def of branch
			if(poldegree(AB)>1, xB=Mod(xB,AB));
			BU[i][1][1] = xB;
		)
	);
	if(p==0,
		BU = apply(BranchSimplify,BU);
	);
	BU;
}

BranchExpand(B,e)=
{
	my([P,Q,f]=B,v,y,t,z,e1,df);
	v = variables(f);
	y = v[1];
	if(#v==1,
		return(subst([P,Q],y,0))
	);
	t = v[2];
	df = deriv(f,y);
	e1 = 1;
	z = O(t);
	while(e1<e,
		e1 *= 2;
		if(e1>e,e1=e);
		z = truncate(z)+O(t^e1);
		z -= subst(f,y,z)/subst(df,y,z);
	);
	subst([P,Q],y,z);
}

BranchCheck(f,B,e)=PlaneEval(f,BranchExpand(B[1],e));

BranchValuation(f,b,x,y)=
{
  my(e=2,xe,ye,p,t,f1,n1,d1,c,ne,de,vb,vn,vd);
	[xe,ye] = BranchExpand(b,e);
	t = variable(xe);
	vb = valuation(ye,t); \\ v(y)
	ye *= t^-vb;
	f1 = subst(f,x,xe);
	f1 = subst(f1,y,t^vb*y); \\ y = t^vb*y1
	\\ f1 in K(t)(y)
	n1 = numerator(f1);
	d1 = denominator(f1);
	c = content(n1,y);
	vn = valuation(c,t);
	n1 /= c;
	c = content(d1,y);
	vd = valuation(c,t);
	d1 /= c;
	\\ Now f(xt,t^vb*y1) = t^(vn-vd)*n(y1)/d(y1), where n,d in K[t][y]
  while(1,
		p = serprec(ye,t);
    ne = subst(n1,y,ye)+O(t^p);
    de = subst(d1,y,ye)+O(t^p);
    if(ne && de,return(valuation(ne,t)-valuation(de,t)+vn-vd));
    e *= 2;
		ye = t^-vb*(BranchExpand(b,e)[2]);
  );
}

BranchEval(f,b,e,x,y)=
{
	my(xe,ye,t,vb,f1,n1,d1,cn,cd,p,ne,de,k=1);
	if(type(f)=="t_VEC",
    return(apply(u->BranchEval(u,b,e,x,y),f))
  );
	[xe,ye] = BranchExpand(b,e);
  t = variable(xe);
  vb = valuation(ye,t); \\ v(y)
  ye *= t^-vb;
  f1 = subst(f,x,xe);
  f1 = subst(f1,y,t^vb*y); \\ y = t^vb*y1
  \\ f1 in K(t)(y)
  n1 = numerator(f1);
  d1 = denominator(f1);
  cn = content(n1,y);
  cd = content(d1,y);
	n1 /= cn; d1 /= cd;
  \\ Now f(xt,t^vb*y1) = (cn/cd)(t) * n(y1)/d(y1), where n,d in K[t][y]
  while(1,
    p = serprec(ye,t);
    de = subst(d1,y,ye)+O(t^p);
		if(de,break);
		e += k;
		k += 1;
		ye = t^-vb*BranchExpand(b,e)[2];
	);
	ne = subst(n1,y,ye)+O(t^p);
	(cn*ne)/(cd*de);
}

BranchOrigin(B)=
{
	my(e=1,t,b,m,X,Y,Z);
	t = variables(B[3])[2];
	while(1,
		e*=2;
		b = BranchExpand(B,e);
		if(b==0,next);
		[X,Y] = b; Z=1;
		m = vecmin([valuation(X,t),valuation(Y,t),0]);
		return(subst([X,Y,Z]/t^m,t,0));
	);
}

BranchesAt(f,F,p,P,a,t)=
{
  my(B=[],x,y,z,S,x1,y1,z1,A,f1,B1,n1,bi,ei,G,aG,xA,yA);
  [x,y,z] = variables(F);
  [x1,y1,z1] = P;
  if(type(x1)=="t_POLMOD",
    A = x1.mod; \\ y1 guaranteed to have same A
  ,
    A = if(p,Mod(a,p),a);
   );
   if(z1, \\ Finite case: shift
    x1/=z1; \\ Affine coords
    y1/=z1;
    f1 = subst(subst(f,y,y+y1),x,x+x1); \\ Shift
    B = Branches0(f1,t,A,p,1);
		if(B==0,return(0));
    for(i=1,#B,
      [bi,ei,G,aG] = B[i]; \\ bi=[P,Q,Phi]
      \\ Must change alg model
      xA = if(A,subst(liftpol(x1),a,aG),x1);
      yA = if(A,subst(liftpol(y1),a,aG),y1);
      bi[1] += xA; bi[2] += yA; \\ Shift
      B[i] = [bi,G,[xA,yA,1]]; \\ Branch, base field, Org in new model
    );
    return(B);
	);
  if(x1, \\ Case [1:b:0]
    f1 = subst(F,x,1); \\ Dehomogenise, vars y,z
    y1 /= x1; \\ Normalise: work at y=y1,z=0
    f1 = subst(subst(f1,y,y+y1),z,x); \\ Work at origin, in vars u=1/x,v=y/x-y1
    B = Branches0(f1,t,A,p,1);
		if(B==0,return(0));
    for(i=1,#B,
      [bi,ei,G,aG] = B[i]; \\ bi=[u=P,v=Q,Phi]
      \\ Must change alg model
      yA = if(A,subst(liftpol(y1),a,aG),y1);
      bi[1] = 1/bi[1]; \\ x=1/u
      bi[2] = (bi[2]+yA)*bi[1]; \\ y = (v+y1)*x
      B[i] = [bi,G,[1,yA,0]]; \\ Branch, base field, Org in new model
    );
	  return(B);
  );
  \\ Case [0:1:0] TODO that's the one forcing P(t,z) in branches
  f1 = subst(subst(F,y,1),z,y); \\ Dehomogenise, vars x,z meaning u=x/y, v=1/y. Work at origin
  B = Branches0(f1,t,A,p,1);
	if(B==0,return(0));
  for(i=1,#B,
    [bi,ei,G,aG] = B[i]; \\ bi=[u=P,v=Q,Phi]
    bi[2] = 1/bi[2]; \\ y=1/v
    bi[1] *= bi[2]; \\ x = u*y
    B[i] = [bi,G,[0,1,0]]; \\ Branch, base field, Org
  );
  B;
}
