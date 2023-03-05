FnIsConst(f)=
{
	my(t);
	t = type(simplify(f));
	if(t=="t_INT",return(1));
	if(t=="t_FRAC",return(1));
	if(t=="t_POLMOD",return(1));
	0;
}

Pt2Branch(C,P)=
{
	my(f,F,p,x,y,z,t,a,B);
	[f,F] = C[1];
  p = C[2];
  [x,y,z,t,a] = C[3];
	if(type(P)=="t_VEC",
    if(!PtIsOnCrv(F,P),
      error("This point is not on this curve")
    );
    if(PtIsSing(F,P),
      error("This point is singular, specify branch number instead")
    );
    if(#P==2,
      P=[P[1],P[2],1]
    );
    B = BranchesAt(f,F,p,P,a,t)[1];
		if(B==0,error("Unable to compute branch in this characteristic"));
		B;
  ,
    C[5][P][3]
  );
}

Branch2Pt(C,B)=
{
	my(S=C[5]);
	if(type(B[1])!="t_VEC",return(B)); \\ Already a pt
	for(i=1,#S, \\ Look for B in sing branches
		if(S[i][3]==B,return(i))
	); \\ If not found, then pt is reg
	BranchOrigin(B[1]);
}

CrvFindRatPt(C,M=10)=
{
	my(C4=C[4],U,B,P);
	for(i=1,#C4,
    [U,B] = C4[i];
    if(poldegree(U)>1,next);
    for(j=1,#B,
      if(poldegree(B[j][3])==1,return(Branch2Pt(C,B[j])))
    )
  );
	for(z=0,M,
		for(x=-M,M,
			for(y=-M,M,
				P=[x,y,z];
				if(content(P)!=1,next);
				if(!PtIsOnCrv(C,P),next);
				if(!PtIsSing(C,P),return(P));
			)
		)
	);
	[];
}

CrvRatAux(f,N,D,x,y,t)=
{
	my(n,g,L,u,m,R,L1,u1,R1,L2,u2,R2,L3,u3,R3,A,B,e,a,b,c,d,M);
	n = poldegree(f,x);
	g = t*D-N;
	L = vector(3);
	u = -1;
	m = 0;
	while(m<3,
		R = polresultant(subst(f,y,u),subst(g,y,u),x);
		if(poldegree(R,t)==n,
			m++;
			L[m] = [u,R];
		);
		u++
	);
	[L1,L2,L3] = Vec(L);
	[u1,R1] = L1;
	[u2,R2] = L2;
	[u3,R3] = L3;
	A = (-u1*R2+u3*R2);
  B = (u2*R1-u3*R1);
	\\ Want c s.t. A*c+B = R3*cst -> Compare 2 coefs of A,B,R3.
	v = min(valuation(A,t),valuation(R3,t));
	e2 = v+1;
	e = v+2;
	for(j=1,+oo,
		a = A + O(t^e);
		b = B + O(t^e);
		c = R3 + O(t^e);
		M = matrix(2,2);
		M[1,1] = polcoef(a,v);
		M[1,2] = polcoef(c,v);
		for(i=e2,e-1,
			M[2,1] = polcoef(a,i);
			M[2,2] = polcoef(c,i);
			d = matdet(M);
			if(d,
				c = (polcoef(c,v)*polcoef(b,i) - polcoef(c,i)*polcoef(b,v))/d;
				return((-u1*c*R2+u2*R1)/(R1-c*R2));
			)
		);
		e2 = e;
		e += j;
	);
}

CrvRat(C,P,Q)=
{
	my(f,F,L,T,N,D,X,Y,x,y,z,t,a);
  [f,F] = C[1];
	[x,y,z,t,a] = C[3];
	if(P==0,
		error("Please specify a rational point or branch")
	);
	if(type(P)=="t_VEC",
		if(!PtIsOnCrv(F,P),
    	error("This point is not on this curve")
  	);
  	if(PtIsSing(F,P),
    	error("This point is singular, specify branch number instead")
  	)
	);
	if(Q,
		if(type(Q)=="t_VEC",
    	if(!PtIsOnCrv(F,Q),
      	error("This point is not on this curve")
    	);
    	if(PtIsSing(F,Q),
      	error("This point is singular, specify branch number instead")
    	);
		);
		D = [P,1;Q,-1]
	,
		D = [P,1]
	);
	L = RiemannRoch(C,D);
	T = select(f->!FnIsConst(f),L)[1];
	D = denominator(T);
	N = numerator(T);
	X = CrvRatAux(f,N,D,y,x,t);
	Y = CrvRatAux(f,N,D,x,y,t);
	[[X,Y],T];
}

FnsBranchMatRat(F0,B,e0,x,y)=
{
	my(A,a,t,d,n,F,m,M,S,c,e=e0);
	A = B[3];
	a = variable(A);
	d = poldegree(A);
	n = #F0;
	while(1,
		F = BranchEval(F0,B[1],e,x,y);
		t = variable(F);
		m = valuation(F,t);
		M = serprec(F,t);
		if(M==+oo,M=e+m);
		if(M-m>=e0,break);
		e += e0-(M-m)+1;
	);
	S = matrix((M-m)*d,n);
	for(j=1,n,
		for(i=m,M-1,
			c = liftpol(polcoef(F[j],i));
			for(k=0,d-1,
				S[d*(i-m)+k+1,j] = polcoef(c,k,a)
			)
		)
	);
	S;
}

FnsBranchMatRat_conic(u,v,B,e,x,y)=
{
  my(A,a,t,d,F,m,M,S,c);
  A = B[3];
  a = variable(A);
  d = poldegree(A);
  [u,v] = BranchEval([u,v],B[1],e,x,y);
	F = [u^2,u*v,v^2,u,v];
  t = variable(F);
  m = min(0,valuation(F,t));
  M = serprec(F,t);
  if(M==+oo,M=e+m);
  S = matrix((M-m)*d,6);
  for(j=1,5,
    for(i=m,M-1,
      c = liftpol(polcoef(F[j],i));
      for(k=0,d-1,
        S[d*(i-m)+k+1,j] = polcoef(c,k,a)
      )
    )
  );
	if(m<=0 && M>=1,S[-m*d+1,6] = 1);
  S;
}

FnsBranchMat(F0,B,e0,x,y)=
{
  my(t,n,F,m,M,S,e=e0);
  n = #F0;
	while(1,
  	F = substvec(F0,[x,y],BranchExpand(B[1],e));
  	t = variable(F);
		m = valuation(F,t);
  	M = serprec(F,t);
		if(e>=20,breakpoint());
		if(M-m>=e0,break);
		e += e0-(M-m)+1;
	);
  S = matrix((M-m),n);
  for(j=1,n,
    for(i=m,M-1,
       S[i-m+1,j] = polcoef(F[j],i)
    )
  );
  S;
}

DiffsBranchMat(W,den,B,e0,x,y)=
{
  my(k=1,b,D,t,n,m,M,S,Wb,e=e0);
	n = #W;
	while(1,
		b = BranchExpand(B[1],e);
		D = substvec(den,[x,y],b);
		if(D==0,
			e += k;
			k += 1;
			next
		);
		Wb = substvec(W,[x,y],b)*deriv(b[1])/D;
    t = variable(Wb);
    m = valuation(Wb,t);
    M = serprec(Wb,t);
    if(M==+oo,M=e+m);
    if(M-m>=e0,break);
    e += e0-(M-m)+1;
  );
  S = matrix((M-m),n);
  for(j=1,n,
    for(i=m,M-1,
       S[i-m+1,j] = polcoef(Wb[j],i)
    )
  );
  S;
}

CrvEll(C,P)=
{
	my(ID=[],f=C[1][1],p=C[2],x,y,z,B,L,LB,L3,L2,LB2,X,Y,XY,e,K,E,U);
	[x,y,z] = C[3][1..3];
	if(C[6]!=1,
			error("This curve does not have genus 1")
	);
	if(P===0,
		P = CrvFindRatPt(C);
		if(P==[],error("Please specify a rational point (could not find any)"));
	);
	B = Pt2Branch(C,P);
	L = RiemannRoch(C,[P,3]); \\ L(3*P)
	LB = substvec(L,[x,y],BranchExpand(B[1],2));
	L3 = apply(s->polcoef(s,-3,t),LB); \\ Coef of t^-3 in L(3*P)
	L3 = matker(Mat(L3)); \\ combis that are O(t^-2)
	L2 = L*L3; \\ L(2*P)
	LB2 = LB*L3; \\ their t-exps
	X = L2[select(f->valuation(f,t)==-2,LB2,1)[1]];
	Y = L[select(f->valuation(f,t)==-3,LB,1)[1]];
	XY = [X,Y];
	L = [1,X,Y,X^2,X*Y,X^3,Y^2];
	e = 7;
	while(1,
		K = matker(FnsBranchMat(L,B,e,x,y));
		if(#K==1,break);
		e *=2
	);
	K = K[,1];
	XY *= -K[6]/K[7];
	E = ellinit([K[5]/K[7],-K[4]/K[7],-K[3]*K[6]/K[7]^2,K[2]*K[6]/K[7]^2,-K[1]*K[6]^2/K[7]^3]);
	if(p==0,
		E = ellminimalmodel(E,&U);
		XY = ellchangepoint(XY,U);
		ID = ellidentify(E);
		if(#ID,ID=ID[1];ID=[ID[1],apply(P->PtPullback(C,XY,P),ID[3])]);
	);
	XY = apply(s->FnNormalise(s,f,x,z),XY);
	[E,ID,XY];
}

FnsRel(L,F,B,vars)=
{
	my([x,y,z,t,a]=vars,n=#L,e,M,K,N,m);
	e = n+2;
	while(1,
		M = FnsBranchMatRat(L,B,e,x,y);
    K = matker(M);
		N = FnNormalise(L*K,F,x,t);
		m = #select(s->s,N);
		if(m==0,return(K));
		e += m+1;
	);
}

CrvIsHyperell(C)=
{
	my(W=C[7][1],g,W2,g2,k=1,K);
	g = C[6];
	g2 = (g*(g+1))/2;
	W2 = vector(g2);
	for(i=1,g,
		for(j=1,i,
			W2[k] = W[i]*W[j];
			k++
		)
	);
	K = FnsRel(W2,C[1][1],C[4][1][2][1],C[3]);
	g2-#K == 2*g-1;
}

CrvHyperell_sub(b,u,v,n,vars,p)=
{ \\ deg u = 2; not guaranteed that K(u,v) = K(C)
	\\ TODO char 2
	my(x,y,z,t,a,d,e,nd,uB,vB,m,o,M,ui,uv,K,A,B,C,D,R,S,c,num,g1,U,M1,H);
	[x,y,z,t,a] = vars;
	d = poldegree(b[2],a); \\ Degree of branch
	b = b[1];
	e = ceil(3*(n+1)/d)+1;
	uB = BranchEval(u,b,2,x,y);
	vB = BranchEval(v,b,2,x,y);
	m = 0;
	if((o = valuation(uB,t)) < 0,
		m += (n+1)*o
	);
	if((o = valuation(vB,t)) < 0,
    m += 2*o
  );
	nd = ceil(n/d);
	e = 4*(nd-m)+1;
	uB = BranchEval(u,b,e,x,y);
  vB = BranchEval(v,b,e,x,y);
	M = matrix(d*(4*nd+-m+1),3*n+3);
	ui = 1;
	for(i=0,n,
		uv = ui;
		for(k=0,4*nd-m,c = liftpol(polcoef(uv,m+k-1,t));for(l=0,d-1,M[d*k+l+1,1+i]=polcoef(c,l,a)));
		uv *= vB;
		for(k=0,4*nd-m,c = liftpol(polcoef(uv,m+k-1,t));for(l=0,d-1,M[d*k+l+1,n+2+i]=polcoef(c,l,a)));
		uv *= vB;
		for(k=0,4*nd-m,c = liftpol(polcoef(uv,m+k-1,t));for(l=0,d-1,M[d*k+l+1,2*n+3+i]=polcoef(c,l,a)));
		ui *= uB
	);
	K = matker(M)[,1];
	C = Polrev(K[1..n+1],x);
	B = Polrev(K[n+2..2*n+2],x);
	A = Polrev(K[2*n+3..3*n+3],x); \\ A(u)*v^2+B(u)*v+C(u)=0
	if(p==2,error("Characteristic 2 not implemented"));
	if(A==0,return(0)); \\ v in K(u)
	D = B^2-4*A*C;
	if(D==0,return(0)); \\ v in K(u)
	\\ Now v not in K(u), so K(u,v) = K(C) and it's going to work
	S = factor(D); \\ TODO make sqfree
	S[,2] = apply(x->x\2,S[,2]);
	S = factorback(S);
	R = D/S^2;
	A = subst(A,x,u);
	B = subst(B,x,u);
	S = subst(S,x,u);
	v = (2*A*v+B)/S; \\ Now v^2=R(u)
	if(p==0, \\ Minimise model
		\\ First, make integral, and get rid of some content
		c = content(R);
		num = numerator(c);
		d = denominator(c);
		\\ v^2 = R(u), R = n/d*R1, n=n1*n2^2, d=d1*d2^2
		num /= core(num); \\ n2^2
		R /= num; \\ n1/d*R1
		v /= sqrtint(num); \\ (v/n2)^2 = n1/d*R1(u)
		d *= core(d); \\ (d1*d2)^2
		R *= d;
    v *= sqrtint(d); \\ (d1*d2*v/n2)^2 = n1*d1*R1(u)
		\\ Now, let PARI take over :)
		g1 = (poldegree(R)+1)\2; \\ g+1
		R = hyperellminimalmodel(R,&U);
		[e,M,H] = U;
		M1 = M^(-1);
		u = (M1[1,1]*u+M1[1,2])/(M1[2,1]*u+M1[2,2]);
		v = ((M[2,1]*u+M[2,2])^g1*v-subst(H,x,u))/e;
	,
		R=[R,0]; \\ Mod p case; need long format for below
	);
	if(R[2]==0,
		R=R[1]; \\ R=[P,Q]; if Q==0, drop Q
		d = poldegree(R);
		if(d%2==0, \\ Look for integral roots
			fa = factor(R)[,1];
			fa = select(f->poldegree(f)==1 && polcoef(f,1)==1,fa);
			if(#fa,
				c = -polcoef(fa[1],0);
				R = subst(R,x,x+c);
				u -= c;
				R = polrecip(R);
				u = 1/u;
				v *= u^(d/2);
				d--;
			)
		);
		if(p==0 && d%2 && polcoef(R,d)<0,
			R = subst(R,x,-x);
			u = -u
		)
	);
	[R,[u,v]];
}

CrvHyperell(C,P=0)=
{
	my(g=C[6],F=C[1][1],W=C[7],x=C[3][1],z=C[3][3],B,u,e,M,m,K2,K1,H);
	if(g<=1,error("Genus too low:",g));
	if(CrvIsHyperell(C)==0,return(0)); \\ Check if hyperell
	B = if(P,Pt2Branch(C,P),C[4][1][2][1]); \\ Make sure B is in branch form
	if(g==2, \\ Find u with deg u = 2
		u = W[1][2]/W[1][1]; \\ If g==2, easy
	,
	  if(poldegree(B[2])>1,
		  error("Please supply a rational point")
		);
		e = 2*g;
		while(1, \\ TODO while loop no longer necessary?
			M = DiffsBranchMat(W[1],W[2],B,e,x,y);
			m = #M~;
			if(m>2*g-2,break);
			e += 2*g-m;
		);
		e = g-2;
		while(1, \\ Find pair of diffs which vanish at highest order
			K2 = matker(M[1..e,]);
			m = #K2;
			if(m==2,break);
			e += m-2;
		);
		e++;
		while(1, \\ Find diff which vanishes at highest order
      K1 = matker(M[1..e,]);
      m = #K1;
      if(m==1,break);
      e += m-1;
    );
		W = W[1];
		K1 = K1[,1]; \\ Take u = highest ord / 2nd highest ord
		K = matconcat([K1,K2[,1]]);
		u = if(matrank(K)==1,(W*K2[,2])/(W*K1),(W*K2[,1])/(W*K1));
	);
	\\ K(C) is at least one of K(u,x) or K(u,y); try both
	H = CrvHyperell_sub(B,u,x,poldegree(F,y),C[3],C[2]);
	if(H==0,H=CrvHyperell_sub(B,u,y,poldegree(F,x),C[3],C[2]));
	H[2] = apply(u->FnNormalise(u,F,x,z),H[2]);
	H;
}

CanProj(C,uvw=0,P=0)=
{
	my(x,y,u,v,w,g=C[6],B,W=C[7][1],K,M,f,n);
	[u,v,w] = apply(i->W[i],if(uvw,uvw,[3,2,1]));
	[x,y] = C[3][1..2];
  B = if(P,Pt2Branch(C,P),C[4][1][2][1]);
	d = 2*g-2;
	d2 = (d+2)*(d+1)/2;
	M = f = vector(d2);
	n = 1;
	for(i=0,d,
		for(j=0,d-i,
      f[n] = x^i*y^j;
			M[n] = u^i*v^j*w^(d-i-j);
			n++;
		)
	);
	M = FnsBranchMatRat(M,B,d^2+1,x,y);
	K = matker(M);
	f = f*K[,1];
	[f,[u/w,v/w]];
}

Crv3(C,P=0)=
{
  my(x,y,u,v,w,g=C[6],B,W=C[7],K,M,f);
  if(g!=3,error("Genus is ",g," not 3"));
  if(CrvIsHyperell(C),CrvHyperell(C),CanProj(C));
}

Crv0Conic(C)=
{
	my(x,y,B,SB,d,L,u,v,K,D=0,e=4);
	[x,y] = C[3][1..2];
	B = C[4][1][2][1];
	SB = C[5];
	\\ Look for branch of deg 1 or 2; else take antican
	for(i=1,#SB,
		d = poldegree(SB[i][3][3]);
		if(d<=2,
			D = Mat([i,2/d]);
			break
		)
	);
	if(D==0,
		D = dxDiv(C);
		D[,2] *= -1;
	);
	L = RiemannRoch(C,D);
	if(#L!=3,error(""));
	u = L[2]/L[1];
	v = L[3]/L[1];
	until(#K==1,
		K = FnsBranchMatRat_conic(u,v,B,e,x,y);
		K = matker(K);
		e *= 2;
	);
	[K[,1]~,[u,v]];
}

ConicCheck(C,P)=
{
	my(x,y,Q);
	if(#P==3,return(ConicCheck(C,P[1..2]/P[3])));
	[x,y]=P;
	Q=[x^2,x*y,y^2,x,y,1]~;
	C*Q;
}

Zsqfree(n)=
{ \\ n = r*s^2;
	my(fa1,fa2,v);
	if(n==0,return([0,1]));
	fa1 = fa2 = factor(n);
	for(i=1,#fa1~,
		v = fa1[i,2];
		if(v%2,
			fa1[i,2] = 1; fa2[i,2] = (v-1)/2;
		,
			fa1[i,2] = 0; fa2[i,2] = v/2;
		)
	);
	apply(factorback,[fa1,fa2]);
}

ConicRat(C)=
{ \\ C coefs of ax^2+bxy+cy^2+dx+ey+f=0, find rat point, or prove none exists and return []
	my([a,b,c,d,e,f]=C,P,d1,f1,D,M1,x,y);
	if(a==0 && b==0 && c==0,\\ Line
	  if(d==0,
			if(e==0,error("Not a curve"));
			P = [0,-f,e];
		,
			P = [-f,0,d];
		);
		return(P/content(P));
	);
	if(b^2==4*a*c, \\ Parabolic case
		if(c==0,
			P = ConicRat([c,b,a,e,d,f]);
			if(P!=[],P = [P[2],P[1],P[3]]);
			return(P);
		);
		\\ Now c!=0
		d1 = 2*(2*c*d-b*e);
		f1 = 4*c*f-e^2;
		\\ (bx+2cy+e)^2 + d1x + f1 = 0
		if(d1==0,
			if(f1==0,error("Double line"));
			f1 = -f1;
			if(issquare(f1),error("Reducible over Q"));
			f1 = core(f1);
			print("Irreducible over Q but reducible over Q(sqrt",f1,")");
			return([]);
		);
		P = [-f1,(b*f1-e*d1)/(2*c),d1];
		return(P/content(P));
	);
	\\ General case
	if(a==0 && c==0,
		if(d*e==b*f,error("Reducible over Q"));
		if(d,
			P = [-f,0,d]
		,
			if(e,
				P = [0,-f,e]
			,
				P = [b,-f,b]
			)
		);
		return(P/content(P));
	);
	if(c==0,
    P = ConicRat([c,b,a,e,d,f]);
    if(P!=[],P = [P[2],P[1],P[3]]);
    return(P);
  );
	\\ Now c!=0
	D = 4*a*c-b^2;
	M1 = 4*((c*d)^2-b*c*d*e+a*c*e^2+b^2*c*f-a*f*(2*c)^2);
	if(M1==0,
		if(issquare(D),error("Reducible over Q"));
    D = core(D);
    print("Irreducible over Q but reducible over Q(sqrt",D,")");
    return([]);
	);
	if(D>0 && M1<0,return([]));
	P = ConicLegendre(M1,-D);
	if(P==[],return([]));
	x = (P[3]+(b*e-2*d*c)*P[1])/D;
	y = (P[2]-b*x-e*P[1])/(2*c);
	P = [x,y,P[1]];
	P/content(P);
}

/*ConicDiagRat(a,b,c)=
{ \\ ax^2+by^2+cz^2=0
	my(a2,b2,P);
	\\ -acx^2-bcy^2=(cz)^2
	[a,a2] = Zsqfree(-a*c);
	[b,b2] = Zsqfree(-b*c);
	\\ a(a2x)^2+b(b2y)^2=(cz)^2
	if(a<0 && b<0,return([]));
	P = ConicLegendre(a,b);
	if(P==[],return([]));
	P = [P[1]/a2,P[2]/b2,P[3]/abs(c)];
	P/content(P);
}*/

SqrtMod(x,n)=
{ \\ Assumes n sqfree. Relies on CRT.
	my(fa,l,p,r);
	if(x^2==x,return(x));
	fa = factor(n)[,1]; \\ TODO lazy facto
	l = #fa;
	r = vector(l);
	for(i=1,l,
		p = fa[i];
		if(!issquare(Mod(x,p)),return([]));
		r[i] = sqrt(Mod(x,p));
	);
	chinese(r);
}

ConicLegendre(a,b)=
{ \\ ax^2+by^2=z^2, a,b integers not both negative
	\\ Look for rational point
	my(r,b1,P);
	if(issquare(a,&r),return([1,0,r]));
	[b,b1] = Zsqfree(b);
	if(b1!=1,
		P = ConicLegendre(a,b);
		if(P!=[],
			P = [b1*P[1],P[2],b1*P[3]];
			P /= content(P);
		);
		return(P);
	);
	if(b==1,return([0,1,1]));
	if(abs(a)>abs(b),
		P = ConicLegendre(b,a);
		return(if(P==[],[],[P[2],P[1],P[3]]))
	);
	\\ Now |a| <= |b| and a is not a square, so any sol has y!=0
	r = SqrtMod(a,b);
	if(r==[],return([]));
	r = centerlift(r);
	b1 = (r^2-a)/b;
	P = ConicLegendre(a,b1); \\ Think in terms of b and bb1 being norms in Q(sqrta)
	if(P==[],return([]));
	P=[P[3]-r*P[1],b1*P[2],r*P[3]-a*P[1]];
	apply(abs,P)/content(P);
}

Crv0RatPt(C,E,uv)=
{
	my(P,D);
	P = CrvFindRatPt(C);
	if(P!=[],return(P));
	if(E==0,[E,uv] = Crv0Conic(C));
	P = ConicRat(E);
	if(P==[],return([]));
	if(P[3],
		D = FnDiv(C,uv[1]-P[1]/P[3])
	,
		D = FnDiv(C,if(P[1],uv[1],uv[2]))
	);
	for(i=1,#D~,
		P = D[i,1];
		if(PtDeg(P)==1,return(Branch2Pt(C,P)))
	);
	error("Bug in Crv0Rat");
}

CrvConic(C,P,Q)=
{
	my(E,P1);
	if(C[6]!=0,error("Nonzero genus"));
	if(P==0,
		[E,uv] = Crv0Conic(C);
		P1 = Crv0RatPt(C,E,uv);
		if(P1==[],return([E,uv]));
		P = P1;
	);
	CrvRat(C,P,Q);
}

PtPullback(C,uv,P)=
{
	my(u,v,Du,Dv,Q);
	[u,v] = uv;
	if(#P==3 && P[3]==0, \\ P=[a:b:0] at infty
		if(P[1], \\ a<>0 -> dehom wrt x: [u:v:1] = [1:v/u:1/u]
			[u,v] = [v,1]/u;
			P = [P[2]/P[1],0]
		, \\ P = [0:1:0] -> dehom wrt y: [u:v:1] = [u/v:1:1/v]
		  [u,v] = [u,1]/v;
			P = [0,0]
		);
	);
	Du = FnDiv(C,u-P[1]);
	Dv = FnDiv(C,v-P[2]);
	Du = select(p->p[2]>0,Du~)~;
	Dv = select(p->p[2]>0,Dv~)~;
	for(i=1,#Du~,
		for(j=1,#Dv~,
			if(Du[i,1]==Dv[j,1],
				Q = Branch2Pt(C,Du[i,1]);
				if(type(Q)=="t_VEC" && Q[3],Q=Q[1..2]/Q[3]);
				return(Q);
			)
		)
	);
	error("Bug in PtPullback");
}
