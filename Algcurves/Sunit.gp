Deg1Pts(C)=
{
	my(P=List(),S,b,p=C[2],f=C[1][1],[x,y]=C[3][1..2],fi,q);
	\\ Get sing branches of deg 1
	S = C[5];
	for(i=1,#S,
		b = S[i][3];
		if(poldegree(b[3])==1,listput(P,b))
	);
	\\ TODO add pts at OO
	for(i=0,p-1,
		fi = subst(f,x,Mod(i,p));
		fi = polrootsmod(fi);
		for(j=1,#fi,
			q = [i,fi[j]];
			if(PtIsSing(f,q)==0,listput(P,q))
		)
	);
	Vec(P);
}

PtIsInS(P,S)=
{
	my(n=#S);
	if(type(P[1])=="t_VEC",
		for(i=1,n,
			if(S[i]==P,return(i))
		)
	,	
		for(i=1,n,
			if(PtEq(S[i],P),return(i))
		)
	);
	0;
}

DivsIntersect(S,T)=
{
	my(j);
	for(i=1,#S,
		j = PtIsInS(S[i],T);
		if(j,return([i,j]))
	);
	0;
}

ChooseSubset(S,m,Without)=
{
	my(n=#S,S1);
	while(1,			
		S1 = Vec(Set(vector(m,i,S[1+random(n)])));
		if(Without==0,return(S1));
		if(DivsIntersect(S1,Without)==0,return(S1));
	);
}

GetSunit(C,S,Dforce=0,t=5,s=8,rs=random())=
{
	my(g,n,m,D,d,L,f,Df,j,Sf,S1,n1,tgdeg);
	setrand(rs);
	n=#S;
	g = C[6];
	tgdeg = g-if(Dforce,DivDeg(Dforce),0);
	m = ceil(tgdeg/s);
	S1 = ChooseSubset(S,s,if(Dforce,Dforce[,1],0));
	n1 = #S1;
	D = matrix(n1,2);
	D[,1] = S1~;
	m = ceil((#S1)/g);
	for(i=1,#S1,
		D[i,2] = random(2*t+1)-t+m
	);
	d = vecsum(D[,2]);
	D[1+random(n1),2] -= d-tgdeg; \\ Make degree exactly tgdeg
	if(Dforce,
		D = matconcat([D,Dforce]~)
	);
	L = RiemannRoch(C,D);
	while(#L>1,
		\\print("Extra dim ",#L);
		D[1+random(n1),2] -= #L-1;
		L = RiemannRoch(C,D)
	);
	f = L[1];
	Df = FnDiv(C,f);
	Sf = vector(n);
	for(i=1,#Df~,
		if(Dforce,
			if(PtIsInS(Df[i,1],Dforce[,1]),next);
		);
		j = PtIsInS(Df[i,1],S);
		if(j==0,return(0));
		Sf[j] = Df[i,2];
	);
	if(Dforce,
		for(i=1,#Dforce~,
			j = PtIsInS(Dforce[i,1],Df[,1]);
			if(j==0,return(0));
			if(Df[j,2] != -Dforce[i,2],return(0))
		)
	);
	return([Sf,f]);
}

\\export(GetSunit);
\\export(RRrecord0,FindInBOO,PtUB,PtIsOnCrv,PtIsSing,BranchesAbove,RiemannRoch);
exportall();

DivSimplify(P,V)=
{
	my(Q,W,J);
	J = select(v->v,V,1);
	matconcat([vecextract(P,J)~,vecextract(V,J)]);
}

PicStruct(C)=
{
	my(p=C[2],Lp,NJ,N,S,n,m,l,r,R,U,V,D,U1,G,D1,d);
	if(p==0,error("Only implemented over finite fields"));
	S = Deg1Pts(C); \\ TODO dep on g
	n = #S;
	m = ceil(1.1*n); \\ TODO
	l = 0;
	R = matrix(n,m);
	Lp = CrvCharpoly(C);
	print("");
	NJ = subst(Lp,x,1);
	while(1,
		N = 1;
		parfor(i=1,+oo,
			GetSunit(C,S,0,5,8,i), \\ TODO params
			r,if(l<m && r,
				l++;
				print1(round(100*l/m),"% ");
				R[,l] = r[1]~;
				if(l==m,break)
			)
		);
		print("");
		[U,V,D] = matsnf(R,1);
		U1 = U^-1;
		m -= n;
		D1 = List();
		G = List();
		for(i=1,n,
			d = D[i,i+m];
			if(d==1,break);
			listput(D1,d);
			listput(G,DivSimplify(S,U1[,i]));
			if(d,
				N *= d;
				U[i,]*=Mod(1,d)
			);
		);
		if(N==NJ,break());
		print("Got ",N," vs ",NJ);
		m = #R + 10;
		R = matconcat([R,matrix(n,10)]);
	);
	D1 = Vec(D1);
	G = Vec(G);
	[D1,G,S,U[1..#G,]];
}

PicWord(C,J,X)=
{
	my(r,[D,G,S,U]=J);
	parfor(i=1,+oo,
		GetSunit(C,S,X,5,8,random()),
		r,if(r,
			return(U*r[1]~)
		)
	);
}
