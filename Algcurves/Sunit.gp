PtIsInS(P,S)=
{
	my(n=#S);
	for(i=1,n,
		if(PtEq(S[i],P),return(i))
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

GetSunit(C,S,dS,Dforce=0,t=5,s=8,rs=random())=
{
	my(g,n,m,D,d,L,f,Df,j,Sf,S1,n1,tgdeg,r,P);
	setrand(rs);
	n=#S;
	g = C[6];
	tgdeg = g-if(Dforce,DivDeg(Dforce),0);
	S1 = ChooseSubset(S,s,if(Dforce,Dforce[,1],0));
	n1 = #S1;
	D = matrix(n1,2);
	D[,1] = S1~;
	m = ceil(tgdeg/n1);
	for(i=1,#S1,
		D[i,2] = round((random(2*t+1)-t+m)/PtDeg(D[i,1]));
	);
	d = DivDeg(D);
	/*r = -floor((d-tgdeg)/PtDeg(D[1,1]));
	D[1,2] += r;
	print([tgdeg,d,PtDeg(D[1,1]),r,DivDeg(D)]);*/
	r = 1+random(n1);
	D[r,2] -= floor((d-tgdeg)/PtDeg(D[r,1])); \\ Make degree close >= tgdeg
	if(Dforce,D = BDivAdd(D,Dforce));
	L = RiemannRoch(C,D);
	/*while(#L>1,
		\\print("Extra dim ",#L);
		D[1+random(n1),2] -= #L-1;
		L = RiemannRoch(C,D)
	);*/
	f = L[1];
	Df = FnDiv(C,f);
	if(Dforce,Df=BDivAdd(Df,Dforce));
	Sf = vector(n);
	for(i=1,#Df~,
		P = Df[i,1];
		if(Mod(dS,PtDeg(P)),return(0));
		j = PtIsInS(Df[i,1],S);
		Sf[j] = Df[i,2];
	);
	if(sum(i=1,n,Sf[i]*PtDeg(S[i]))!=if(Dforce,DivDeg(Dforce),0),error("Bug in GetSunit")); \\ TODO
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
	my(p=C[2],g=C[6],extra=1,h1,S,dS,dh,N,n,m,l,r,R,U,V,D,U1,G,D1,d);
	if(p==0,error("Only implemented over finite fields"));
	[S,NC] = PicGenPlaces(C);
	dS = #NC;
	print("Pic gen in deg ",dS);
	dh = ceil(2*log(6*g/(sqrt(p)-1))/log(p));
	if(dh>dS, NC=concat([NC,CrvPtCount(C,[dS+1,dh])]); print(""));
	h1 = p^g * exp(sum(d=1,dh,(NC[d]-p^d-1)/(d*p^d)));
	print("Approx h by counting up to deg ",dh,": ",h1);
	n = #S;
	m = n; \\ TODO
	l = 0;
	R = matrix(n,m);
	while(1,
		parfor(i=random(),+oo,
			GetSunit(C,S,dS,0,5,8,random()+i), \\ TODO params
			r,if(l<m && r,
				l++;
				print1(round(100*l/m),"% ");
				R[,l] = r[1]~;
				if(l==m,break)
			)
		);
		\\ Non-parallel version for debugging
		/*for(i=1,+oo,
			r = GetSunit(C,S,dS,0,5,8,i);
			if(r==0,next);
			l++;
			R[,l] = r[1]~;
				print1(round(100*l/m),"% ");
			if(l==m,break)
		);*/
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
		);
		D1 = Vec(D1);
		N = prod(i=2,#D1,D1[i]);
		print("SNF: ",D1," => Tentative h: ",N);
		if(N && abs(log(N/h1))<log(2)/2,break());
		for(i=2,#D1,
			if(D1[i],break);
			extra++
		);
		m = #R + extra;
		R = matconcat([R,matrix(n,extra)]);
		extra++;
	);
	G = Vec(G);
	[D1,G,S,dS,U[1..#G,]];
}

PicWord(C,J,X)=
{
	my(r,d,[D,G,S,dS,U]=J);
	if(type(X)!="t_MAT",
		X = if(type(X[1])=="t_VEC",Mat(X),Mat([X,1]))
	);
	parfor(i=1,+oo,
		GetSunit(C,S,dS,X,5,8,random()+i),
		r,if(r,
			r = U*r[1]~;
			for(i=1,#D,
				if(D[i],r[i]=Mod(r[i],D[i]))
			);
			return(r)
		)
	);
}
