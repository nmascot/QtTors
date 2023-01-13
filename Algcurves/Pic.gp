/*
g -> choose D0 of deg d0 >= 2g+1
then E1, E2 effective of deg d0-g
*/

LLLknap(w,x,p=100)=
{
	my(n=#w,m,A,B,sol,C,B1,b);
	A = matrix(n+1,n+1);
	for(i=1,n,
		A[i,i] = 1; A[n+1,i] = w[i]*p;
	);
	A[n+1,n+1] = x*p;
	\\print("A");
	\\printp(A);
	B = qflll(A);
	\\print("B");
	\\printp(B);
	\\print("AB");
	\\printp(A*B);
	\\print("Select true sols");
	B = select(b->w*b[1..n]+x*b[n+1]==0,Vec(B));
	\\print(B);
	m = #B;
	sol = List();
	B1 = 0;
	for(i=1,m,
		if(abs(B[i][n+1])==1,
			B1 = B[i];
			break
		)
	);
	\\print("B1");
	\\printp(B1);
	if(B1==0, return([]));
	for(i=1,m,
		C = B[i];
		b = C[n+1];
		\\print("Trying ",C);
		if(b==0, C -= B1; b = C[n+1]); \\print("Corrected: ",C));
		if(abs(C[n+1])!=1,next);
		C = -b*A*C;
		\\print("Now ",C);
		C = C[1..n];
		for(j=1,n,
			if(C[j]<0,
				next(2);
			)
		);
		\\print("OK");
		listput(sol,C);
	);
	Vec(sol);
}

LLLediv(C,d,p=10)=
{
	my(B,B1,BU,dB,D,i,j);
	B = C[4];
	B1 = List();
	for(i=1,#B,
		BU = B[i][2];
		for(j=1,#BU,
			listput(B1,[[i,j]]);
		)
	);
	B1 = Vec(B1);
	dB = vector(#B1);
	for(k=1,#B1,
		[i,j] = B1[k][1];
		dB[k] = poldegree(B[i][2][j][3]);
		\\print(B1[k][1]," deg ",dB[k]);
	);
	D = LLLknap(dB,d,p);
	for(i=1,#D,
		d = List();
		for(j=1,#dB,
			if(D[i][j],listput(d,[B1[j],D[i][j]]))
		);
		D[i] = matconcat(Vec(d)~);
	);
	D;
}

BDivSub(A,B)= \\ DivSub on branches
{
  my(C);
  C = List();
  for(i=1,#B~,
    for(j=1,#A~,
      if(B[i,1]==A[j,1],
        A[j,2] -= B[i,2];
        next(2)
      )
    );
    listput(C,[B[i,1],-B[i,2]]~)
  );
  C = matconcat([A~,Mat(C)]);
  C = select(c->c[2],Vec(C));
  matconcat(C)~;
}

BDivAdd(A,B)= \\ DivSub on branches
{
	my(C);
	C = List();
	for(i=1,#B~,
		for(j=1,#A~,
			if(B[i,1]==A[j,1],
				A[j,2] += B[i,2];
				next(2)
			)
		);
		listput(C,[B[i,1],B[i,2]]~)
	);
	C = matconcat([A~,Mat(C)]);
	C =	select(c->c[2],Vec(C));
	matconcat(C)~;
}

CrvPicRR(C)= \\ RR spaces needed for picinit
{
  my(f,x,d0,g,D0,E,D2,L,LL,L1,L2);
  f = C[1][1];
  x = C[3][1];
  g = C[6];
  d0 = 2*g;
  while(1,
		d0++;
		print("Trying d0=",d0);
    D0 = LLLediv(C,d0);
    if(D0==[],next);
    D0 = D0[1];
    E = LLLediv(C,d0-g);
    if(#E>=2,break);
  );
  print("Using d0=",d0);
  print("D0=",D0);
  D2 = D0;
  for(i=1,#D2~,D2[i,2]*=2); \\ 2*D0;
  print("E1=",E[1]);
  E[1] = BDivSub(D2,E[1]);
  print("2D0-E1=",E[1]);
  print("E2=",E[2]);
  E[2] = BDivSub(D2,E[2]);
  print("2D0-E2=",E[2]);
  L = RiemannRoch(C,D0);
  LL = RiemannRoch(C,D2);
  L1 = RiemannRoch(C,E[1]);
  L2 = RiemannRoch(C,E[2]);
  L = [L,LL,[L1,L2]];
	[L,denominator(L,x),d0,g];
}

CrvPic(C,p,a,e)=
{
	my(L,bad,d0,g,f,Cp,Lp);
	[L,bad,d0,g] = CrvPicRR(C);
	f = C[1][1];
	Cp = CrvInit(Mod(f,p));
	Lp = CrvCharpoly(Cp);
	picinit(f,[],g,d0,L,bad,p,a,e,Lp);
}

CrvGalRep(f,l,P,D)=
{
	my(Df,C,L,bad,d0,g,best,Cp,Lp,a,Chi,e,J);
	\\ Init curve in char 0
	Df = poldisc(f,variables(f)[2]);
	C = CrvInit(f);
	print("Genus ",C[6]);
	\\ Divisors for Makdisi
  [L,bad,d0,g] = CrvPicRR(C);
	\\ Choose p
	if(type(P)=="t_INT", \\ max p
		forprime(p=2,P,
			if(p==l,next);
			print("Trying p=",p);
			if(Mod(Df,p)==0,
				print("Non reduced");
				next
			);
			Cp = CrvInit(Mod(f,p));
			if(Cp==0,
				print("Puiseux failure");
				next;
			);
			gp = Cp[6];
			if(gp!=g,
				print("Bad reduction (genus ",gp,")");
				next;
			);
			Lp = CrvCharpoly(Cp);
  		a = rootorder(Lp,l)[2];
			print("Requires residual degree ",a);
			if(best==0 || a<best[2],
				print("Best prime so far");
				best = [p,a,Lp];
			)
		);
		[p,a,Lp] = best;
		Chi = 0;
	,
		[p,Chi] = P; \\ imposed p
    \\ TODO handle list of those
	);
  e = ceil((D*log(10)+log(2))/log(p));
  print("Working mod ",p,"^",e," in deg ",a);
	J = picinit(f,[],g,d0,L,bad,p,a,e,Lp);
  pictorsgalrep(J,l,Chi);
}
