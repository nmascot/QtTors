install("ZetaFromPointCount","GUU");

/*
CrvCharpoly(C)=
{
	my(f,p,x,y,z,t,a,B,g,BadU,N,q,T,X,u,fa,BU,db);
	f = C[1][1];
	p = C[2];
	[x,y,z,t,a] = C[3];
  B = C[4]; \\ All branches
  g = C[6];
	BadU = prod(i=2,#B,B[i][1]);
	N = vector(g);
	for(d=1,g,
		print(d);
		q = p^d;
		T = ffinit(p,d,a);
		n = 0;
		for(X=0,p^d-1,
			xu = X;
			u = 0;
			for(i=0,d-1,
				u *= a;
				u += Mod(xu,p);
				xu \= p;
			);
			u = Mod(u,T);
			if(subst(BadU,x,u)==0,next);
			fa = factormod(subst(f,x,u),[p,T],1)[,1];
			for(i=1,#fa,
				if(fa[i]==1,n++)
			)
		);
		print(n);
		for(i=1,#B,
			BU = B[i][2];
			for(j=1,#BU,
				db = poldegree(BU[j][3]);
				if(Mod(d,db)==0,n+=db)
			)
		);
		N[d] = n;
	);
	print(N);
	ZetaFromPointCount(Vecsmall(N),p,g);
}
*/

/*CrvCharpoly_loc(f,BadU,p,u1,s,r,l)=
{ \\ q-1 = (p-1)*r
	\\ Fq* = Z/(q-1) ->> Z/(p-1), work in fibre x1*<s>, s=g^(p-1), x1 = g^l
	my(u=u1,x,y,n,m,fu,done,i1);
	[x,y] = variables(f);
	n = 0;
	done = vector(r);
	for(i=1,r,
		u *= s;
		if(done[i],next);
		m = 0;
		\\ TODO cst on Frob orb
		if(subst(BadU,x,u)==0,next);
		fu = subst(f,x,u);
		fu = factormod(fu,,1)~; \\ TODO
		for(j=1,#fu,
      if(fu[1,j]==1,m++)
    );
		i1 = i;
		while(done[i1]==0,
			done[i1]=1;
			n += m;
			i1 = (i1*p+l)%r;
			if(i1==0,i1=r);
		);
	);
	n;
}

export(CrvCharpoly_loc);*/
install("CrvZeta_loc","lGGGUGGUU");
install("ZX_to_Flx","GU");
install("ZXX_to_FlxX","GU");

CrvCharpoly(C)=
{
  my(f,p,x,y,z,t,a,gC,T,g,s,r,B,BadU,N,q,BU,DB,db,f0,gi);
  p = C[2];
	f = C[1][1];
  [x,y,z,t,a] = C[3];
  B = C[4]; \\ All branches
	gC = C[6];
  BadU = x/x; \\ Locus of branches
	DB = List(); \\ Degs of branches
	for(i=1,#B,
		if(i>=2,
			BadU *= B[i][1]
		);
		BU = B[i][2];
		for(j=1,#BU,
			listput(DB,poldegree(BU[j][3]))
		)
	);
	DB = Vec(DB);
	f0 = 0;
	if(polcoef(BadU,0),	f0=factormod(subst(f,x,0),p,1)[,1]);
	f = liftint(f);
  f = subst(f,x,z);
  f = subst(f,y,x);
  f = subst(f,z,y);
  f = ZXX_to_FlxX(f,p);
	BadU = ZX_to_Flx(liftint(BadU),p);
  N = vector(gC);
  for(d=1,gC,
    print1(d,"/",gC," ");
    q = p^d;
    T = ffinit(p,d,a);
		g = ffprimroot(ffgen(T));
		s = g^(p-1);
		r = (q-1)/(p-1);
		T = ZX_to_Flx(liftint(T),p);
		s = ZX_to_Flx(s.pol,p);
		gi = vector(p-1,i,g^(i-1));
		gi = apply(x->ZX_to_Flx(x.pol,p),gi);
		N[d] = vecsum(parapply(i->CrvZeta_loc(f,BadU,T,p,gi[i],s,r,i-1),[1..p-1]));
		\\ Take branches into account
		for(i=1,#DB,
      db = DB[i];
      if(Mod(d,db)==0,N[d]+=db)
    );
		\\ Take x=0 into account
		if(f0,
			for(i=1,#f0,
				if(Mod(d,f0[i])==0,N[d]+=f0[i])
			)
		)
  );
  ZetaFromPointCount(Vecsmall(N),p,gC);
}
