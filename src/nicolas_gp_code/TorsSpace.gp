ProjPol(Z,l,d,op)=
\\ Given conjugate algebraic numbers indexed by A^n,
\\ gathers them along vector lines in a symmetric way
\\ --> conjugate algebraic numbers indexed by P^(n-1).
\\ Useful to go from a linear representation to its projectivisation
{
	my(PZ,PV,done,j,v,z,PF,PA,t);
	PZ=List();
	PV=List();
	done=vector(l^d-1);
	for(i=1,l^d-1,
		if(done[i],next);
		v=Vec(i2c(i,l,d));
		listput(PV,v);
		z=op;
		for(k=1,l-1,
		 j=c2i(Vecsmall(k*v),l);
		 done[j]=1;
		 z=if(op,z*Z[j],z+Z[j]);
		);
		listput(PZ,z);
	);
	PZ=Vec(PZ);
	PF=factorback(apply(z->'x-z,PZ));
	PA=bestappr(liftpol(PF));
	t=variable(Z[1].mod);
	if(poldegree(PA,t)==0,PA=subst(PA,t,0));
	[PA,PZ,Vec(PV)];
}

TorsSpaceFrobGen(J,l,B,matFrob)=
\\ Given the basis B of a subspace T of J[l] stable under Frob,
\\ and the matrix of Frob w.r.t. B,
\\ Finds a minimal generating set WB of T as an Fl[Frob]-module
\\ and returns it, along as the coordinates of the generators on B
{
	my(F,Q,NF,WB,cB,n,c);
	[F,Q] = matfrobenius(Mod(matFrob,l),2); \\ F = rational canonical form of matFrob, Q = transition matrix
	Q = lift(Q^(-1));
	NF = apply(poldegree,matfrobenius(F,1)); \\ List of degrees of elementary divisors
	WB = List(); cWB = List();
	n = 1;
	for(i=1,#NF,
  	c=Q[,n];
  	listput(cWB,c);
  	c=centerlift(Mod(c,l));
  	listput(WB,PicLC(J,c,B));
  	n+=NF[i]
	);
	WB = Vec(WB); \\ Generating set of T under Frob
	cWB = Vec(cWB); \\ Coordinates of these generators on B
	[WB,cWB];
}
