PolarBranchMat(L,den,b,m,x,y,t,a)=
{ \\ Matrix of coefs of parts up to O(t^m) of l(b) for l in L
  my(n=#L,M,p=2,be,pe,Le,d,c);
	if(n==0,return(Mat([])));
  while(1,
    be = BranchExpand(b[1],p);
    Le = subst(subst(L,x,be[1]),y,be[2])*(1/subst(den,x,be[1]));
    pe = serprec(Le,t);
    if(pe>=m,break); \\ TODO should be pe>=m, BUG #2358
    p += m-pe; \\ TODO should be m-pe (same bug)
  );
  Le = apply(s->s+O(t^m),Le); \\ In case some are exact, sercoef would fail
  p = vecmin(apply(l->valuation(l,t),Le)); \\ t^p + ... + O(t^m) -> m-p coeffs
  d = poldegree(b[3]);
  M = matrix(d*(m-p),n);
  for(j=1,n,
    for(i=p,m-1,
      c = liftpol(polcoef(Le[j],i,t));
      for(k=0,d-1,
        M[d*(i-p)+k+1,j] = polcoef(c,k,a)
      )
    )
  );
  M;
}

IntClosure1(y1,n,U,BU,x,y,t,a)=
{
  my(den=1,den1=1,d=poldegree(U),L=vector(n),Lr,M,K);
  \\print("Int closure above ",U);
  L[1] = 1;
  for(r=1,n-1, \\ Rank r->r+1
    L[r+1] = y1*L[r];
		\\print(L);
    while(1,
      Lr = vector(r*d+1);
      for(i=0,d-1,
        for(j=1,r,
          Lr[i*r+j] = L[j]*x^i;
        )
      );
			Lr[r*d+1] = L[r+1];
      den1 = den * U;
      \\print("Trying ",Lr," with den ",den1);
      M = apply(b->PolarBranchMat(Lr,den1,b,0,x,y,t,a),BU);
      M = matconcat(M~);
      \\printp(M);
      K = matker(M);
			\\print("#K=",#K);
			if(#K>1,breakpoint());
      if(#K==0,break);
      L[r+1] = Lr*K[,1];
      for(i=1,r,L[i]*=U);
      den = den1;
    )
  );
  [L,den];
}

export(BranchExpand);
export(PolarBranchMat);
export(IntClosure1);

IntClosure(f,B,x,y,t,a)=
{
  my(dy,lf,y1,OCU,dens);
  dy = poldegree(f,y);
  lf = polcoef(f,dy,y);
  y1 = if(poldegree(lf),lf*y,y);
  B = vecsort(B,b->poldegree(b[1]),4);
	print("Local integral closures");
  OCU = parapply(bu->IntClosure1(y1,dy,bu[1],bu[2],x,y,t,a),B);
  OCU = select(o->o[2]!=1,OCU);
  if(#OCU==0,return([powers(y1,dy-1),1]));
  if(#OCU==1,return(OCU[1]));
  dens = apply(o->o[2],OCU);
  print1("Joining... ");
  OCU = apply(lu->matrix(dy,dy,i,j,polcoef(lu[1][j],i-1,y)),OCU);
  for(i=1,#OCU,OCU[i]*=prod(j=1,#OCU,if(i==j,1,dens[j])));
	\\OCU = concat(OCU,[matid(dy)*vecprod(dens)]);
  OCU = matconcat(OCU);
  OCU = mathnf(OCU);
  print("done");
  OCU = vector(dy,j,sum(i=1,dy,OCU[i,j]*y^(i-1)));
  OCU = apply(o->o/content(o,1),OCU);
  [OCU,vecprod(dens)];
}

