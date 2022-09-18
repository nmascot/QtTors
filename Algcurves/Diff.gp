/*DiffFormEval(w,B,e)=
{
  my(b,res,c,q);
  b = BranchExpand(B,e);
  res = PlaneEval(w,b);
  deriv(b[1])*res;
}

DiffFormPolarPart(w,B)=
{ \\ Polar part of w(x,y)dx along B
  my(y,p);
  y = DiffFormEval(w,B,2,t);
  p = serprec(y,x);
  if(p<0,
    y = DiffFormEval(w,B,-p+2)
  );
  y+O(t^0);
}*/

CrossProd2(A,B,C)=(B[1]-A[1])*(C[2]-A[2])-(B[2]-A[2])*(C[1]-A[1]);

ConvexHullEqn(Pts)=
{
  my(n,nU,nL,U,L,h,H);
  n = #Pts;
  Pts = vecsort(Pts);
  L = vector(n);
  U = vector(n);
  nU = nL = 0;
  for(i=1,n,
    P = Pts[i];
    while(nL>=2 && CrossProd2(L[nL-1],L[nL],P)<=0,nL--);
    nL++;
    L[nL] = P;
  );
  forstep(i=n,1,-1,
    P = Pts[i];
    while(nU>=2 && CrossProd2(U[nU-1],U[nU],P)<=0,nU--);
    nU++;
    U[nU] = P;
  );
  h = nL+nU-1;
  H = vector(nL+nU-1);
  for(i=1,nL-1,H[i]=L[i]);
  for(i=1,nU-1,H[i+nL-1]=U[i]);
  H[h] = U[nU];
  vector(h-1,i,[H[i][2]-H[i+1][2],H[i+1][1]-H[i][1],H[i][2]*H[i+1][1]-H[i][1]*H[i+1][2]]);
}

HolomorphicDifferentials(f,B,a,t)=
{
  my(x,y,d,dx,dy,S,H,L,nH,nB,fy,dxfy,mpdxfy,K,W,n,A,db,be,p,mp,Ki,Wi,Wix,b);
  [x,y] = variables(f);
  d = TotalDegree(f);
  dx = poldegree(f,x);
  dy = poldegree(f,y);
  fy = deriv(f,y);
  S = Pol2Support(f);
  H = ConvexHullEqn(S);
  nH = #H;
  W = vector((dx+1)*(dy+1)); \\ The x^(i-1)*y^(j-1) for (i,j) strictly in cvx hull of supp(f)
  n = 0;
  for(i=1,dx-1,
    for(j=1,dy-1,
      n++;
      W[n] = x^(i-1)*y^(j-1); \\ Add differential
      for(k=1,nH,
        L = H[k];
        if(L[1]*i+L[2]*j <= L[3],
          n--; \\ Remove it
          break;
        )
      )
    )
  );
  W = W[1..n];
  print(,n, " differentials strictly in convex hull of support");
	B = apply(b->b[3],B); \\ Drop org pts and U
	B = vecsort(B,b->poldegree(b[3]));
  nB = #B;
  K = vector(nB)~;
  for(i=1,nB,
    if(n==0, break);
    b = B[i][1];
		A = B[i][3];
    db = poldegree(A);
    print1("Branch ",i,"/",nB,", degree ",db,": ");
    if(db==1,b=apply(c->polcoef(c,0,a),liftpol(b))); \\ Drop polmods in deg 1
    mpdxfy = 1;
    dxfy = 0;
    while(dxfy == 0,
      mpdxfy *= 2;
      \\print("Expanding ",mpdxfy);
      be = BranchExpand(b,mpdxfy);
      \\print("dxfy");
      dxfy = PlaneEval(fy,be);
    );
    dxfy = deriv(be[1],t)/dxfy;
    \\print("prec dxfy: ",serprec(dxfy,t));
    \\print("Eval x");
    Wix = parapply(w->subst(w,x,be[1]),W);
    \\print("Eval y ",mpdxfy);
    Wi = parapply(w->subst(w,y,be[2])*dxfy,Wix);
    p = apply(w->serprec(w,t),Wi);
    mp = vecmin(p);
    if(mp<0,
      \\print("Worst: ",mp);
      mp = mpdxfy-mp;
      \\print("Expanding ",mp);
      be = BranchExpand(b,mp);
      \\print("dxfy");
      dxfy = deriv(be[1],t)/PlaneEval(fy,be);
      \\print("Eval y");
      Wi = parvector(n,j,subst(Wix[j],y,be[2])*dxfy); \\ TODO lower prec
    );
    p = -valuation(Wi,t);
    Ki = matrix(p*db,n);
    Wi = liftpol(Wi);
    for(j=1,n,
      for(k=1,p,
        for(m=0,db-1,
          Ki[db*(k-1)+m+1,j] = polcoef(polcoef(Wi[j],-k,t),m,a)
        )
      )
    );
    \\K[i] = Ki;
		\\print("Linalg");
    W = W*matker(Ki);
    n = #W;
    print("g drops to ",n);
  );
  [n,[W,fy]];
}

