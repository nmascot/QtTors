install("TotalDegree","lGD&");
install("PolHomogenise","GGLD&");
install("ZXY_disc","GL");

PolRoot1(f)=-polcoef(f,0)/polcoef(f,1);

AlgExtend(A,G,p,maxdeg=40,maxdeg2=8)=
{ \\A(a), G(x,a) irr over Prim(a)
  \\ -> T(t), g(t) root of G(x,a(t)), a(t)
  my(x,a,d,c,T,z,al,k);
  \\print("Algextend ",A," ",G);
  x = variable(G);
  a = variable(A);
	if(poldegree(G)==1,
		z = PolRoot1(G);
		if(poldegree(A)>1,
			z = Mod(z,A)
		);
		return([A,z,a])
	);
  d = poldegree(A);
  c = polcoef(A,d);
  if(p,
    T = ffinit(p,d*poldegree(G),a);
    al = polrootsmod(subst(A,a,x),[T,p])[1];
    G = subst(liftpol(G),a,al);
    return([T,polrootsmod(G,[T,p])[1],al]);
  );
  [z,al,k] = rnfequation(A,G,1);
	d = poldegree(z);
  if(d>maxdeg,
		print("Skipping polred: degree ",d);
    z = subst(z,x,a);
    al = Mod(subst(liftpol(al),x,a),z);
    return([z,Mod(a,z)-k*al,al]);
  );

  if(default(debug),print("polred degree ",d));
	\\print(z);
  [z,T] = if(d<=maxdeg2,polredabs(z,17),polredbest(z,1));
  z = subst(z,x,a);
  T = Mod(subst(liftpol(T),x,a),z);
  al = subst(liftpol(al),x,T);
  \\ Verif
  \\if(subst(A,a,al),error("al"));
  \\if(subst(subst(G,a,al),x,T-k*al),error("g"));
  \\ End verif
  [z,T-k*al,al];
}

RootRed(A,maxdeg=40,maxdeg2=8)=
{
	my(a=variable(A),d,c,z,B);
	d = poldegree(A);
	c = polcoef(A,d);
	if(d==1,
		z = PolRoot1(A);
		B = if(type(c) == "t_INTMOD", Mod(a,c.mod), a)
	,
		if(type(c) != "t_INTMOD" && d<=maxdeg,
      if(default(debug),print("polred degree ",d));
      [B,z] = if(d<=maxdeg2,polredabs(A,17),polredbest(A,1)); 
    ,
      z = Mod(a,A); B = A;
    )
	);
	[z,B];
}

PolRoot1(f)=-polcoef(f,0)/polcoef(f,1);


read("Sing.gp");
read("Diff.gp");
read("IntClos.gp");
read("Crv.gp");
read("RR.gp");
read("Print.gp");
read("Zeta.gp");
read("Pic.gp");
read("Hom.gp");
read("Special.gp");
read("Sunit.gp");

F=-256*x^56 + 6144*x^55 - 62464*x^54 + 333824*x^53 - 859648*x^52 - 120832*x^51 + 7252992*x^50 - 16046080*x^49 - 9891072*x^48 + 90136576*x^47 - 73076736*x^46 - 237805568*x^45 + 420485120*x^44 + 341843968*x^43 - 1165840384*x^42 - 192667648*x^41 + 2178936320*x^40 - 238563328*x^39 - 3063240704*x^38 + 639488000*x^37 + 3412593664*x^36 - 639488000*x^35 - 3063240704*x^34 + 238563328*x^33 + 2178936320*x^32 + 192667648*x^31 - 1165840384*x^30 - 341843968*x^29 + (-288*y^4 + 420485120)*x^28 + (3456*y^4 + 237805568)*x^27 + (-14400*y^4 - 73076736)*x^26 + (14976*y^4 - 90136576)*x^25 + (56160*y^4 - 9891072)*x^24 + (-142848*y^4 + 16046080)*x^23 + (-52992*y^4 + 7252992)*x^22 + (400896*y^4 + 120832)*x^21 + (-55872*y^4 - 859648)*x^20 + (-624384*y^4 - 333824)*x^19 + (134784*y^4 - 62464)*x^18 + (624384*y^4 - 6144)*x^17 + (-55872*y^4 - 256)*x^16 + (16*y^6 - 400896*y^4)*x^15 + (-96*y^6 - 52992*y^4)*x^14 + (-384*y^6 + 142848*y^4)*x^13 + (3232*y^6 + 56160*y^4)*x^12 + (-5424*y^6 - 14976*y^4)*x^11 + (960*y^6 - 14400*y^4)*x^10 - 3456*y^4*x^9 + (960*y^6 - 288*y^4)*x^8 + 5424*y^6*x^7 + 3232*y^6*x^6 + 384*y^6*x^5 - 96*y^6*x^4 - 16*y^6*x^3 + 27*y^8;

F1=x^4+y^4+2*x^3+x*(x+y);

FE=(y^2-x^2)*(x-1)*(2*x-3)-4*(x^2+y^2-2*x)^2;

F2=y^3-x^7+2*x^3*y;

F3=y^9+3*x^2*y^6+3*x^4*y^3+x^6+y^2; 

F4=x^5 - 6*x^3 + 6*x^2 + y*x + (y^5 - 3*y^2);

F5=y^2*x^7 - 4*y*x^5 + 4*x^3 - y;
