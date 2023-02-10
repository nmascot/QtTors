BranchPrint(B,e=2)=
{
	my(A,x,y);
	[x,y] = liftall(BranchExpand(B[1],e));
	A = B[3];
	if(poldegree(A)>1,
		print("Branch x = ",x,", y = ",y,", where ",liftall(A)," = 0")
	,
		print("Branch x = ",x,", y = ",y)
	);
}

PointPrint(P)=
{
	my(A=0,x,y);
	if(#P==3,
		if(P[3],
			PointPrint(P[1..2]/P[3]);
		,
			if(P[1]==0,
				print([0,1,0]);
			,
				y = P[2]/P[1];
				if(type(y)=="t_POLMOD",
					A = y.mod;
					y = liftall(y);
				);
				if(poldegree(A)>1,
					print([1,y,0],", where ",liftall(A)," = 0")
				,
					print([1,y,0])
				)
			)
		);
		return;
	);
	[x,y] = P;
	if(type(x)=="t_POLMOD",
		A = x.mod;
		x = liftall(x);
	);
	if(type(y)=="t_POLMOD",
    A = y.mod;
    y = liftall(y);
  );
	if(poldegree(A)>1,
    print([x,y],", where ",liftall(A)," = 0")
  ,
    print([liftint(x),liftint(y)])
  );
}


DivPrint(D,e=2)=
{
	my(v,P);
	for(i=1,#D~,
		[P,v] = D[i,];
		print1(v," * ");
		if(type(P[1])=="t_VEC",
			BranchPrint(P,e)
		,
			PointPrint(P)
		)
	);
}

CrvPrint(C,e=2)=
{
	my(f,p,g,S);
	f = C[1][1];
	p = C[2];
	g = C[6];
	S = C[5];
	if(p,
		print("Plane curve of equation ",liftint(f)," = 0 mod ",p);
	,
		print("Plane curve of equation ",f," = 0")
	);
	print("Genus ",g);
	if(#S,
		print("Singular branches:");
		for(i=1,#S,
			print1(i,": ");
			BranchPrint(S[i][3],e);
		);
	,
		print("No singularities")
	);
}
