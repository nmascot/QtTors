BranchEvDiff(B,W,e)=
{
	my(BE,WE);
	BE=BranchExpand(B[1],e);
	WE=subst(subst(W[1],x,BE[1]),y,BE[2])*deriv(BE[1])/subst(subst(W[2],x,BE[1]),y,BE[2]);
	apply(w->centerlift(w)+O(t^0),WE);
}
