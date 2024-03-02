/* Declare variables in appropriate order */
z;t;a;
/* Load libpari code */
install("PlaneZeta","GU");
install("tPicInit","GGUUGGGGLUG");
install("tPicRand","GG");
install("tPicChord","GGGL");
install("tPicMul","GGGL");
install("tPicTruncate","G");
install("tPicSetPrec","GU");
install("tPicEval","GG");
setdebug("pic",1);
install("HyperRRdata","GG");
install("SmoothRRdata","GGGG");
install("FpX_root_order_bound","GG");
install("PicTorsBasis","GGG");
install("PicTors_FrobGen","GGGG");
install("ZqXn_Subspace_normalize","GGGGGLU")
install("FqM_indexrank","GGG")
install("tPicInflate_U","GGG")
install("tPicDeflate_U","GGU")
install("tPicMember_val","GG");
install("tPicEq_val","GGG");
install("tPicIsZero_val","GG");
install("tPicIsTors_val","GGG");
install("tPicMember","iGG");
install("tPicEq","iGGG");
install("tPicIsZero","iGG");
install("tPicIsTors","iGGG");
install("tPicLiftTors","GGGL");
install("tPicTorsSpaceFrobEval","GGGUGG");
install("ZqXnV_mroots_to_pol","GGG");
install("tAllPols","GGUG");

f=x^4+(2-t)*y^4+2*x^3+x*(x+y)+(t-1)*(y+x^2+x); /* Family of plane quartics */
P1=[0,0]; \\ Need two Q(t)-points
P2=[-1,0];
P=[[P1],[P2]];
l=2;Chi=0;p=5;e=128;pe=p^e;a=7;h=128; \\ 2-torsion 5-adically, prec O(5^128), O(t^128)
[f,Auts,g,d0,L] = SmoothRRdata(f,p,P,t); \\ Data to construct Jacobian
Lp = PlaneZeta(subst(f,t,0),p); \\ Zeta function for point-counting
J = tPicInit(f,Auts,g,d0,L,y,p,a,e,h,Lp); \\ Jacobian over Q(t)
writebin("J_g3",J);
J0 = tPicTruncate(J); \\ Special fibre over t=0
J00 = picsetprec(J0,1); \\ Special fibre over p=0
[B,MFrob,MAuts] = PicTorsBasis(J00,l,Chi); \\ Generators for J(Fq)[2]
[G,C] = PicTors_FrobGen(J00,l,B,MFrob);
writebin("Frob_g3",[B,MFrob,MAuts,G,C]);
WT00 = G[1];
WT0 = piclifttors(J0,WT00,l,1,1); \\ Lift to J(Zq)[2]
WT = tPicLiftTors(J,WT0,l,-1); \\ Lift to J(Zq[[t]])[2]
writebin("WT_g3",WT);
Z = tPicTorsSpaceFrobEval(J,[WT],C,l,MFrob,MAuts);
X = tAllPols(J,Z,l,MFrob); \\ 2-division polynomials
writebin("X_g3",X);
