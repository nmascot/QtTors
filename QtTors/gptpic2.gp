/* Declare vairables in appropriate order */
z;t;a;
/* Make some libpari code accessible from gp */
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

f = x^6-x^4+(t-1)*(x+1)*x; \\ Family of curves of genus 2
l=3;Chi=0;p=17;e=48;pe=p^e;h=16; \\ 3-torsion, 17-adically, prec O(17^48), O(t^16)
f0 = subst(f,t,0); \\ Fibre at t=0
P1 = [-1,0]; \\ Need two Q(t)-points 
P2 = [0,0];
[f,Auts,g,d0,L] = HyperRRdata(f,[P1,P2]); \\ Ingredients to construct Jacobian
Lp = hyperellcharpoly(Mod(f0,p)); \\ Zeta function, needed for point counting
a = FpX_root_order_bound(Lp,l)[2]; \\ Work over Qq, q=p^a
J = tPicInit(f,Auts,g,d0,L,y,p,a,e,h,Lp); \\ Jacobian over Q(t)
writebin("J_hyper_2",[B,MFrob,MAuts,G,C]);
J0 = tPicTruncate(J); \\ Special fibre at t=0
J00 = picsetprec(J0,1); \\ Special fibre at p=0
[B,MFrob,MAuts] = PicTorsBasis(J00,l,Chi); \\ l-torsion over Fq
[G,C] = PicTors_FrobGen(J00,l,B,MFrob); \\ Generating set of J(Fq)[3]
writebin("Frob_hyper_2",[B,MFrob,MAuts,G,C]);
WT00 = G[1];
WT0 = piclifttors(J0,WT00,l,1,1); \\ Lift J[3] from Fq to Zq
WT = tPicLiftTors(J,WT0,l,-1); \\ Lift J[3] from Zq to Zq[[t]]
writebin("WT_hyper_2",WT);
Z = tPicTorsSpaceFrobEval(J,[WT],C,l,MFrob,MAuts);
X = tAllPols(J,Z,l,MFrob); \\ l-divison polynomials
write("X_hyper_2.txt",X);
