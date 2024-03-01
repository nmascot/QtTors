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

f = t*(1+2*t-t^2)*(x^2-1)*((t*x)^2-1); \\ Family of curves of genus 1
t0 = 2;
f = subst(f,t,t0+t); \\ Shift so as to have good reductino at t=0
l=3;Chi=0;p=7;e=16;pe=p^e;h=32; \\ 3-torsion, 7-adically, prec O(7^16), O(t^32)
f0 = subst(f,t,0); \\ Fibre at t=0
P1 = [-1,0]; \\ Need two Q(t)-points 
P2 = [1,0];
[f,Auts,g,d0,L] = HyperRRdata(f,[P1,P2]); \\ Ingredients to construct Jacobian
Lp = hyperellcharpoly(Mod(f0,p)); \\ Zeta function, needed for point counting
a = FpX_root_order_bound(Lp,l)[2]; \\ Work over Qq, q=p^a
J = tPicInit(f,Auts,g,d0,L,y,p,a,e,h,Lp); \\ Jacobian over Q(t)
J0 = tPicTruncate(J); \\ Special fibre at t=0
J00 = picsetprec(J0,1); \\ Special fibre at p=0
[B,MFrob,MAuts] = PicTorsBasis(J00,l,Chi); \\ l-torsion over Fq
[G,C] = PicTors_FrobGen(J00,l,B,MFrob); \\ Generating set of J(Fq)[3]
WT00 = G[1];
WT0 = piclifttors(J0,WT00,l,1,1); \\ Lift J[3] from Fq to Zq
WT = tPicLiftTors(J,WT0,l,-1); \\ Lift J[3] from Zq to Zq[[t]]
Z = tPicTorsSpaceFrobEval(J,[WT],C,l,MFrob,MAuts);
X = tAllPols(J,Z,l,MFrob); \\ l-divison polynomials
F = X[1][1]; \\ Take first one
F = subst(F,t,t-t0); \\ Un-shift t
3*F \\ We would normally use Pade appproximants to identify the coefficients of F from Q[[t]] to Q(t); but here the coefficients convincingly lie in Q[t]
