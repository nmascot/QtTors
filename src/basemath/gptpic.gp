t;a;
install("gvar","lG");
print1(a);
print1(" ");
print(gvar(a));
print1(t);
print1(" ");
print(gvar(t));
p=17;e=6;pe=p^e;h=4;a=3;
T=liftall(ffinit(p,a,'a));
RandZqXn()=Pol(vector(h,i,random(pe*variable(T)^(poldegree(T)-1))),t);
A = matrix(3,2,i,j,RandZqXn());
install("ZqXn_0","ULL");
install("ZqXn_1","ULL");
install("ZqXn_from_Z","GULL");
install("ZqXn_from_Zq","GLL");
install("ZqXn_setprec","GUL");
install("ZqXn_add","GG");
install("ZqXn_sub","GG");
install("ZqXn_mul","GGGG");
install("ZqXn_inv","GGGGL");
install("ZqXn_div","GGGGGL");
install("ZqXnM_mul","GGGG");
install("ZqXnM_inv","GGGGL");
install("ZqXnM_ker","GGGGL");
install("ZqXnM_eqn","GGGGL");
install("ZqXnM_to_ZqM","G");
install("tFnEvalAt","GGGGGGLU");
install("tCrvLiftPty","GGGGGGGGGLU");
install("tPicInit","GGUUGGGGLUG");
install("tPicRand","GG");
install("tPicChord","GGGL");
install("tPicMul","GGGL");
install("tPicTruncate","G");
install("tPicSetPrec","GU");
install("tPicEval","GG");
setdebug("pic",5);
install("HyperRRdata","GG");
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
install("tPicLiftTors","GGGL");
f = x^6-x^4+(t-1)*(x+1)*x;
f0 = subst(f,t,0);
P1 = [-1,0];
P2 = [0,0];
[f,Auts,g,d0,L] = HyperRRdata(f,[P1,P2]);
\\Auts = [];
Lp = hyperellcharpoly(Mod(f0,p));
l = 3;
Chi = 0;
a = FpX_root_order_bound(Lp,l)[2];
J = tPicInit(f,Auts,g,d0,L,y,p,a,e,h,Lp);
J0 = tPicTruncate(J);
Wq = picrandtors(J0,l);
\\Wq = picrand(J0);
W = tPicLiftTors(J,Wq,l,-1);
/*J00 = picsetprec(J0,1);
[B,MFrob,MAuts] = PicTorsBasis(J00,l,Chi);
[G,C] = PicTors_FrobGen(J00,l,B,MFrob);
WT00 = G[1];
WT0 = piclifttors(J0,WT00,l,1,1);*/
/*L = [1,x,x^2,x^3,y];
LL = [1,x,x^2,x^3,x^4,x^5,x^6,y,x*y,x^2*y,x^3*y];
f = x^6-x^4+(t-1)*(x+1)*x;
x1 = 0;
y1 = 1;
x2 = -1;
y2 = 0;
L1 = ;
L2 = ;
L = [L,LL,[L1,L2]];
J = tPicInit(y^2-x^6-1+t,[],2,6,L,y,p,a,e,h,0);*/


