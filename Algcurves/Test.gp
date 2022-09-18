read("Algcurves.gp");
C=CrvInit(F);C[6]
CrvHyperell(C)
C=CrvInit(Mod(x^3*y+y^3+x,7));CrvRat(C,[1,0,0])
C=CrvInit(F3);CrvHyperell(C)
C=CrvInit((x+1/x+y+1/y+1)*x*y);CrvEll(C,[0,0])
