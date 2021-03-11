/* Development functions */

timestr(~t0)=
{
  my(t,s);
  t = [getabstime(),getwalltime()];
  s = Str("cpu ",strtime(t[1]-t0[1]),", real ",strtime(t[2]-t0[2]));
  t0[1] = t[1]; t0[2] = t[2];
  s;
}

mysize(s,threshold=10^4)=
{
  my(u="B");
  if(s>=threshold,s=round(s/1024);u="kB");
  if(s>=threshold,s=round(s/1024);u="MB");
  if(s>=threshold,s=round(s/1024);u="GB");
  if(s>=threshold,s=round(s/1024);u="TB");
  Str(s,u);
}

/* Temporary: needed until gp code is converted into C code */

install("JgetT","G");
install("Jgetp","G");
install("Jgetg","lG");
install("JgetW0","G");
install("JgetFrobMat","G");
install("JgetAutsCyc","G");
install("Fq_zeta_l","GGG");
install("AddFlipChain","GL");
install("TorsSpaceFrobEval","GGGUGG");
install("AllPols","GUGGGGGL");
install("i2c","UUU");
install("c2i","uGU");
