KXYnumden(f)=
{
  my(n,d,c);
  n = numerator(f);
  d = denominator(f);
  c = denominator(content(n));
  n *= c;
  d *= c;
  c = denominator(content(d));
  n *= c;
  d *= c;
  [n,d];
}

MorImg(f,U,V)=
{
  my(n,d,X,Y,F);
  [n,d] = KXYnumden(U);
  X = polresultant(f,d*'u-n,y);
  [n,d] = KXYnumden(V);
  Y = polresultant(f,d*'v-n,y);
  F = polresultant(X,Y,x);
  subst(subst(F,'u,x),'v,y);
}

