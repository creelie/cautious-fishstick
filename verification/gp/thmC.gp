\\ thmC.gp -- Theorem C and Lemma 4.3.
\\ idx(n): sqrt(|disc m_{C_n}| / prod |disc Q(zeta_d)^+|), the index computed from discriminants,
\\ against formula(n) (Theorem C(i)) for n <= 150; the resultant identity of Lemma 4.3 for
\\ d < d' <= 120; the closed form D(d) for the field discriminants (d <= 150) and the relation
\\ disc(m_{C_n}) = I(n)^2 prod D(d) (n <= 100); the valuation formula (Theorem C(ii)) for n <= 400.
read("common.gp");
idx(n) = {my(V=divisors(n), m=prod(i=1,#V,Psi(V[i])), dk=1, I2);
  for(i=1,#V, if(poldegree(Psi(V[i]))>1, dk *= nfdisc(Psi(V[i]))));
  I2 = abs(poldisc(m))/abs(dk); if(!issquare(I2), return(-1)); sqrtint(I2)};
check(N) = {my(bad=0, I); for(n=3, N, I = idx(n);
  if(I != formula(n), bad++; print("MISMATCH n=", n, " index=", I, " formula=", formula(n))));
  print("index mismatches up to ", N, ": ", bad)};
resid(N) = {my(bad=0, R, Rph, ex); for(a=1,N, for(b=a+1,N,
  R = abs(polresultant(Psi(a),Psi(b))); Rph = abs(polresultant(polcyclo(a),polcyclo(b)));
  if(R^(eps(a)*eps(b)) != Rph^2, bad++; print("resultant identity fails ", a, " ", b));
  ex = if(b%a==0 && #factor(b/a)~==1, factor(b/a)[1,1]^(2*eulerphi(a)/(eps(a)*eps(b))), 1);
  if(R != ex, bad++; print("resultant value fails ", a, " ", b))));
  print("resultant failures up to ", N, ": ", bad)};
dchk(N) = {my(bad=0); for(d=1,N, my(P=Psi(d), v = if(poldegree(P)==1,1,abs(nfdisc(P))));
  if(v != D(d), bad++; print("disc mismatch d=",d))); print("field disc mismatches up to ",N,": ",bad)};
mchk(N) = {my(bad=0); for(n=3,N, my(V=divisors(n), m=prod(i=1,#V,Psi(V[i])));
  if(abs(poldisc(m)) != formula(n)^2*prod(i=1,#V,D(V[i])), bad++; print("m disc mismatch n=",n)));
  print("disc(m_Cn) mismatches up to ",N,": ",bad)};
vchk(N) = {my(bad=0, f, I); for(n=3,N, I=formula(n); f=factor(n);
  for(i=1,#f~, if(valuation(I,f[i,1]) != vform(n,f[i,1]), bad++; print("BAD ",n," ",f[i,1])));
  if(I != prod(i=1,#f~, f[i,1]^vform(n,f[i,1])), bad++; print("BADPROD ",n)));
  print("valuation formula mismatches up to ",N,": ",bad)};
check(150); resid(120); dchk(150); mchk(100); vchk(400);
quit;
