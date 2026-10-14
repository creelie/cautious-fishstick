\\ common.gp -- definitions shared by the checks.
\\ Psi(d): minimal polynomial of 2cos(2 pi/d) over Q;  eps(d) = 1 for d <= 2, 2 for d >= 3.
\\ formula(n): I(n) from Theorem C(i);  vform(n,p): v_p(I(n)) from Theorem C(ii).
\\ D(d): closed form for |disc Q(zeta_d)^+|;  cyc(n): adjacency matrix of C_n.
Psi(d) = if(d==1, x-2, if(d==2, x+2, minpoly(Mod(x + x^(d-1), polcyclo(d)))));
eps(d) = if(d<=2, 1, 2);
formula(n) = {my(V=divisors(n), r=1, a, b, f);
  for(i=1,#V, for(j=i+1,#V, a=V[i]; b=V[j];
    if(b%a==0, f=factor(b/a); if(#f~==1, r *= f[1,1]^(2*eulerphi(a)/(eps(a)*eps(b)))))));
  r};
vform(n,p) = {my(a=valuation(n,p), m=n/p^a);
  if(p==2, (n - m + 2*a + 1)/2, (n-m)/(2*(p-1)) + a*gcd(2,n)/2)};
D(d) = {my(f, p, k);
  if(d<=4 || d==6, return(1));
  if(d%4==2, return(D(d/2)));
  f = factor(d);
  if(#f~==1, p=f[1,1]; k=f[1,2];
     if(p==2, return(2^(2^(k-2)*(k-1)-1)), return(p^((p^(k-1)*(p*k-k-1)-1)/2))));
  d^(eulerphi(d)/2) / prod(i=1,#f~, f[i,1]^(eulerphi(d)/(2*(f[i,1]-1))))};
cyc(n) = matrix(n,n,i,j, if((i-j)%n==1 || (j-i)%n==1, 1, 0));
