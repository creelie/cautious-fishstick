\\ thmB.gp -- Theorem B: the minimal polynomial of A_{C_n} over F_p, p <= 7, p | n <= 80, against
\\ the product of (x - z - 1/z)^e over pairs {z, 1/z} in mu_m, and the dimension formula.
read("common.gp");
\\ predicted: prod over pairs {z,1/z} in mu_m of (x - z - 1/z)^e
pred(n,p) = {my(a=valuation(n,p), m=n/p^a, q=p^a, Q, f, r=Mod(1,p)*x^0, fa); Q = polresultant(y^m-1, y^2-x*y+1, y)*Mod(1,p); fa = factor(Q); for(i=1,#fa~, f=fa[i,1]; if(poldegree(f)==1 && (subst(f,x,2)==0 || subst(f,x,-2)==0), r*=f^((q+1)\2), r*=f^q)); r};
dform(n,p) = {my(a=valuation(n,p), m=n/p^a); if(p==2, n/2, (n + if(m%2==0,2,1))/2)};
chk(N) = {my(bad=0, mp, pr); forprime(p=2,7, for(n=3,N, if(n%p, next); mp = minpoly(cyc(n)*Mod(1,p)); pr = pred(n,p); if(mp != pr, bad++; print("MISMATCH ",n," ",p," ",factor(mp)," ",factor(pr))); if(poldegree(mp)!=dform(n,p), bad++; print("DIM ",n," ",p)))); print("modular cycle mismatches up to ", N, ": ", bad)};
\\ the statement as printed: prod over d | m of reduce(Psi_d)^e_d
pred2(n,p) = {my(a=valuation(n,p), m=n/p^a, q=p^a, V=divisors(m)); prod(i=1,#V, (Psi(V[i])*Mod(1,p))^if(V[i]<=2, (q+1)\2, q))};
chk2(N) = {my(bad=0); forprime(p=2,7, for(n=3,N, if(n%p, next); if(minpoly(cyc(n)*Mod(1,p)) != pred2(n,p), bad++; print("STATEMENT ",n," ",p)))); print("Theorem B statement mismatches up to ", N, ": ", bad)};
chk(80);
chk2(80);
quit;
