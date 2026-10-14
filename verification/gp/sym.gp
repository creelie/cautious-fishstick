\\ sym.gp -- Proposition 4.1: Z[A_{C_n}] has index gcd(2,n) in the symmetric integer circulants.
\\ The first columns of A^0, ..., A^{r-1} (r = deg m_{C_n}) span Z[A] e_1; the product of the
\\ nonzero Smith invariants is its index in its saturation, the symmetric integer vectors.
read("common.gp");
satidx(n) = {my(A=cyc(n), r=poldegree(minpoly(A)), v=vector(n,i,i==1)~, M=matrix(n,r), d);
  for(k=1,r, M[,k]=v; v=A*v); d=matsnf(M); prod(i=1,#d, if(d[i],d[i],1))};
{my(bad=0); for(n=3,40, if(satidx(n) != gcd(2,n), bad++; print("MISMATCH ", n, " ", satidx(n))));
 print("symmetric circulant index mismatches up to 40: ", bad)};
quit;
