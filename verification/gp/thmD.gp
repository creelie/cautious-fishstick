\\ thmD.gp -- Theorem D: the prism C_m x K_2 has (N+t)/2 distinct eigenvalues iff 4 !| m and 6 !| m.
\\ Exactly, for m <= 60, as the degree of the minimal polynomial of the adjacency matrix; numerically
\\ (60 digits, gap 1e-20) for m <= 300.
prismM(m) = {my(N=2*m, M=matrix(N,N)); for(i=0,N-1, my(x=i\2, y=i%2);
  M[i+1, 2*((x+1)%m)+y+1] += 1; M[i+1, 2*((x+m-1)%m)+y+1] += 1; M[i+1, 2*x+(1-y)+1] += 1); M};
bound(m) = 2*(m\2 + 1);
pred(m) = (m%4 != 0 && m%6 != 0);
default(realprecision, 60);
prismcount(m) = {my(v=List(), c); for(k=0, m\2, c=2*cos(2*Pi*k/m); listput(v, c+1); listput(v, c-1));
  v = vecsort(Vec(v)); my(cnt=1); for(i=2,#v, if(abs(v[i]-v[i-1])>1e-20, cnt++)); cnt};
{my(bad=0); for(m=3,60, if((poldegree(minpoly(prismM(m))) == bound(m)) != pred(m), bad++; print("EXACT ", m)));
 for(m=3,300, if((prismcount(m) == bound(m)) != pred(m), bad++; print("NUMERIC ", m)));
 print("Theorem D failures (exact m <= 60, numeric m <= 300): ", bad)};
quit;
