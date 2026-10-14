\\ thmA.gp -- Theorem A on twelve groups of order at most 12, in characteristics 2, 3 and 5:
\\ every connection set when N <= 8, every symmetric one otherwise. For each case it checks
\\ A^q = adjacency matrix of Cay(G, pi(S)), dim rad = deg m_A - deg m_{A^q}, and
\\ (m_A squarefree) <=> (every s in S has order prime to p).
elts(ns) = {my(L=List()); forvec(v=vector(#ns,i,[0,ns[i]-1]), listput(L, v)); Vec(L)};
gidx(v,ns) = {my(r=0); for(i=1,#ns, r = r*ns[i] + v[i]); r+1};
tr(g,ns,E) = {my(N=#E); matrix(N,N,i,j, gidx(vector(#ns,k,(E[i][k]+g[k])%ns[k]),ns)==j)};
pip(g,ns,p) = {my(r=vector(#ns)); for(k=1,#ns, my(n=ns[k], a=valuation(n,p), m=n/p^a, u); \\ CRT: component in Z/m inside Z/n
   u = chinese(Mod(1,m), Mod(0,p^a)); r[k] = lift(Mod(g[k]*lift(u), n))); r};
gord(g,ns) = {my(o=1); for(k=1,#ns, o = lcm(o, ns[k]/gcd(g[k],ns[k]))); o};
issqfree(f) = (poldegree(gcd(f, deriv(f))) == 0);
idealdim(B, A, p, d) = {my(M=matrix(#A^2, d), C=B); for(i=1,d, M[,i] = Col(concat(Vec(C))~); C = C*A); matrank(M*Mod(1,p))};
run(ns, primes) = {my(E=elts(ns), N=#E, T=vector(N,i,tr(E[i],ns,E)), nz=vector(N-1,i,i+1), bad=0, tot=0, symonly = (N>8));
  forsubset(N-1, s, my(S=vector(#s,i,nz[s[i]]));
    if(#S==0, next);
    if(symonly, my(ok=1); for(i=1,#S, my(g=E[S[i]], ng=gidx(vector(#ns,k,(-g[k])%ns[k]),ns)); if(!setsearch(Set(S),ng), ok=0; break)); if(!ok, next));
    my(A = sum(i=1,#S, T[S[i]]));
    for(j=1,#primes, my(p=primes[j], e=1, q, Aq, Sh, mA, mAq, J, pred, ss);
      \\ q: power of p, divisible by exp(G_p), congruent 1 mod exp(G_p')
      my(ex = lcm(ns), ep = p^valuation(ex,p), eh = ex/ep); q = p; while(q % ep || (q % eh) != 1 % eh, q *= p);
      Aq = (A*Mod(1,p))^q;
      Sh = sum(i=1,#S, T[gidx(pip(E[S[i]],ns,p),ns)])*Mod(1,p);
      if(Aq != Sh, bad++; print("SHADOW ", ns, " ", p, " ", S));
      mA = minpoly(A*Mod(1,p)); mAq = minpoly(Aq);
      J = idealdim(A*Mod(1,p) - Aq, A*Mod(1,p), p, poldegree(mA));
      if(J != poldegree(mA) - poldegree(mAq), bad++; print("RAD ", ns, " ", p, " ", S));
      ss = issqfree(mA); pred = 1; for(i=1,#S, if(gord(E[S[i]],ns) % p == 0, pred = 0));
      if(ss != pred, bad++; print("CRIT ", ns, " ", p, " ", S));
      tot++)); [tot, bad]};
{
my(groups=[[4],[6],[8],[2,2],[2,4],[3,3],[9],[10],[12],[2,6],[2,2,2],[2,2,3]], tb=0, tt=0, r);
for(i=1,#groups, r = run(groups[i], [2,3,5]); print(groups[i], " ", r); tt += r[1]; tb += r[2]);
print("Theorem A checks: ", tt, " cases, ", tb, " failures");
}
quit;
