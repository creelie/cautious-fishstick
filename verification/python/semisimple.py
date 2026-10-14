"""semisimple.py -- Theorem A, independently of PARI: for abelian G and symmetric S, F_p[A] is semisimple
(the minimal polynomial over F_p is squarefree) iff every s in S has order prime to p. Prints the number
of (group, S, p) cases and mismatches; exits 1 on a mismatch."""
import itertools, sys
def polytrim(a):
    while a and a[-1]==0: a.pop()
    return a
def polymod(a,b,p):
    a=a[:]; inv=pow(b[-1],p-2,p)
    while len(a)>=len(b):
        c=a[-1]*inv%p; sh=len(a)-len(b)
        for i in range(len(b)): a[sh+i]=(a[sh+i]-c*b[i])%p
        polytrim(a)
    return a
def polygcd(a,b,p):
    a=polytrim(a[:]); b=polytrim(b[:])
    while b: a,b=b,polymod(a,b,p)
    return a
def minpoly(A,p):
    n=len(A); vecs=[]; basis=[]  # Krylov on matrices flattened
    cur=[[int(i==j) for j in range(n)] for i in range(n)]
    rows=[]; combos=[]
    k=0
    while True:
        v=[x%p for r in cur for x in r]
        # reduce v against rows (row echelon with tracked combos)
        comb=[0]*(k+1); comb[k]=1
        v=v[:]
        for (piv,rv,rc) in rows:
            if v[piv]:
                c=v[piv]
                v=[(x-c*y)%p for x,y in zip(v,rv)]
                rc2=rc+[0]*(k+1-len(rc))
                comb=[(x-c*y)%p for x,y in zip(comb,rc2)]
        nz=[i for i,x in enumerate(v) if x]
        if not nz:
            return comb  # comb[0..k] coefficients, monic in x^k
        piv=nz[0]; inv=pow(v[piv],p-2,p)
        v=[x*inv%p for x in v]; comb=[x*inv%p for x in comb]
        rows.append((piv,v,comb)); k+=1
        cur=[[sum(cur[i][l]*A[l][j] for l in range(n))%p for j in range(n)] for i in range(n)]
def order(g,ns):
    from math import gcd
    o=1
    for a,n in zip(g,ns):
        oi=n//gcd(a,n); o=o*oi//gcd(o,oi)
    return o
def run(ns,primes):
    G=list(itertools.product(*[range(n) for n in ns])); N=len(G); idx={g:i for i,g in enumerate(G)}
    neg=lambda g: tuple((-a)%n for a,n in zip(g,ns))
    add=lambda g,h: tuple((a+b)%n for a,b,n in zip(g,h,ns))
    classes=[]; seen=set()
    for g in G:
        if all(a==0 for a in g) or g in seen: continue
        c=sorted({g,neg(g)}); seen|=set(c); classes.append(c)
    bad=0; tot=0
    for mask in range(1,1<<len(classes)):
        S=[s for j in range(len(classes)) if mask>>j&1 for s in classes[j]]
        A=[[0]*N for _ in range(N)]
        for g in G:
            for s in S: A[idx[g]][idx[add(g,s)]]+=1
        for p in primes:
            m=minpoly(A,p)
            dm=[(i*m[i])%p for i in range(1,len(m))]
            ss = len(polygcd(m,dm,p))==1
            pred = all(order(s,ns)%p!=0 for s in S)
            tot+=1
            if ss!=pred: bad+=1; print('MISMATCH',ns,p,S,ss,pred)
    return tot,bad
T = B = 0
for ns in [(4,),(6,),(8,),(9,),(10,),(12,),(2,2),(2,4),(2,6),(3,3),(2,2,2),(2,2,3)]:
    t, b = run(ns, [2, 3, 5]); T += t; B += b
    print(ns, t, b); sys.stdout.flush()
print(f"semisimplicity criterion: {T} cases, {B} mismatches")
sys.exit(1 if B else 0)
