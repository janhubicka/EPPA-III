#!/usr/bin/env python3
"""Exact switching check for partial automorphisms of two-graphs."""
from itertools import combinations,permutations
def solvable(rows,n):
    piv={}
    for row in rows:
        while row:
            b=(row&-row).bit_length()-1
            if b>=n:return False
            if b in piv:row^=piv[b]
            else:piv[b]=row;break
    return True
def check(n):
    free=[p for p in combinations(range(n),2) if 0 not in p]
    total=good=0
    for mask in range(1<<len(free)):
        E={p:(mask>>i)&1 for i,p in enumerate(free)}
        def e(x,y):
            return 0 if x==y else E.get(tuple(sorted((x,y))),0)
        def tri(a,b,c):
            return e(a,b)^e(a,c)^e(b,c)
        for k in range(n+1):
            for D in combinations(range(n),k):
                for F in permutations(range(n),k):
                    total+=1
                    pos={x:i for i,x in enumerate(D)}
                    if any(tri(*q)!=tri(*(F[pos[z]] for z in q))
                           for q in combinations(D,3)):continue
                    good+=1
                    rows=[]
                    for i in range(k):
                        for j in range(i+1,k):
                            a,b,c,d=D[i],D[j],F[i],F[j]
                            var=(1<<a)^(1<<b)^(1<<c)^(1<<d)
                            rhs=e(a,b)^e(c,d)
                            rows.append(var|(rhs<<n))
                    assert solvable(rows,n),(n,mask,D,F)
    return total,good
for n in (4,5):
    total,good=check(n)
    print("Partial two-graphs order",n,"PASS:",total,"maps;",good,"preserve triples")
