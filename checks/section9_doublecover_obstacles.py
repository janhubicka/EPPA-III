#!/usr/bin/env python3
"""Finite regression for the corrected two-cover obstacle criterion (stdlib only)."""
from itertools import combinations, permutations, product
from math import factorial

def taylor(n, edge):
    V=tuple(product((0,1),range(n)))
    def adj(u,v):
        a,x=u; b,y=v
        return x!=y and (bool(edge(x,y)) == (a==b))
    return V,adj

def is_eppa(V,adj,S,autos):
    S=tuple(S)
    for k in range(len(S)+1):
        for D in combinations(S,k):
            extensions={tuple(q[V.index(x)] for x in D) for q in autos}
            for R in permutations(S,k):
                if all(adj(D[i],D[j])==adj(R[i],R[j])
                       for i in range(k) for j in range(i+1,k)):
                    if R not in extensions:
                        return False
    return True

def admissible(S):
    S=set(S)
    pairs={x for _,x in S if (0,x) in S and (1,x) in S}
    return not pairs or (len(S)==2 and len(pairs)==1)

def crown(n):
    V,adj=taylor(n,lambda x,y:False)
    autos=tuple(tuple((b^flip,p[x]) for b,x in V)
          for p in permutations(range(n)) for flip in (0,1))
    assert len(autos)==2*factorial(n)
    assert all(all(adj(x,y)==adj(q[V.index(x)],q[V.index(y)])
                   for x,y in combinations(V,2)) for q in autos)
    good=set()
    for mask in range(1 << (2*n)):
        S=tuple(V[i] for i in range(2*n) if mask&(1<<i))
        observed=is_eppa(V,adj,S,autos)
        assert observed==admissible(S),(n,mask,S,observed)
        if observed: good.add(mask)
    maximal=[mask for mask in good
             if all((mask|(1<<i)) not in good
                    for i in range(2*n) if not mask&(1<<i))]
    assert len(maximal)==(1<<n)+n
    return (len(good),len(maximal))

def adversarial():
    # One Taylor double is not vertex-transitive: K2 + 3 isolated.
    V,adj=taylor(5,lambda x,y:x!=y and x<2 and y<2)
    def triangle_count(u):
        N=[v for v in V if adj(u,v)]
        return sum(adj(v,w) for v,w in combinations(N,2))
    assert triangle_count((0,0))==3
    assert triangle_count((0,2))==1

    # Vertex transitivity plus invariant pairs still is not enough.
    V,adj=taylor(5,lambda x,y:(x-y)%5 in (1,4))
    def common(u,v):
        return sum(adj(u,z) and adj(v,z) for z in V)
    for u in V:
        assert [v for v in V if v!=u and common(u,v)==0]==[(1-u[0],u[1])]
    assert common((0,0),(0,1))==1
    assert common((0,0),(1,2))==2
    assert adj((0,0),(0,1)) and adj((0,0),(1,2))
    # Its dihedral base action together with the deck map is transitive.
    autos=[tuple((b^flip,(k+(-x if refl else x))%5) for b,x in V)
           for flip,k,refl in product((0,1),range(5),(0,1))]
    assert len(set(autos))==20
    assert all(all(adj(u,v)==adj(q[V.index(u)],q[V.index(v)])
                   for u,v in combinations(V,2)) for q in autos)
    assert len({q[0] for q in autos})==10
    assert not adj((0,1),(1,2))

if __name__=="__main__":
    for n in (3,4):
        good,maximal=crown(n)
        print("crown",n,"good subsets",good,"maximal",maximal)
    adversarial()
    print("PASS: double-cover obstacle and counterexample regression")
