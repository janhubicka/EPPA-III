#!/usr/bin/env python3
"""Full 10-vertex Taylor(C5) EPPA obstacle enumeration (stdlib only)."""
from itertools import product, permutations, combinations

V=tuple(product((0,1),range(5)))
index={v:i for i,v in enumerate(V)}
G=lambda x,y: (x-y)%5 in (1,4)
H=lambda u,v: u[1]!=v[1] and (G(u[1],v[1])==(u[0]==v[0]))
autos=[]
for flip,k,refl in product((0,1),range(5),(0,1)):
    q=tuple(index[(b^flip,(k+(-x if refl else x))%5)] for b,x in V)
    assert all(H(V[i],V[j])==H(V[q[i]],V[q[j]])
               for i,j in combinations(range(10),2))
    autos.append(q)
assert len(set(autos))==20

def eppa(S):
    S=tuple(S)
    for n in range(len(S)+1):
        for D in combinations(S,n):
            extends={tuple(q[i] for i in D) for q in autos}
            for R in permutations(S,n):
                if all(H(V[D[i]],V[D[j]])==H(V[R[i]],V[R[j]])
                       for i,j in combinations(range(n),2)):
                    if R not in extends:
                        return False
    return True

good=set()
for mask in range(1<<10):
    S=[i for i in range(10) if mask>>i&1]
    computed=eppa(S)
    layers={V[i][0] for i in S}
    predicted=len(S)<=2 or len(layers)<=1
    assert computed==predicted,(mask,S,computed,predicted)
    if computed: good.add(mask)
assert len(good)==88
bad=set(range(1<<10))-good
minbad=[m for m in bad if all(m^(1<<i) in good
             for i in range(10) if m>>i&1)]
maxgood=[m for m in good if all((m|(1<<i)) in bad
             for i in range(10) if not m>>i&1)]
assert len(minbad)==100 and all(m.bit_count()==3 for m in minbad)
assert len(maxgood)==27 and sorted(m.bit_count() for m in maxgood)==[2]*25+[5]*2

def orbit_decomposition(masks):
    unseen=set(masks);sizes=[]
    while unseen:
        m=min(unseen)
        orb={sum(1<<q[i] for i in range(10) if m>>i&1) for q in autos}
        assert orb<=unseen
        unseen-=orb
        sizes.append(len(orb))
    return sorted(sizes)
assert orbit_decomposition(minbad)==[10,10,20,20,20,20]
assert orbit_decomposition(maxgood)==[2,5,10,10]
print("PASS Taylor(C5): 1024 subsets, 88 EPPA, 100 minimal bad triples (6 orbits), 27 maximal good (4 orbits)")
