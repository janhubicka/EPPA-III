"""Exact finite EPPA check: mate edges cannot be omitted from Claim 3.6.

Let G=C5 + isolated vertex (non-homogeneous; not a disjoint union of
cliques or its complement), and let H be the Taylor double of G with
the additional matching between fibre mates. The resulting graph is
the complement of the icosahedron. Check that H is vertex-transitive,
that every automorphism preserves the six fibre pairs, and that all
957 partial automorphisms of the chosen G extend to H.

This checks the *literal equality* wording in Claim 3.6. It does not
contradict Lemma 3.3 if 'up to complementation within all blocks' is
understood to permit toggling the mate edges.
"""
from itertools import combinations, permutations
from section3_counterexamples import graph, automorphisms, eppa_against_autos


def example():
    n=6
    G=graph(n, ((i,(i+1)%5) for i in range(5)))
    edges=[]
    for i,j in combinations(range(n),2):
        if G[i][j]:
            edges.extend(((i,j),(i+n,j+n)))
        else:
            edges.extend(((i,j+n),(j,i+n)))
    edges.extend((i,i+n) for i in range(n))
    H=graph(2*n,edges)
    return G,H


def main():
    G,H=example()
    aut=automorphisms(H)
    assert len(aut)==120
    assert {p[0] for p in aut}==set(range(12))
    fibres=[{i,i+6} for i in range(6)]
    assert all({p[i],p[i+6]} in fibres for p in aut for i in range(6))
    count=eppa_against_autos(H,tuple(range(6)),aut)
    assert count==957
    assert {sum(row) for row in H}=={6}
    print('C5+K1 with mate matching:')
    print('host order = 12, host degree = 6')
    print('automorphism count =',len(aut),'and fibre partition is invariant')
    print('partial automorphisms checked =',count)
    print('LITERAL TAYLOR-DOUBLE DISTINCTION PASS')


if __name__=='__main__':
    main()
