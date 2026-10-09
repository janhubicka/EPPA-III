"""Exact degree-screen for the invariant pair system in Lemma 3.12, Case 2.

Two-point EPPA forces uniform 2x2 fibre-pair relations on G-edges and
G-nonedges. This enumerates the resulting five binary parameters:
  eps = mate edge, ce/cn = cross-layer edge values, et/nt = top-layer values.
For all unequal clique-size compositions with 3 <= n <= 8, the sole
regular matrices are the Taylor doubles with eps=0 or eps=1.
Uses Python's standard library only.
"""
from itertools import product


def double_matrix(sizes, eps, ce, cn, et, nt):
    cliques=[i for i,k in enumerate(sizes) for _ in range(k)]
    n=len(cliques)
    H=[[False]*(2*n) for _ in range(2*n)]
    for u in range(2*n):
        for v in range(u+1, 2*n):
            x,y=u%n,v%n
            if u//n==v//n==0:
                edge=(x!=y and cliques[x]==cliques[y])
            elif u//n==v//n==1:
                edge=(x!=y and (et if cliques[x]==cliques[y] else nt))
            elif x==y:
                edge=eps
            else:
                edge=ce if cliques[x]==cliques[y] else cn
            H[u][v]=H[v][u]=bool(edge)
    return H


def sizes_from_cuts(n, cuts):
    result=[];k=1
    for i in range(n-1):
        if cuts & (1<<i):
            result.append(k);k=1
        else:
            k+=1
    result.append(k)
    return result


def main():
    tested=0
    for n in range(3,9):
        for cuts in range(1,1<<(n-1)):
            sizes=sizes_from_cuts(n,cuts)
            if len(set(sizes))==1:
                continue
            for eps,ce,cn,et,nt in product((0,1),repeat=5):
                H=double_matrix(sizes,eps,ce,cn,et,nt)
                regular=len({sum(row) for row in H})==1
                intended=(ce,cn,et,nt)==(0,1,1,0)
                assert regular==intended,(sizes,(eps,ce,cn,et,nt))
                tested+=1
    print('Two-point invariant matrices checked:',tested)
    assert tested==7520
    print('SECTION 3 PAIR-SYSTEM DEGREE CLASSIFICATION PASS')


if __name__=='__main__':
    main()
