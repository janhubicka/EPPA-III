"""Check that an 8-vertex transitive EPPA witness for a designated
G=2K2 cannot have H\\G=P3+K1.

Regularity forces H\\G to have exactly two edges. This script exhausts
the nonmatching possibility, including every regular cross-edge matrix.
Python standard library only.
"""
from itertools import combinations, product
from section3_counterexamples import graph, automorphisms, eppa_against_autos

LEFT_EDGES = ((0,1),(2,3))
OUTSIDE_EDGES = tuple(combinations(range(4,8),2))


def main():
    regular = locally_uniform = transitive = eppa = 0
    for outside in combinations(OUTSIDE_EDGES,2):
        d0 = [0]*8
        for u,v in outside:
            d0[u] += 1
            d0[v] += 1
        if sorted(d0[4:]) != [0,1,1,2]:
            continue  # require P3 + isolated on the second half
        for r in range(5):
            total_degree = r+1  # every first-half vertex has one internal edge
            desired = [total_degree-d0[i] for i in range(4,8)]
            if any(c<0 or c>4 for c in desired):
                continue
            row_choices = tuple(combinations(range(4,8),r))
            for rows in product(row_choices,repeat=4):
                if [sum(j in row for row in rows) for j in range(4,8)] != desired:
                    continue
                regular += 1
                cross = [(i,j) for i,row in enumerate(rows) for j in row]
                H = graph(8,tuple(LEFT_EDGES)+outside+tuple(cross))
                # Vertex transitivity implies the same number of triangles
                # and the same neighbour-common-neighbour multiset at each vertex.
                triangles = [sum(H[u][v] and H[u][w] and H[v][w]
                            for v in range(8) for w in range(v+1,8))
                            for u in range(8)]
                if len(set(triangles)) != 1: continue
                invariant = [
                    tuple(sorted(sum(H[u][w] and H[v][w] for w in range(8))
                        for v in range(8) if H[u][v])) for u in range(8)]
                if len(set(invariant)) != 1: continue
                locally_uniform += 1
                autos = automorphisms(H)
                if len({p[0] for p in autos}) != 8: continue
                transitive += 1
                try:
                    eppa_against_autos(H,range(4),autos)
                except AssertionError:
                    continue
                eppa += 1
    print('P3+K1 candidate, regular:',regular,
          'locally uniform:',locally_uniform,
          'vertex-transitive:',transitive,'EPPA:',eppa)
    assert (regular,locally_uniform,transitive,eppa)==(864,96,96,0)
    print('SECTION 3 2K2 COMPLEMENT CHECK PASS')


if __name__ == '__main__':
    main()
