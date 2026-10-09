"""Reproducible exact orbit certificate for the R3 case of EPPA--III
Lemma 3.20. Standard-library Python, no external graph package.

For a transitive imprimitive EPPA witness H of R3, the multiset of
cross neighbourhoods in G is Aut(G)-invariant, so the orbit sizes below
exclude cross-degrees 2 and 3 and identify the two degree-4 patterns.
"""
from itertools import combinations
from section3_counterexamples import rook3, automorphisms, graph

G = rook3()
A = automorphisms(G)
assert len(A) == 72

def orbits(k):
    remaining = set(combinations(range(9),k))
    answers = []
    while remaining:
        S = min(remaining)
        orbit = {tuple(sorted(p[i] for i in S)) for p in A}
        remaining -= orbit
        e = sum(G[i][j] for i,j in combinations(S,2))
        answers.append((len(orbit),e,S))
    return sorted(answers)

def graph_from_two_layers(opposite=False,cross_nonedge=False):
    edges=[]
    for i in range(9):
        for j in range(i+1,9):
            if G[i][j]:edges.append((i,j))
            if bool(G[i][j]) != opposite: edges.append((i+9,j+9))
        for j in range(9):
            if i != j and G[i][j] == (not cross_nonedge):
                edges.append((i,j+9))
    return graph(18,edges)

def triangle_counts(H):
    return [sum(H[u][v] and H[u][w] and H[v][w]
                for v in range(18) for w in range(v+1,18))
            for u in range(18)]

def main():
    for k,expected in [
        (1,[9]),
        (2,[18,18]),
        (3,[6,6,36,36]),
        (4,[9,9,36,36,36])
    ]:
        data = orbits(k)
        got = sorted(length for length,e,S in data)
        print(f'{k}-sets: orbit sizes {got}')
        assert got == expected
        if k == 4:
            small = [S for length,e,S in data if length == 9]
            assert sorted(sum(G[u][v] for u,v in combinations(S,2)) for S in small) == [2,4]
    for cross_nonedge in [False,True]:
        H = graph_from_two_layers(opposite=True,cross_nonedge=cross_nonedge)
        counts = triangle_counts(H)
        print('complementary layers, cross_nonedge',cross_nonedge,
              'triangles on G and Vprime:', counts[0],counts[9])
        assert sorted([counts[0],counts[9]]) == [10,12]
    print('SECTION 3 R3 ORBIT CERTIFICATE PASS')

if __name__ == '__main__':
    main()
