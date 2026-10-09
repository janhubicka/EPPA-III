"""Exact small counterexample checks for EPPA--III Section 3.
Uses Python's standard library only; no graph-library oracle.
"""
from itertools import combinations, permutations


def graph(n, edges):
    adj = [[False] * n for _ in range(n)]
    for u, v in edges:
        adj[u][v] = adj[v][u] = True
    return adj


def cliques(s, t):
    return graph(s*t, ((t*i+a, t*i+b)
                 for i in range(s) for a in range(t) for b in range(a+1, t)))


def cycle(n):
    return graph(n, ((i, (i+1)%n) for i in range(n)))


def rook3():
    return graph(9, ((u, v) for u in range(9) for v in range(u+1,9)
                      if u//3 == v//3 or u%3 == v%3))


def automorphisms(H):
    n = len(H)
    degrees = [sum(row) for row in H]
    order = sorted(range(n), key=lambda u: (-degrees[u], u))
    p, used = [-1]*n, [False]*n

    def search(k):
        if k == n:
            yield tuple(p)
            return
        u = order[k]
        for v in range(n):
            if used[v] or degrees[u] != degrees[v]:
                continue
            if any(H[u][a] != H[v][p[a]] for a in order[:k]):
                continue
            p[u], used[v] = v, True
            yield from search(k+1)
            p[u], used[v] = -1, False
    return list(search(0))


def partials(H, vertices):
    vertices = tuple(vertices)
    for k in range(len(vertices)+1):
        for D in combinations(vertices, k):
            for E in permutations(vertices, k):
                if all(H[u][v] == H[E[i]][E[j]]
                       for i,u in enumerate(D) for j,v in enumerate(D) if i < j):
                    yield D, E


def eppa_against_autos(H, verts, automorphism_list):
    checked = 0
    for D, E in partials(H, verts):
        checked += 1
        assert any(all(a[u] == v for u,v in zip(D,E)) for a in automorphism_list), (D,E)
    return checked


def disjoint_double(H):
    n = len(H)
    return graph(2*n, ((n*c+u,n*c+v) for c in range(2)
                 for u in range(n) for v in range(u+1,n) if H[u][v]))


def check_three_cliques():
    H = cliques(4,3)
    G = (0,1,2, 3,4, 6)  # K3 + K2 + K1
    checked = 0
    for D, E in partials(H,G):
        checked += 1
        block = {}
        for u,v in zip(D,E):
            x,y = u//3,v//3
            assert x not in block or block[x] == y
            block[x] = y
        assert len(set(block.values())) == len(block)
        # Any such partial permutation of four blocks, followed
        # by independent permutations inside the 3-cliques, extends in H.
    assert checked == 1465
    return checked


def main():
    H = cliques(3,2)
    n = eppa_against_autos(H, (0,1,2), automorphisms(H))
    assert n == 22
    print('K2 + K1 in 3K2:', n, 'partial automorphisms extend')
    print('K3 + K2 + K1 in 4K3:', check_three_cliques(), 'extensions')

    for name, G, expected, witness in (
        ('C5', cycle(5), 286, (0,2)),
        ('R3', rook3(), 34498, (0,4)),
    ):
        aut = automorphisms(G)
        n = eppa_against_autos(G, range(len(G)), aut)
        assert n == expected
        H = disjoint_double(G)
        u,v = witness
        assert not H[u][v] and not H[u][len(G)]
        # A nonedge inside one connected component cannot be sent
        # to a nonedge across components by any automorphism of 2G.
        print('2'+name+' witnesses '+name+':', n,
              'partial automorphisms; 2'+name+' is not homogeneous')
    print('SECTION 3 CHECKS PASS')


if __name__ == '__main__':
    main()
