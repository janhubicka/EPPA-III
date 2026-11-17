#!/usr/bin/env python3
"""Exact model checks for the two nontrivial homogeneous Taylor doubles.

All graph relations and parities are Boolean. Backtracking checks the
full two-graph actions on 6 and 10 points. Host recognition uses explicit
bijections into ring and 3-subset models, respectively.
"""
from collections import Counter
from itertools import combinations, product


def graph(n, adj):
    return tuple(tuple(x != y and bool(adj(x, y)) for y in range(n)) for x in range(n))


def cycle(n):
    return graph(n, lambda x, y: (x - y) % n in (1, n - 1))


def rook(n):
    return graph(n * n, lambda x, y: x // n == y // n or x % n == y % n)


def with_isolate(g):
    return tuple(tuple(False for _ in range(len(g) + 1)) if x == 0 else
                 (False,) + g[x - 1] for x in range(len(g) + 1))


def parity(g, x, y, z):
    return g[x][y] ^ g[y][z] ^ g[z][x]


def switched(g, bits):
    return graph(len(g), lambda x, y: g[x][y] ^ bits[x] ^ bits[y])


def complement(g):
    return graph(len(g), lambda x, y: not g[x][y])


def relabel_equal(g, h, p):
    return all(g[x][y] == h[p[x]][p[y]]
               for x, y in product(range(len(g)), repeat=2))


def two_graph_automorphisms(g):
    """Each prefix is extended once, and all triples are tested when complete."""
    n = len(g)
    def visit(p, unused):
        u = len(p)
        if u == n:
            yield tuple(p)
            return
        for v in sorted(unused):
            if all(parity(g, a, b, u) == parity(g, p[a], p[b], v)
                   for a, b in combinations(range(u), 2)):
                p.append(v)
                yield from visit(p, unused - {v})
                p.pop()
    return list(visit([], set(range(n))))


def same_pair_movers(g):
    """Point movers suffice by induction on the partial-map domain."""
    n = len(g)
    if n == 5:
        return [p for a, sign in product(range(n), (1, -1))
                if relabel_equal(g, g, p := tuple((a + sign * i) % n for i in range(n)))]
    from itertools import permutations
    assert n == 9
    return [tuple(3 * p[x % 3 if flip else x // 3] +
                  q[x // 3 if flip else x % 3] for x in range(9))
            for p, q, flip in product(list(permutations(range(3))),
                                      list(permutations(range(3))), (False, True))]


def check_descendant_homogeneous(g):
    auts = same_pair_movers(g)
    assert all(relabel_equal(g, g, a) for a in auts)
    for x, y in product(range(len(g)), repeat=2):
        support = [z for z in range(len(g)) if z not in (x, y) and g[x][z] == g[y][z]]
        assert any(a[x] == y and all(a[z] == z for z in support) for a in auts)


def host_taylor(g):
    n = len(g)
    return graph(2 * n, lambda x, y:
                 x % n != y % n and (g[x % n][y % n] == (x // n == y // n)))


def icosahedron_edges(u, v):
    u, v = sorted((u, v))
    if u == 0:
        return 1 <= v <= 5
    if v == 11:
        return 6 <= u <= 10
    if u <= 5 and v <= 5 or 6 <= u and 6 <= v:
        return (v - u) % 5 in (1, 4)
    return u <= 5 and 6 <= v <= 10 and (v - u) % 5 in (0, 4)


def named_icosahedron_identification(seed):
    h = graph(12, icosahedron_edges)
    # Bottom: north pole and the lower ring. Top: the antipodes in order.
    p = (0, 6, 7, 8, 9, 10, 11, 4, 5, 1, 2, 3)
    assert sorted(p) == list(range(12))
    assert relabel_equal(host_taylor(seed), h, p)
    return p


def named_johnson_identification(seed):
    triples = list(combinations(range(6), 3))
    index = {t: i for i, t in enumerate(triples)}
    h = graph(20, lambda x, y: len(set(triples[x]) & set(triples[y])) == 2)
    model_bottom = [(0, 1, 2)] + [
        (i,) + tuple(j for j in range(3, 6) if j != k)
        for i, k in product(range(3), range(3, 6))]
    model_top = [tuple(j for j in range(6) if j not in t) for t in model_bottom]
    p = tuple(index[t] for t in model_bottom + model_top)
    assert sorted(p) == list(range(20))
    assert relabel_equal(host_taylor(seed), h, p)
    return p


def embedding(g, h):
    """Return a graph isomorphism or None, with degree and edges checked."""
    n = len(g)
    degree_g = [sum(row) for row in g]
    degree_h = [sum(row) for row in h]
    if sorted(degree_g) != sorted(degree_h):
        return None
    pos = sorted(range(n), key=lambda x: degree_g.count(degree_g[x]))
    p = [-1] * n
    def visit(k, unused):
        if k == n:
            return tuple(p)
        u = pos[k]
        for v in sorted(unused):
            if degree_g[u] == degree_h[v] and all(
                    g[u][w] == h[v][p[w]] for w in pos[:k]):
                p[u] = v
                result = visit(k + 1, unused - {v})
                if result is not None:
                    return result
                p[u] = -1
        return None
    return visit(0, set(range(n)))


def all_switchings(seed):
    for tail in product((False, True), repeat=len(seed) - 1):
        bits = (False,) + tail
        yield bits, switched(seed, bits)


def check_icosahedron_four_types(seed):
    legged_triangle = graph(6, lambda x, y: x < 3 and y < 3 or abs(x - y) == 3)
    models = (seed, complement(seed), legged_triangle, complement(legged_triangle))
    counts = Counter()
    for _, g in all_switchings(seed):
        matches = [i for i, m in enumerate(models) if embedding(g, m) is not None]
        assert len(matches) == 1
        counts[matches[0]] += 1
    return [counts[i] for i in range(4)]


def check_petersen_in_class(seed):
    pairs = list(combinations(range(5), 2))
    petersen = graph(10, lambda x, y: not set(pairs[x]).intersection(pairs[y]))
    for bits, g in all_switchings(seed):
        p = embedding(g, petersen)
        if p is not None:
            assert relabel_equal(g, petersen, p)
            return bits, p
    raise AssertionError("Petersen graph was not found in the switching class")


def check_nontrivial_pairs(seed):
    # Any set containing a Taylor fibre has odd parity on every triple
    # containing that pair. No pair in the model switching class has
    # constant parity, so all actual copies of its graphs are transversals.
    n = len(seed)
    for x, y in combinations(range(n), 2):
        odd_thirds = {bool(parity(seed, x, y, z))
                      for z in range(n) if z not in (x, y)}
        assert odd_thirds == {False, True}


def check_obvious_gardiner_descendant_exceptions(n):
    # From Gardiner, the only nonempty proper equal clique possibility
    # at a root is 3 K3 at order 10, and its complement.
    # Under any two-graph automorphism sending 0 to y, the isolated-root
    # graphs on their remaining vertices must have the same degree lists.
    for edge in (True, False):
        d = graph(n - 1, lambda x, y: (x // 3 == y // 3) == edge)
        g = with_isolate(d)
        y = 1
        new = switched(g, tuple(g[y][z] for z in range(n)))
        assert not any(new[y])
        assert sorted(sum(g[z]) for z in range(1, n)) != sorted(
            sum(new[z]) for z in range(n) if z != y)


def main():
    for descendant, model, group_order in (
            (cycle(5), named_icosahedron_identification, 60),
            (rook(3), named_johnson_identification, 720)):
        seed = with_isolate(descendant)
        p = model(seed)
        automorphisms = two_graph_automorphisms(seed)
        assert len(automorphisms) == group_order, len(automorphisms)
        assert {a[0] for a in automorphisms} == set(range(len(seed)))
        check_descendant_homogeneous(descendant)
        check_nontrivial_pairs(seed)
        print(f"order {len(seed)}: two-graph group order {group_order}, named host bijection {p}")
        if len(seed) == 6:
            print(f"icosahedral four switch types: {check_icosahedron_four_types(seed)}")
        else:
            print(f"Petersen switching and relabelling: {check_petersen_in_class(seed)}")
    check_obvious_gardiner_descendant_exceptions(10)
    print("Both 3K3 descendant orientations excluded.")


if __name__ == "__main__":
    main()
