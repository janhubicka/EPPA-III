"""Independent finite audit of the two-point fibre argument.

In an invariant pair system, two-point EPPA produces four binary bits
(cross-edge, cross-nonedge, top-edge, top-nonedge). Equality of the
number of edges over base edges and nonedges has exactly three solutions.
For the two non-Taylor solutions, every graph automorphism preserving
the pair system must either flip all pairs or flip none. We test that
rigidity on all base graphs of order three and four, both values of the
within-fibre matching bit, and every fibre-permuting map.

This is independent computational corroboration, not a Lean proof.
"""
from itertools import combinations, permutations, product


def relation(G, cross, mate, a, b):
    layer_a, x = a
    layer_b, y = b
    if x == y:
        return bool(layer_a != layer_b and mate)
    if layer_a != layer_b:
        return bool(cross)
    return G[x][y] if layer_a == 0 else not G[x][y]


def audit_small(n):
    checked = automorphisms = bad = 0
    pairs = tuple(combinations(range(n), 2))
    vertices = tuple((layer, x) for layer in range(2) for x in range(n))
    vertex_pairs = tuple(combinations(vertices, 2))
    for mask in range(1 << len(pairs)):
        G = [[False] * n for _ in range(n)]
        for bit, (x, y) in enumerate(pairs):
            G[x][y] = G[y][x] = bool(mask & (1 << bit))
        for cross, mate in product(range(2), repeat=2):
            for sigma in permutations(range(n)):
                for flips in product((0, 1), repeat=n):
                    checked += 1

                    def move(v):
                        layer, x = v
                        return (layer ^ flips[x], sigma[x])

                    if all(relation(G, cross, mate, a, b) ==
                           relation(G, cross, mate, move(a), move(b))
                           for a, b in vertex_pairs):
                        automorphisms += 1
                        if len(set(flips)) > 1:
                            bad += 1
    return checked, automorphisms, bad


def main():
    patterns = [
        (ce, cn, te, tn)
        for ce, cn, te, tn in product(range(2), repeat=4)
        if 1 + 2 * ce + te == 2 * cn + tn
    ]
    assert patterns == [
        (0, 0, 0, 1),  # one edge between distinct fibres
        (0, 1, 1, 0),  # Taylor double
        (1, 1, 0, 1),  # three edges between distinct fibres
    ]
    print('Balanced 2x2 fibre-patterns:', patterns)
    for n, expected in ((3, (1536, 96, 0)), (4, (98304, 1152, 0))):
        actual = audit_small(n)
        assert actual == expected, (n, actual)
        print('Base order', n, ':', actual,
              '(maps screened, automorphisms, nonuniform-flip automorphisms)')
    print('TWO-POINT FIBRE CHECK PASS')


if __name__ == '__main__':
    main()
