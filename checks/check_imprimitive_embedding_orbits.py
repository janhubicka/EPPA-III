#!/usr/bin/env python3
"""Exhaustively compare each named base-copy set with its canonical orbit."""

from itertools import combinations


def graph(n, edge):
    return tuple(sum(1 << y for y in range(n) if x != y and edge(x,y)) for x in range(n))


def induced(g, vertices):
    return graph(len(vertices), lambda x,y: g[vertices[x]] >> vertices[y] & 1)


def automorphisms(g, h=None):
    h = g if h is None else h
    n = len(g)
    degrees_g = [ng.bit_count() for ng in g]
    degrees_h = [nh.bit_count() for nh in h]
    if sorted(degrees_g) != sorted(degrees_h):
        return
    def invariants(rows, degrees):
        return [(degrees[i], tuple(sorted(degrees[j] for j in range(n) if row >> j & 1)))
                for i,row in enumerate(rows)]
    labels_g = invariants(g, degrees_g)
    labels_h = invariants(h, degrees_h)
    masks = [sum(1 << j for j, label_h in enumerate(labels_h) if label_h == label_g)
             for label_g in labels_g]
    assignment = [-1] * n
    def solve(domains, pending):
        if not pending:
            yield tuple(assignment)
            return
        x = min(pending, key=lambda i: domains[i].bit_count())
        todo = [i for i in pending if i != x]
        js = domains[x]
        while js:
            bit = js & -js
            js ^= bit
            j = bit.bit_length() - 1
            assignment[x] = j
            updated = domains.copy()
            for i in todo:
                updated[i] &= h[j] if g[x] >> i & 1 else ~(h[j] | bit)
                if not updated[i]:
                    break
            else:
                yield from solve(updated, todo)
    yield from solve(masks, list(range(n)))


def image(perm, old):
    return tuple(sorted(perm[u] for u in old))


def disjoint(g):
    n = len(g)
    return graph(2*n, lambda x,y: x//n == y//n and g[x%n] >> (y%n) & 1)


def matching(g, complement_top=False):
    n = len(g)
    def edge(x,y):
        if x//n != y//n:
            return x%n == y%n
        return (g[x%n] >> (y%n) & 1) != bool(complement_top and x//n)
    return graph(2*n, edge)


def double(g, cross_edge):
    n = len(g)
    return graph(2*n, lambda x,y: (g[x%n] >> (y%n) & 1) if x//n == y//n
                 else cross_edge(x%n, y%n) if x < y else cross_edge(y%n, x%n))


def audit(name, host, base):
    canonical = tuple(range(len(base)))
    assert induced(host, canonical) == base, (name, induced(host, canonical), base)
    assert all(bool(host[x] >> y & 1) == bool(host[y] >> x & 1)
               for x,y in combinations(range(len(host)), 2)), name
    autos = list(automorphisms(host))
    orbit = {image(p, canonical) for p in autos}
    base_degrees = sorted(row.bit_count() for row in base)
    copies = []
    for domain in combinations(range(len(host)), len(base)):
        sub = induced(host, domain)
        if sorted(row.bit_count() for row in sub) != base_degrees:
            continue
        if next(automorphisms(sub, base), None) is not None:
            copies.append(domain)
    assert orbit <= set(copies)
    print(f"{name}: |Aut(H)|={len(autos)}, copies={len(copies)}, "
          f"canonical orbit={len(orbit)}", flush=True)
    remaining = set(copies) - orbit
    all_copies_equivalent = not remaining
    if remaining:
        # The selected base is homogeneous, so it suffices to check the entire
        # automorphism group of each orbit representative, including full maps.
        base_auts = set(automorphisms(base))
        while remaining:
            example = min(remaining)
            representation = next(automorphisms(base, induced(host, example)))
            selection = tuple(example[i] for i in representation)
            extensions = {
                tuple(selection.index(q[x]) for x in selection)
                for q in autos if image(q, selection) == example
            }
            this_orbit = {image(q, selection) for q in autos}
            missing = sorted(base_auts - extensions)
            print("  orbit", len(this_orbit), "representative", selection, "good", not missing,
                  "nonextendible", missing[:1], flush=True)
            remaining -= this_orbit
    assert all_copies_equivalent, f"{name}: a selected copy is outside the canonical orbit"


def main():
    c5 = graph(5, lambda x,y: (x-y) % 5 in (1,4))
    r3 = graph(9, lambda x,y: x//3 == y//3 or x%3 == y%3)
    wagner = graph(8, lambda x,y: (x-y) % 8 in (1,4,7))
    wagner_order = (0,4,2,6,1,3,5,7)
    wagner = induced(wagner, wagner_order)
    for name,g in [('C5',c5),('R3',r3)]:
        n=len(g)
        audit(f'{name} disjoint',disjoint(g),g)
        audit(f'{name} same matching',matching(g),g)
        audit(f'{name} complementary matching',matching(g,True),g)
        audit(f'{name} Taylor',double(g,lambda x,y:x!=y and not (g[x] >> y & 1)),g)
        if name=='C5':
            for d in (1,2):
                audit(f'{name} cyclic pairs d={d}',double(g,lambda x,y: (x-y)%5 in (0,d)),g)
        if name=='R3':
            audit(f'{name} rook cross',double(g,lambda x,y:g[x] >> y & 1),g)
    audit('Wagner',wagner,graph(4,lambda x,y:x//2==y//2))


if __name__ == "__main__":
    main()
