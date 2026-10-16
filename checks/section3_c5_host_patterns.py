#!/usr/bin/env python3
"""Exhaustive finite audit of the cyclic 10-vertex C5 host patterns.

No external dependencies.  This does NOT prove the general Lemma 3.18:
it checks the explicitly labelled host matrices, their automorphism
actions, EPPA for the designated bottom C5, and primitivity.
"""
from itertools import combinations, permutations

VERTICES = tuple(range(10))
BOTTOM = tuple(range(5))

def edge(a, b):
    return tuple(sorted((a, b)))

def adjacent_cycle(i, j):
    return (i - j) % 5 in (1, 4)

def host(top_complement=False, offsets=(0,)):
    edges = set()
    for i, j in combinations(range(5), 2):
        if adjacent_cycle(i, j):
            edges.add(edge(i, j))
        if adjacent_cycle(i, j) != top_complement:
            edges.add(edge(5 + i, 5 + j))
    for j in range(5):
        for a in offsets:
            edges.add(edge((j + a) % 5, 5 + j))
    return frozenset(edges)

def automorphisms(edges):
    neighbors = tuple(frozenset(j for j in VERTICES
        if j != i and edge(i, j) in edges) for i in VERTICES)
    degree = tuple(map(len, neighbors))
    values = [-1] * 10
    used = [False] * 10
    result = []

    def extend(i):
        if i == 10:
            result.append(tuple(values))
            return
        for j in VERTICES:
            if used[j] or degree[i] != degree[j]:
                continue
            if any((a in neighbors[i]) != (values[a] in neighbors[j])
                   for a in range(i)):
                continue
            used[j] = True
            values[i] = j
            extend(i + 1)
            used[j] = False
            values[i] = -1

    extend(0)
    return result

def invariant_blocks(autos, size):
    """Nontrivial blocks containing vertex zero; possible sizes 2,5."""
    count = 0
    for rest in combinations(range(1, 10), size - 1):
        block = frozenset((0, *rest))
        if all(len(block & {g[v] for v in block}) in (0, size)
               for g in autos):
            count += 1
    return count

def partial_eppa(edges, autos):
    count = 0
    for k in range(6):
        for domain in combinations(BOTTOM, k):
            for image in combinations(BOTTOM, k):
                for target in permutations(image):
                    partial = dict(zip(domain, target))
                    if any((edge(u, v) in edges) !=
                           (edge(partial[u], partial[v]) in edges)
                           for u, v in combinations(domain, 2)):
                        continue
                    count += 1
                    assert any(all(g[u] == partial[u] for u in domain)
                               for g in autos), ("EPPA extension missing", partial)
    assert count == 286, count
    return count

CASES = (
    ("no cross edges", False, (), 10, 200, True, 0, 1),
    ("all cross edges", False, tuple(range(5)), 35, 200, True, 0, 1),
    ("matching prism", False, (0,), 15, 20, True, 1, 1),
    ("matching Petersen", True, (0,), 15, 120, True, 0, 0),
    ("two adjacent offsets", False, (0,1), 20, 20, True, 1, 1),
    ("two diagonal offsets", False, (0,2), 20, 320, True, 1, 0),
    ("two offsets / complementary top", True, (0,1), 20, 10, False, 1, 1),
    ("two diagonals / complementary top", True, (0,2), 20, 10, False, 1, 1),
)

def main():
    for name, top_complement, offsets, m, order, transitive, b2, b5 in CASES:
        edges = host(top_complement, offsets)
        autos = automorphisms(edges)
        assert len(edges) == m, (name, len(edges), m)
        assert len(autos) == order, (name, len(autos), order)
        assert len({g[0] for g in autos}) == (10 if transitive else 5), name
        assert invariant_blocks(autos, 2) == b2, name
        assert invariant_blocks(autos, 5) == b5, name
        partial_eppa(edges, autos)
        print(f"{name}: edges={m}, automorphisms={order}, "
              f"transitive={transitive}, blocks=(2:{b2},5:{b5}), EPPA=286")
    print("All exact C5 matrix and imprimitivity certificates passed.")

if __name__ == "__main__":
    main()
