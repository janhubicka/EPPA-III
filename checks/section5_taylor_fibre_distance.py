#!/usr/bin/env python3
"""Exact finite screen of the Taylor double distance-three fibre condition.

Enumerate anchored representatives of all switching classes on 3..7
vertices. When every base pair belongs to an even-parity triple,
the only vertex at distance 3 from (side,x) must be (!side,x).
"""
from collections import deque
from itertools import combinations


def check(n):
    free = list(combinations(range(1, n), 2))
    good = bad = distances = 0
    for mask in range(1 << len(free)):
        E = {p: (mask >> i) & 1 for i, p in enumerate(free)}

        def edge(x, y):
            return x != y and E.get(tuple(sorted((x, y))), 0) == 1

        def odd(x, y, z):
            return (edge(x, y) + edge(x, z) + edge(y, z)) % 2

        covered = all(
            any(not odd(x, y, z) for z in range(n) if z != x and z != y)
            for x, y in combinations(range(n), 2)
        )
        if not covered:
            bad += 1
            continue
        good += 1
        graph = [[] for _ in range(2 * n)]
        for x in range(n):
            for y in range(n):
                if x == y:
                    continue
                for side in (0, 1):
                    for other in (0, 1):
                        if edge(x, y) ^ (side != other):
                            graph[side * n + x].append(other * n + y)

        for root in range(2 * n):
            dist = [-1] * (2 * n)
            dist[root] = 0
            queue = deque([root])
            while queue:
                v = queue.popleft()
                for w in graph[v]:
                    if dist[w] == -1:
                        dist[w] = dist[v] + 1
                        queue.append(w)
            assert all(
                (dist[v] == 3) == (v == ((root + n) % (2 * n)))
                for v in range(2 * n)
            ), (n, mask, root, dist)
            assert all(x in (0, 1, 2, 3) for x in dist)
            distances += 1
    return good, bad, distances


if __name__ == "__main__":
    for n in range(3, 8):
        a, b, c = check(n)
        print(
            f"Taylor double order {n}: {a} classes with pair coverage; "
            f"{b} without; {c} rooted distance checks PASS"
        )
