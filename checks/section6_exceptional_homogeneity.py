#!/usr/bin/env python3
"""Independent finite homogeneity audit of C5 and the 3x3 rook graph.

For each subset orbit under an explicit automorphism group, enumerate
EVERY injective adjacency-preserving partial map and check that it is the
restriction of a member of the group.

This is an independent combinatorial verification, NOT a Lean proof.
The Lean formalization of the generic EPPA lifting is checked separately.
"""
from itertools import permutations, product


def verify(name, n, adjacent, automorphisms, n_orbits, n_partial):
    group = sorted(set(automorphisms))
    assert tuple(range(n)) in group
    assert all(sorted(q) == list(range(n)) for q in group)
    assert all(
        adjacent(i, j) == adjacent(q[i], q[j])
        for q in group for i in range(n) for j in range(n)
    )
    covered = set()
    reps = []
    total = 0
    for mask in range(1 << n):
        if mask in covered:
            continue
        orbit = {
            sum(1 << q[i] for i in range(n) if mask & (1 << i))
            for q in group
        }
        assert mask in orbit
        covered |= orbit
        domain = [i for i in range(n) if mask & (1 << i)]
        reps.append((mask, len(orbit)))
        restrictions = {tuple(q[i] for i in domain) for q in group}
        chosen = []
        used = set()

        def visit():
            nonlocal total
            if len(chosen) == len(domain):
                total += 1
                assert tuple(chosen) in restrictions, (name, domain, chosen)
                return
            a = domain[len(chosen)]
            for b in range(n):
                if b in used:
                    continue
                if any(adjacent(a, x) != adjacent(b, y)
                       for x, y in zip(domain, chosen)):
                    continue
                used.add(b)
                chosen.append(b)
                visit()
                chosen.pop()
                used.remove(b)

        visit()
    assert covered == set(range(1 << n))
    assert len(reps) == n_orbits, (name, reps)
    assert total == n_partial, (name, total)
    print(f"{name}: {len(group)} automorphisms, {len(reps)} "
          f"domain orbits, {total} partial isomorphisms checked; all extend")


def main():
    cycle = lambda i, j: (i - j) % 5 in (1, 4)
    dihedral = [
        tuple((shift + sign * i) % 5 for i in range(5))
        for shift in range(5) for sign in (1, -1)
    ]
    verify("C5", 5, cycle, dihedral, 8, 66)

    grid = [(i, j) for i in range(3) for j in range(3)]
    rook = lambda a, b: (
        a != b and (grid[a][0] == grid[b][0] or
                    grid[a][1] == grid[b][1]))
    wreath = []
    for pr, pc, swap in product(permutations(range(3)),
                                permutations(range(3)), (False, True)):
        q = []
        for i, j in grid:
            x, y = (j, i) if swap else (i, j)
            q.append(3 * pr[x] + pc[y])
        wreath.append(tuple(q))
    verify("3x3 rook", 9, rook, wreath, 26, 1594)


if __name__ == "__main__":
    main()
