#!/usr/bin/env python3
"""Independent finite EPPA sufficiency check for all uniform clique covers.

Checks (1) that every partial isomorphism of sK_t with st<=6 is
the restriction of a full wreath-product base automorphism, and
(2) that each base automorphism lifts diagonally to every uniform
cover (all four X and two Y choices), for several larger cases.
The arbitrary-size proof of (2) is CoverAutomorphismLift.lean.
"""

from itertools import combinations, permutations, product


def base_adj(s, t, u, v):
    return u // t == v // t and u != v


def host_adj(s, t, X, Y, u, v):
    if u == v:
        return False
    n = s * t
    su, sv = u // n, v // n
    x, y = u % n, v % n
    if su == sv:
        return base_adj(s, t, x, y)
    if x // t != y // t:
        return Y
    if X == "0":
        return False
    if X == "1":
        return True
    if X == "M":
        return x % t == y % t
    return x % t != y % t


def wreath_permutations(s, t):
    inner = list(permutations(range(t)))
    for outer in permutations(range(s)):
        for inners in product(inner, repeat=s):
            yield tuple(outer[i] * t + inners[i][a]
                        for i in range(s) for a in range(t))


def check(s, t, complete):
    n = s * t
    autos = list(wreath_permutations(s, t))
    assert len(autos) == __import__("math").factorial(s) * (
        __import__("math").factorial(t) ** s)
    for p in autos:
        assert len(set(p)) == n
        for u in range(n):
            for v in range(n):
                assert base_adj(s, t, u, v) == base_adj(
                    s, t, p[u], p[v])
    if complete:
        for k in range(n + 1):
            for domain in combinations(range(n), k):
                lifts = {tuple(p[x] for x in domain) for p in autos}
                for target in permutations(range(n), k):
                    partial = all(
                        base_adj(s, t, domain[i], domain[j])
                        == base_adj(s, t, target[i], target[j])
                        for i in range(k) for j in range(i + 1, k)
                    )
                    assert (target in lifts) == partial, (s, t, domain, target)
    lifted = 0
    for X in ("0", "1", "M", "m"):
        for Y in (False, True):
            for p in autos:
                for u in range(2 * n):
                    U = u // n * n + p[u % n]
                    for v in range(2 * n):
                        V = v // n * n + p[v % n]
                        assert host_adj(s, t, X, Y, u, v) == host_adj(
                            s, t, X, Y, U, V
                        ), (s, t, X, Y, p, u, v)
                lifted += 1
    return len(autos), lifted


def main():
    cases = [(1,t) for t in range(1,7)] + [
        (2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)
    ]
    checks = 0
    for s, t in cases:
        a, lifts = check(s,t,s*t<=6)
        checks += lifts
        print(f"s={s}, t={t}: {a} base automorphisms, "
              f"{lifts} checked cover lifts, "
              f"{'complete partial-isomorphism test' if s*t<=6 else 'lift-only test'}")
    print(f"Uniform generalized clique-cover sufficiency PASS: "
          f"{checks} lifted automorphisms")


if __name__ == "__main__":
    main()
