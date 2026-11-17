#!/usr/bin/env python3
"""Independent exhaustive finite EPPA audits for icosahedron and J(6,3).

Both selected embeddings are constructed and checked, including a concrete
Petersen transversal of Johnson's graph. This computational certificate
complements, but is NOT a substitute for, a kernel-checked Lean proof.
"""
from itertools import combinations


def graph_group(n, adj):
    result, image, used = [], [], set()

    def visit():
        i = len(image)
        if i == n:
            result.append(tuple(image))
            return
        for y in range(n):
            if y in used or any(adj(i, j) != adj(y, image[j]) for j in range(i)):
                continue
            used.add(y)
            image.append(y)
            visit()
            image.pop()
            used.remove(y)

    visit()
    return result


def two_graph_group(n, adj, complement=False):
    parity = lambda a, b, c: (
        adj(a, b) + adj(b, c) + adj(c, a)) % 2
    result, image, used = [], [], set()

    def visit():
        i = len(image)
        if i == n:
            result.append(tuple(image))
            return
        for y in range(n):
            if y in used:
                continue
            if any(parity(i, a, b) !=
                   (int(complement) ^ parity(y, image[a], image[b]))
                   for a, b in combinations(range(i), 2)):
                continue
            used.add(y)
            image.append(y)
            visit()
            image.pop()
            used.remove(y)

    visit()
    return result


def taylor_graph(n, adj):
    def edge(u, v):
        x, b = divmod(u, 2)
        y, c = divmod(v, 2)
        return int(x != y and bool(adj(x, y)) == (b == c))
    return edge


def taylor_lifts(n, adj, group):
    lifts = []
    for f in group:
        h = [int(adj(0, x) != adj(f[0], f[x])) for x in range(n)]
        assert all(
            int(adj(x, y) != adj(f[x], f[y])) == (h[x] ^ h[y])
            for x in range(n) for y in range(n))
        for deck in (0, 1):
            lifts.append(tuple(2 * f[x] + (b ^ h[x] ^ deck)
                               for x in range(n) for b in (0, 1)))
    assert len(set(lifts)) == 2 * len(group)
    return lifts


def eppa_audit(name, n, base, base_aut, host, host_aut, selected,
               expected_base_aut, expected_host_aut, expected_orbits,
               expected_partial):
    assert len(base_aut) == expected_base_aut
    assert len(host_aut) == expected_host_aut
    assert len(set(selected)) == n
    assert all(base(i, j) == host(selected[i], selected[j])
               for i in range(n) for j in range(n))
    assert all(host(u, v) == host(q[u], q[v])
               for q in host_aut
               for u in range(2 * n) for v in range(2 * n))
    assert {q[0] for q in host_aut} == set(range(2 * n))
    covered, reps, count = set(), 0, 0
    for mask in range(1 << n):
        if mask in covered:
            continue
        orbit = {
            sum(1 << q[i] for i in range(n) if mask & (1 << i))
            for q in base_aut
        }
        covered |= orbit
        reps += 1
        domain = [i for i in range(n) if mask & (1 << i)]
        extensions = {tuple(q[selected[x]] for x in domain)
                      for q in host_aut}
        image, used = [], set()

        def visit():
            nonlocal count
            if len(image) == len(domain):
                count += 1
                wanted = tuple(selected[y] for y in image)
                assert wanted in extensions, (name, domain, image)
                return
            a = domain[len(image)]
            for b in range(n):
                if b in used or any(base(a, x) != base(b, y)
                                    for x, y in zip(domain, image)):
                    continue
                used.add(b)
                image.append(b)
                visit()
                image.pop()
                used.remove(b)

        visit()
    assert covered == set(range(1 << n))
    assert (reps, count) == (expected_orbits, expected_partial)
    print(f"{name}: base Aut={len(base_aut)}, host Aut={len(host_aut)}, "
          f"domain orbits={reps}, partial isomorphisms={count}; "
          "EPPA and transitivity verified")


def audit_icosahedron():
    n = 6
    graph = lambda i, j: int(
        i != j and i < 5 and j < 5 and (i - j) % 5 in (1, 4))
    base_aut = graph_group(n, graph)
    group = two_graph_group(n, graph)
    host = taylor_graph(n, graph)
    host_aut = taylor_lifts(n, graph, group)
    assert len(group) == 60
    eppa_audit("Icosahedron / C5+K1", n, graph, base_aut,
               host, host_aut, tuple(2 * i for i in range(n)),
               10, 120, 16, 213)


def audit_johnson():
    n = 10
    pairs = list(combinations(range(5), 2))
    petersen = lambda i, j: int(not (set(pairs[i]) & set(pairs[j])))
    triangular = lambda i, j: int(i != j and not petersen(i, j))

    anti = two_graph_group(n, petersen, complement=True)
    assert len(anti) == 720
    transport = anti[0]
    assert transport == (0, 1, 5, 7, 6, 9, 2, 4, 3, 8)
    inverse = [0] * n
    for i, v in enumerate(transport):
        inverse[v] = i
    side = tuple(int(triangular(0, i) !=
                     petersen(transport[0], transport[i]))
                 for i in range(n))
    assert side == (0, 1, 1, 0, 1, 0, 1, 0, 0, 1)

    taylor = taylor_graph(n, triangular)
    chosen = tuple(2 * inverse[i] + side[inverse[i]]
                   for i in range(n))
    assert chosen == (0, 3, 13, 16, 14, 5, 9, 6, 19, 10)
    assert all(petersen(i, j) == taylor(chosen[i], chosen[j])
               for i in range(n) for j in range(n))

    # The Taylor double of T(5) is J(6,3): an explicit 20-point
    # bijection sends (bottom,S) to S union {5}, and (top,S) to
    # the three-subset [5] minus S.
    triples = list(combinations(range(6), 3))
    indexes = {triple: i for i, triple in enumerate(triples)}
    theta = []
    for pair in pairs:
        theta.append(indexes[tuple(sorted((5, *pair)))])
        theta.append(indexes[tuple(k for k in range(5) if k not in pair)])
    assert len(set(theta)) == 20
    johnson = lambda i, j: int(i != j and
        len(set(triples[i]) & set(triples[j])) == 2)
    assert all(taylor(i, j) == johnson(theta[i], theta[j])
               for i in range(20) for j in range(20))
    assert tuple(theta[i] for i in chosen) == (
        3, 13, 4, 18, 17, 11, 7, 9, 0, 14)

    base_aut = graph_group(n, petersen)
    group = two_graph_group(n, triangular)
    host_aut = taylor_lifts(n, triangular, group)
    assert len(group) == 720
    eppa_audit("J(6,3) / Petersen", n, petersen, base_aut,
               taylor, host_aut, chosen, 120, 1440, 34, 4061)


def main():
    audit_icosahedron()
    audit_johnson()


if __name__ == "__main__":
    main()
