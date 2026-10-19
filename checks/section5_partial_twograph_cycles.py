#!/usr/bin/env python3
"""Independent finite audit of the Section 5.1 cycle-consistency proof.

Unlike the existing F2 Gaussian-elimination test, this constructs the
potential, checks every even/odd cycle, and propagates a switching.
"""
from itertools import combinations, permutations


def check(n):
    free = tuple(p for p in combinations(range(n), 2) if 0 not in p)
    tested = valid = cycle_checks = multi_odd = 0
    for mask in range(1 << len(free)):
        edges = {p: (mask >> i) & 1 for i, p in enumerate(free)}

        def e(u, v):
            return 0 if u == v else edges.get(tuple(sorted((u, v))), 0)

        def tri(u, v, w):
            return e(u, v) ^ e(v, w) ^ e(w, u)

        for k in range(n + 1):
            for dom in combinations(range(n), k):
                for img in permutations(range(n), k):
                    tested += 1
                    f = dict(zip(dom, img))
                    if any(
                        tri(*triple) != tri(*(f[x] for x in triple))
                        for triple in combinations(dom, 3)
                    ):
                        continue
                    valid += 1
                    if not dom:
                        continue
                    root = dom[0]
                    delta = lambda u, v: e(u, v) ^ e(f[u], f[v])
                    h = {x: delta(root, x) for x in dom}
                    assert all(
                        delta(u, v) == h[u] ^ h[v] for u in dom for v in dom
                    )

                    vertices = set(dom) | set(img)
                    indegree = {x: 0 for x in vertices}
                    for v in img:
                        indegree[v] += 1
                    assert max(indegree.values()) <= 1
                    seen = set()
                    components = []
                    for first in vertices:
                        if indegree[first] == 0:
                            component = []
                            x = first
                            while x not in seen:
                                seen.add(x)
                                component.append(x)
                                if x not in f:
                                    break
                                x = f[x]
                            components.append((False, component))
                    for first in vertices:
                        if first in seen:
                            continue
                        component = []
                        x = first
                        while x not in seen:
                            seen.add(x)
                            component.append(x)
                            x = f[x]
                        assert x == first
                        components.append((True, component))
                    assert seen == vertices

                    odd_sums = []
                    for cyclic, component in components:
                        if not cyclic:
                            continue
                        cycle_checks += 1
                        parity = 0
                        for x in component:
                            parity ^= h[x]
                        if len(component) % 2 == 0:
                            assert parity == 0, (n, mask, dom, img, component)
                        else:
                            odd_sums.append(parity)
                    assert len(set(odd_sums)) <= 1, (n, mask, dom, img)
                    if len(odd_sums) > 1:
                        multi_odd += 1
                    constant = odd_sums[0] if odd_sums else 0
                    switches = {}
                    for cyclic, component in components:
                        switches[component[0]] = 0
                        for i in range(len(component) - 1):
                            switches[component[i + 1]] = (
                                switches[component[i]] ^ h[component[i]] ^ constant
                            )
                        if cyclic:
                            assert (
                                switches[component[-1]] ^ switches[component[0]]
                                == h[component[-1]] ^ constant
                            )
                    for x in range(n):
                        switches.setdefault(x, 0)
                    assert all(
                        e(u, v) ^ switches[u] ^ switches[v]
                        == e(f[u], f[v]) ^ switches[f[u]] ^ switches[f[v]]
                        for u in dom for v in dom
                    )
    return tested, valid, cycle_checks, multi_odd


if __name__ == "__main__":
    for n in (4, 5):
        tested, valid, cycles, multi = check(n)
        print(f"Order {n}: {tested} maps; {valid} two-graph maps; "
              f"{cycles} cycle checks; {multi} multi-odd-cycle cases; PASS")
