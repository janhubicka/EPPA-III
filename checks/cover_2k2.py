"""Exact eight-vertex check for EPPA-III Lemma 3.7 / Claim 3.11.

Enumerate all 64 connection matrices with two diagonal types from
{0,1,M,coM} and two off-diagonal types from {M,coM}.
EPPA is tested against the specified embedded 2K2, not an arbitrary embedding.
No external Python packages are required.
"""
from itertools import combinations, permutations, product

TYPES = ("0", "1", "M", "N")


def graph(matrix):
    a = [[False] * 8 for _ in range(8)]
    for i in range(2):
        for u, v in ((2*i, 2*i+1), (4+2*i, 5+2*i)):
            a[u][v] = a[v][u] = True
    for i, j, u, v in product(range(2), repeat=4):
        p = matrix[i][j]
        if p == "1" or (p == "M" and u == v) or (p == "N" and u != v):
            x, y = 2*i+u, 4+2*j+v
            a[x][y] = a[y][x] = True
    return a


def isomorphisms(g, h):
    """Generate all adjacency-preserving bijections on eight vertices."""
    n = len(g)
    dg = [sum(row) for row in g]
    dh = [sum(row) for row in h]
    if sorted(dg) != sorted(dh):
        return
    order = sorted(range(n), key=lambda u: (-dg[u], u))
    used, f = [False] * n, [-1] * n

    def go(depth):
        if depth == n:
            yield tuple(f)
            return
        u = order[depth]
        for w in range(n):
            if used[w] or dg[u] != dh[w]:
                continue
            if any(g[u][v] != h[w][f[v]] for v in order[:depth]):
                continue
            used[w], f[u] = True, w
            yield from go(depth+1)
            used[w], f[u] = False, -1

    yield from go(0)


def eppa(g, automorphisms):
    for k in range(5):
        for domain in combinations(range(4), k):
            possible = {tuple(f[u] for u in domain) for f in automorphisms}
            for target in permutations(range(4), k):
                if any(g[u][v] != g[x][y]
                       for (u,x),(v,y) in combinations(zip(domain,target), 2)):
                    continue
                if target not in possible:
                    return False
    return True


def main():
    ntrans = neppa = 0
    classes = []
    for d0, d1, a01, a10 in product(TYPES, TYPES, ("M","N"), ("M","N")):
        matrix = ((d0,a01),(a10,d1))
        g = graph(matrix)
        autos = list(isomorphisms(g, g))
        if len({f[0] for f in autos}) != 8:
            continue
        ntrans += 1
        valid = eppa(g, autos)
        neppa += int(valid)
        for c in classes:
            if next(isomorphisms(g, c["graph"]), None) is not None:
                c["n"] += 1
                c["eppa"] += int(valid)
                break
        else:
            classes.append({"graph":g, "n":1, "eppa":int(valid),
                            "representative":matrix})

    print("Assignments checked: 64")
    print("Transitive assignments:", ntrans)
    print("Isomorphism classes:", len(classes))
    print("EPPA assignments among transitive:", neppa)
    for idx,c in enumerate(classes,1):
        degrees = sorted(sum(row) for row in c["graph"])
        print(f'Class {idx}: edges={sum(degrees)//2} '
              f'assignments={c["n"]} EPPA={c["eppa"]} '
              f'matrix={c["representative"]}')
    assert (ntrans, len(classes), neppa) == (24,4,16)
    print("FINITE CHECK PASS")


if __name__ == "__main__":
    main()
