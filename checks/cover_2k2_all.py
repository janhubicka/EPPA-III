"""Exhaust all 2^16 cross relations between two copies of 2K2.

This extends the 64 restricted connection-matrix test to all possible
bipartite incidence matrices. Vertex-transitivity implies overall degree
regularity, giving a sound and very effective initial filter.

For each transitive EPPA witness, explicitly search the action of
Aut(2K2) x Aut(2K2) on the designated G and H\\G halves to see whether the
connection matrix normalises to a uniform cover or the Wagner pattern.
No external Python modules are used.
"""
from itertools import permutations, product
from cover_2k2 import isomorphisms, eppa, graph


def cross_host(mask):
    a = [[False] * 8 for _ in range(8)]
    for i in range(2):
        for u, v in ((2*i, 2*i+1), (4+2*i, 5+2*i)):
            a[u][v] = a[v][u] = True
    for x, y in product(range(4), repeat=2):
        if mask & (1 << (4*x+y)):
            a[x][4+y] = a[4+y][x] = True
    return a


def connection_mask(matrix):
    g = graph(matrix)
    return sum((1 << (4*x+y)) for x, y in product(range(4),repeat=2)
               if g[x][4+y])


def perm4():
    for q in permutations(range(2)):
        for flips in product(range(2),repeat=2):
            yield tuple(2*q[i//2] + ((i % 2) ^ flips[i//2])
                        for i in range(4))


def relabelings(mask):
    """Move C-cliques and D-cliques independently, preserving each 2K2."""
    for left in perm4():
        for right in perm4():
            out = 0
            for x, y in product(range(4),repeat=2):
                if (mask >> (4*x+y)) & 1:
                    out |= 1 << (4*left[x]+right[y])
            yield out


NORMAL_FORMS = {
    connection_mask(((X,Y),(Y,X)))
    for X in ("0","1","M","N") for Y in ("0","1")
}
NORMAL_FORMS.add(connection_mask((("M","M"),("N","M"))))


def main():
    regular = transitive = eppa_count = 0
    classes = []
    non_normal = []
    for mask in range(1 << 16):
        rows = [((mask >> (4*i)) & 15).bit_count() for i in range(4)]
        if len(set(rows)) != 1:
            continue
        cols = [sum((mask >> (4*i+j)) & 1 for i in range(4))
                for j in range(4)]
        if len(set(cols)) != 1 or rows[0] != cols[0]:
            continue
        regular += 1
        g = cross_host(mask)
        autos = list(isomorphisms(g,g))
        if len({p[0] for p in autos}) != 8:
            continue
        transitive += 1
        if not eppa(g,autos):
            continue
        eppa_count += 1
        if not any(m in NORMAL_FORMS for m in relabelings(mask)):
            non_normal.append(mask)
        for c in classes:
            if next(isomorphisms(g,c["graph"]),None) is not None:
                c["count"] += 1
                break
        else:
            classes.append({"graph":g,"mask":mask,"count":1})

    print("Cross-edge matrices checked:", 1 << 16)
    print("Degree-regular candidates:", regular)
    print("Transitive candidates:", transitive)
    print("Transitive EPPA candidates:", eppa_count)
    print("EPPA candidates without allowed normal form:", non_normal)
    print("Transitive EPPA isomorphism classes:",len(classes))
    for c in classes:
        print(f'mask={c["mask"]:#06x} assignments={c["count"]} '
              f'degree={sum(c["graph"][0])}')
    assert (regular,transitive,eppa_count,len(classes)) == (140,68,28,6)
    assert not non_normal
    print("ALL CROSS MATRICES CHECK PASS")


if __name__ == "__main__":
    main()
