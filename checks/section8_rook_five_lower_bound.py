"""Verify the eleven-vertex EPPA selection in the five by five rook graph.

For any finite partial isomorphism, the labelled row and column equality
relations must be preserved, up to a common swap of the two directions.
Such a map extends by arbitrary completions of the two coordinate
bijections. If both choices of direction fail, one adjacent pair
witnesses each failure, so at most four vertices witness nonextendability.
"""
from itertools import combinations, permutations, product


def signatures(ordered):
    rows = columns = 0
    for idx, (u, v) in enumerate(combinations(ordered, 2)):
        if u[0] == v[0]:
            rows |= 1 << idx
        if u[1] == v[1]:
            columns |= 1 << idx
    return rows | columns, tuple(sorted((rows, columns)))


def main():
    selected = tuple(product(range(3), repeat=2)) + ((3, 3), (4, 4))
    for size in range(5):
        seen = {}
        for ordered in permutations(selected, size):
            adjacency, axes = signatures(ordered)
            if seen.setdefault(adjacency, axes) != axes:
                raise ValueError((size, ordered, adjacency, axes, seen[adjacency]))
    print("R5: verified EPPA of the eleven-vertex corner and two diagonal points")


if __name__ == "__main__":
    main()
