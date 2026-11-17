"""Exact check of actual half-order EPPA selections in the four by four rook graph.

Every clique of size four is an entire row or column: a clique containing two
cells in one row cannot contain a cell outside that row. The eight such cliques
form a complete bipartite intersection graph on the four rows and four columns.
Thus every host automorphism permutes the rows and columns, possibly swapping
their parts, and this action determines the cell permutation. Conversely each
of the 2 * (4!)^2 resulting permutations preserves adjacency.

An induced selection S is EPPA exactly when (i) all abstract automorphisms of
each subset A of S extend and (ii) induced isomorphic subsets A and B of S
belong to the same host orbit. In the second condition one host automorphism
mapping A to B then reduces the extension of any map A to B to (i).
"""
from itertools import permutations
from collections import Counter, defaultdict


def submasks(mask):
    submask = mask
    while submask:
        yield submask
        submask = (submask - 1) & mask
    yield 0


def cells(mask):
    return tuple(i for i in range(16) if mask >> i & 1)


def rook_adjacent(first, second):
    row, col = divmod(first, 4)
    other_row, other_col = divmod(second, 4)
    return first != second and (row == other_row or col == other_col)


def induced(mask):
    vertices = cells(mask)
    return tuple(tuple(rook_adjacent(a, b) for b in vertices) for a in vertices)


def color_signature(adj):
    """One round of invariant refinement. Distinct colors never get identified."""
    degree = tuple(sum(row) for row in adj)
    return tuple((degree[i], tuple(sorted(degree[j] for j, edge in enumerate(row) if edge)))
                 for i, row in enumerate(adj))


def isomorphism_count(source, target, stop_after_one=False):
    if len(source) != len(target):
        return 0
    source_colors = color_signature(source)
    target_colors = color_signature(target)
    if Counter(source_colors) != Counter(target_colors):
        return 0
    by_color = defaultdict(list)
    for vertex, color in enumerate(target_colors):
        by_color[color].append(vertex)
    order = sorted(range(len(source)), key=lambda v: (len(by_color[source_colors[v]]), -sum(source[v])))
    mapping = {}
    used = set()

    def count(index):
        if index == len(order):
            return 1
        vertex = order[index]
        found = 0
        for image in by_color[source_colors[vertex]]:
            if image in used or any(source[vertex][a] != target[image][b] for a, b in mapping.items()):
                continue
            mapping[vertex] = image
            used.add(image)
            found += count(index + 1)
            used.remove(image)
            del mapping[vertex]
            if found and stop_after_one:
                return 1
        return found

    return count(0)


def host_group():
    lines = tuple(permutations(range(4)))
    for rows in lines:
        for cols in lines:
            yield tuple(4 * rows[i] + cols[j] for i in range(4) for j in range(4))
            yield tuple(4 * cols[j] + rows[i] for i in range(4) for j in range(4))


def main():
    group = tuple(host_group())
    assert len(set(group)) == 1152
    orbit = [-1] * (1 << 16)
    good_auto = {}
    graph_type = {}
    types = defaultdict(list)
    for mask in range(1 << 16):
        if orbit[mask] >= 0:
            continue
        vertices = cells(mask)
        restrictions = set()
        for permutation in group:
            image = tuple(permutation[v] for v in vertices)
            image_mask = sum(1 << v for v in image)
            orbit[image_mask] = mask
            if image_mask == mask:
                restrictions.add(image)
        graph = induced(mask)
        good_auto[mask] = len(restrictions) == isomorphism_count(graph, graph)
        invariant = tuple(sorted(color_signature(graph)))
        for representative, candidate in types[invariant]:
            if isomorphism_count(graph, candidate, stop_after_one=True):
                graph_type[mask] = representative
                break
        else:
            types[invariant].append((mask, graph))
            graph_type[mask] = mask

    def eppa(selection):
        seen = {}
        for submask in submasks(selection):
            representative = orbit[submask]
            if not good_auto[representative]:
                return False
            graph = graph_type[representative]
            if seen.setdefault(graph, representative) != representative:
                return False
        return True

    corner = sum(1 << (4 * i + j) for i in range(3) for j in range(3)) | 1 << 15
    stripe = sum(1 << (4 * i + j) for i in range(4) for j in range(2))
    good_models = {orbit[subset] for model in (corner, stripe) for subset in submasks(model)}
    checked = 0
    successful = Counter()
    for selection in good_auto:
        size = selection.bit_count()
        if size < 8:
            continue
        actual = eppa(selection)
        expected = selection in good_models
        assert actual == expected, (hex(selection), actual, expected)
        checked += 1
        successful[size] += actual
    print(f"R4: checked {checked} host-orbit representatives of order at least eight")
    print(f"Positive orbits by order: {dict(sorted(successful.items()))}")


if __name__ == "__main__":
    main()
