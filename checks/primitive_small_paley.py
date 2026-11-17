"""Bound EPPA selections in the four explicit small Paley hosts.

Run with ``python3 checks/primitive_small_paley.py``. The proof connecting
rooted colour refinement to EPPA is in validation/primitive/small-paley.md.
"""

from collections import Counter
from itertools import product


PRIME_ORDERS = (17, 37, 41)
HOST_PARAMETERS = {
    17: (8, 3, 4),
    25: (12, 5, 6),
    37: (18, 8, 9),
    41: (20, 9, 10),
}


def paley_graph(order):
    if order in PRIME_ORDERS:
        vertices = tuple(range(order))
        squares = {a * a % order for a in vertices}

        def difference(x, y):
            return (x - y) % order

    elif order == 25:
        vertices = tuple(product(range(5), repeat=2))
        squares = {((a * a + 2 * b * b) % 5, 2 * a * b % 5) for a, b in vertices}

        def difference(x, y):
            return (x[0] - y[0]) % 5, (x[1] - y[1]) % 5

    else:
        raise ValueError(f"Unsupported model order {order}")

    return tuple(
        frozenset(
            j
            for j, y in enumerate(vertices)
            if x != y and (difference(x, y) in squares or difference(y, x) in squares)
        )
        for x in vertices
    )


def check_parameters(graph, order):
    degree, adjacent_common, nonadjacent_common = HOST_PARAMETERS[order]
    if len(graph) != order:
        raise ValueError(f"Incorrect order for Paley({order})")
    for x, neighbors in enumerate(graph):
        if x in neighbors or len(neighbors) != degree:
            raise ValueError((order, x, "incorrect neighborhood"))
        for y, other_neighbors in enumerate(graph):
            if x == y:
                continue
            if (y in neighbors) != (x in other_neighbors):
                raise ValueError((order, x, y, "asymmetric adjacency"))
            expected_common = adjacent_common if y in neighbors else nonadjacent_common
            if len(neighbors & other_neighbors) != expected_common:
                raise ValueError((order, x, y, "incorrect common-neighbor count"))


def color_ids(signatures):
    ids = {}
    return tuple(ids.setdefault(signature, len(ids)) for signature in signatures)


def refine(graph, colors):
    neighbor_counts = (Counter(colors[y] for y in neighbors) for neighbors in graph)
    return color_ids(
        (color, tuple(sorted(counts.items()))) for color, counts in zip(colors, neighbor_counts)
    )


def bound_for_anchors(graph, second):
    first = 0
    profiles = tuple((x in graph[first], x in graph[second]) for x in range(len(graph)))
    colors = color_ids(
        (x == first, x == second, profile) for x, profile in enumerate(profiles)
    )
    while True:
        refined = refine(graph, colors)
        if refined == colors:
            break
        colors = refined

    outside_anchors = (x for x in range(len(graph)) if x != first and x != second)
    class_sizes = Counter((profiles[x], colors[x]) for x in outside_anchors)
    largest_class = {profile: 0 for profile in product((False, True), repeat=2)}
    for (profile, _), size in class_sizes.items():
        largest_class[profile] = max(largest_class[profile], size)
    return max(largest_class.values()), 2 + sum(largest_class.values())


def main():
    for order in sorted(HOST_PARAMETERS):
        graph = paley_graph(order)
        check_parameters(graph, order)
        anchor_bounds = Counter(bound_for_anchors(graph, b) for b in range(1, order))
        largest_class = max(size for size, _ in anchor_bounds)
        selection_bound = max(bound for _, bound in anchor_bounds)
        if 2 * selection_bound >= order:
            raise ValueError((order, anchor_bounds, "refinement does not exclude EPPA at half order"))
        print(
            f"Paley({order}): {sum(anchor_bounds.values())} second anchors, "
            f"largest final class {largest_class}, EPPA order at most {selection_bound}"
        )


if __name__ == "__main__":
    main()
