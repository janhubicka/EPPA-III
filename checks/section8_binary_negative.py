#!/usr/bin/env python3
"""Independently verify the Section 8 binary finite exclusions."""
from functools import lru_cache
import gzip
from pathlib import Path


MODELS = ("O6+", "NO6+", "O6-", "NO6-")
BASIS_IMAGES = {
    "+": ((8, 62, 42, 47, 2, 14), (62, 14, 54, 45, 28, 33), (10, 2, 4, 3, 27, 32)),
    "-": ((15, 58, 62, 37, 28, 10), (30, 43, 1, 59, 25, 19), (61, 62, 4, 8, 44, 28)),
}
CERTIFICATE = Path(__file__).with_name("section8_binary_negative_certificate.txt.gz")


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def members(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def vertex_mask(vertices):
    result = 0
    for vertex in vertices:
        result |= 1 << vertex
    return result


def quadratic(x, sign):
    b = [(x >> i) & 1 for i in range(6)]
    if sign == "+":
        return (b[0] * b[3] + b[1] * b[4] + b[2] * b[5]) % 2
    return (b[0] * b[2] + b[1] * b[3] + b[4] + b[5] + b[4] * b[5]) % 2


def isometries(sign):
    images = []
    for basis in BASIS_IMAGES[sign]:
        permutation = []
        for x in range(64):
            y = 0
            for i in members(x):
                y ^= basis[i]
            permutation.append(y)
        require(len(set(permutation)) == 64, "A symmetry must be a permutation")
        require(
            all(quadratic(x, sign) == quadratic(y, sign) for x, y in enumerate(permutation)),
            "A symmetry must preserve the quadratic form",
        )
        images.append(tuple(permutation))
    return tuple(images)


class PointModel:
    def __init__(self, name):
        sign = name[-1]
        wanted = int(name.startswith("NO"))
        self.vertices = tuple(x for x in range(1, 64) if quadratic(x, sign) == wanted)
        self.full = vertex_mask(self.vertices)
        self.order = len(self.vertices)
        self.generators = isometries(sign)
        self.adjacency = {
            x: vertex_mask(
                y for y in self.vertices
                if x != y and quadratic(x ^ y, sign) == (quadratic(x, sign) ^ quadratic(y, sign))
            )
            for x in self.vertices
        }
        self.distinct_nonneighbors = {
            x: self.full & ~(self.adjacency[x] | (1 << x)) for x in self.vertices
        }

    @lru_cache(maxsize=None)
    def parity_even(self, selected):
        return all((selected & row).bit_count() % 2 == 0 for row in self.distinct_nonneighbors.values())

    @lru_cache(maxsize=None)
    def shape(self, selected):
        vertices = tuple(members(selected))
        return tuple(
            vertex_mask(i for i, y in enumerate(vertices) if self.adjacency[x] & (1 << y))
            for x in vertices
        )


@lru_cache(maxsize=None)
def same_induced_graph(left, right):
    if len(left) != len(right):
        return False
    n = len(left)
    degrees = tuple(row.bit_count() for row in right)

    def search(image, unused):
        i = len(image)
        if i == n:
            return True
        for j in members(unused):
            if left[i].bit_count() != degrees[j]:
                continue
            if any(
                bool(left[i] & (1 << k)) != bool(right[j] & (1 << mapped))
                for k, mapped in enumerate(image)
            ):
                continue
            if search((*image, j), unused ^ (1 << j)):
                return True
        return False

    return search((), (1 << n) - 1)


def apply_permutation(mask, permutation):
    return vertex_mask(permutation[x] for x in members(mask))


def verify_point(case, certificate):
    require(next(certificate) == ["case", case], f"Missing point case {case}")
    model = PointModel(case)
    previous = {0}
    finals = {}
    counts = {"keep": 0, "move": 0, "fail": 0}
    for size in range(1, 18):
        require(next(certificate) == ["level", str(size)], f"Missing level {size}")
        required_extensions = {
            parent | (1 << x) for parent in previous for x in members(model.full & ~parent)
        }
        kept = set()
        while True:
            items = next(certificate)
            action = items[0]
            if action in ("end", "level"):
                break
            require(action in counts, f"Unknown certificate action {action}")
            require(len(items) == (2 if action == "keep" else 4), "Malformed rule")
            extension = int(items[1], 16)
            require(extension in required_extensions, "Unexpected or repeated extension")
            required_extensions.remove(extension)
            counts[action] += 1
            if action == "keep":
                kept.add(extension)
            elif action == "move":
                origin = int(items[2], 16)
                require(origin in kept, "Orbit representative must occur earlier in the layer")
                image = origin
                for index in items[3] if items[3] != "-" else "":
                    image = apply_permutation(image, model.generators[int(index)])
                require(image == extension, "The orbit word has the wrong image")
            else:
                even, odd = (int(mask, 16) for mask in items[2:])
                require((even | odd) & ~extension == 0, "Witnesses must lie in the selected subgraph")
                require(model.parity_even(even) and not model.parity_even(odd), "The parity invariant agrees")
                require(same_induced_graph(model.shape(even), model.shape(odd)), "Witnesses are not isomorphic")
        require(not required_extensions, "Some one-point extensions lack certificates")
        if size >= 15:
            finals[size] = kept
        if size < 17:
            require(items == ["level", str(size + 1)], "Unexpected end of point case")
            certificate.push(items)
        else:
            require(items == ["end"] and not kept, "An order-17 representative survived")
        previous = kept
    print(f"{case} order {model.order}: κ≤16 via {sum(counts.values()):,} rules, "
          f"{counts['fail']:,} explicit obstructions")
    return finals, model.generators


class BufferedRows:
    def __init__(self, stream):
        self.rows = (line.split() for line in stream if line.strip() and not line.startswith("#"))
        self.pending = None

    def __next__(self):
        if self.pending is None:
            return next(self.rows)
        row, self.pending = self.pending, None
        return row

    def push(self, row):
        require(self.pending is None, "Unexpected parser lookahead")
        self.pending = row


def orbit(seeds, generators):
    reached = set(seeds)
    frontier = list(seeds)
    for selected in frontier:
        for permutation in generators:
            image = apply_permutation(selected, permutation)
            if image not in reached:
                reached.add(image)
                frontier.append(image)
    return reached


def verify_affine(sign, point_results):
    local, generators = point_results["O6" + sign]
    nonlocal_reps, _ = point_results["NO6" + sign]
    adjacency = tuple(
        vertex_mask(y for y in range(64) if x != y and quadratic(x ^ y, sign) == 0)
        for x in range(64)
    )
    checked = 0
    for local_size in (15, 16):
        all_nonlocal = orbit(nonlocal_reps[31 - local_size], generators)
        for a in local[local_size]:
            for b in all_nonlocal:
                selected = a | b | 1
                require(selected.bit_count() == 32, "Rooted candidate has the wrong order")
                require(
                    any(not 15 <= (adjacency[x] & selected).bit_count() <= 16 for x in members(selected)),
                    "A rooted order-32 candidate survived the degree test",
                )
                checked += 1
    print(f"VO6{sign} order 64: κ≤31 via {checked:,} rooted cases")


def main():
    with gzip.open(CERTIFICATE, "rt", encoding="ascii") as stream:
        certificate = BufferedRows(stream)
        point_results = {case: verify_point(case, certificate) for case in MODELS}
        require(next(certificate, None) is None, "Trailing certificate data")
    for sign in ("+", "-"):
        verify_affine(sign, point_results)


if __name__ == "__main__":
    main()
