#!/usr/bin/env python3
"""Check the drawn ambient embeddings against the Lean finite figure masks."""
from __future__ import annotations

import argparse
from hashlib import sha256
from itertools import combinations, permutations
import json
from math import dist
from pathlib import Path
import re

TOLERANCE = 0.01


def ensure(condition, error):
    if not condition:
        raise ValueError(error)


def draw_center(drawing):
    rectangle = drawing["rect"]
    return ((rectangle.x0 + rectangle.x1) / 2,
            (rectangle.y0 + rectangle.y1) / 2)


def black(color):
    return color == (0.0, 0.0, 0.0)


def read_panel(path, n):
    """Read vertex markers and actual line endpoints from the vector paths."""
    try:
        import fitz
    except ImportError as exc:
        raise SystemExit("Reading figure PDFs requires PyMuPDF") from exc

    with fitz.open(path) as pdf:
        ensure(len(pdf) == 1, f"{path.name}: expected a single page")
        drawings = pdf[0].get_drawings()

    allowed_paths = {("c",) * 4, ("l",), ("re",)}
    ensure(all(tuple(item[0] for item in drawing["items"]) in allowed_paths
               for drawing in drawings), f"{path.name}: unrecognized vector path")
    markers = [d for d in drawings if [item[0] for item in d["items"]] == ["c"] * 4]
    ensure(len(markers) == n, f"{path.name}: expected {n} vertex markers")
    points = [draw_center(marker) for marker in markers]
    selected = {index for index, marker in enumerate(markers)
                if black(marker["fill"] if marker["fill"] is not None else marker["color"])}
    # The two stroked central circles terminate their incident strokes at their
    # respective radii. All other vertex markers use the center as the endpoint.
    radii = [marker["rect"].width / 2 if marker["type"] == "s" else 0
             for marker in markers]

    def vertex(point):
        candidates = [i for i, center in enumerate(points)
                      if abs(dist(center, point) - radii[i]) < TOLERANCE]
        ensure(len(candidates) == 1,
               f"{path.name}: endpoint {point} has marker candidates {candidates}")
        return candidates[0]

    edges = set()
    for drawing in drawings:
        items = drawing["items"]
        if len(items) == 1 and items[0][0] == "l":
            a, b = (vertex(point) for point in items[0][1:])
            edge = tuple(sorted((a, b)))
            ensure(a != b and edge not in edges, f"{path.name}: invalid edge {edge}")
            edges.add(edge)
            ensure(black(drawing["color"]) == ({a, b} <= selected),
                   f"{path.name}: edge color does not match selected endpoints {edge}")
    return graph_rows(n, edges), selected


def graph_rows(n, edges):
    rows = [set() for _ in range(n)]
    for a, b in edges:
        rows[a].add(b)
        rows[b].add(a)
    return rows


def clebsch_rows():
    return graph_rows(16, ((a, b) for a, b in combinations(range(16), 2)
                           if a ^ b in (1, 2, 4, 8, 15)))


def schlafli_rows():
    pairs = list(combinations(range(6), 2))

    def adjacent(a, b):
        if a < 12 and b < 12:
            return a // 6 == b // 6 or a % 6 == b % 6
        if a < 12:
            return a % 6 not in pairs[b - 12]
        return len(set(pairs[a - 12]) & set(pairs[b - 12])) == 1

    return graph_rows(27, ((a, b) for a, b in combinations(range(27), 2)
                           if adjacent(a, b)))


def isomorphism(left, right):
    """Find an ambient graph isomorphism by injective induced-map search."""
    if len(left) != len(right) or sorted(map(len, left)) != sorted(map(len, right)):
        return None
    n = len(left)
    image = {}

    def walk(remaining):
        if not remaining:
            return tuple(image[v] for v in range(n))
        unused = set(range(n)) - set(image.values())
        options = {
            v: [w for w in sorted(unused)
                if len(left[v]) == len(right[w])
                and all((u in left[v]) == (x in right[w]) for u, x in image.items())]
            for v in remaining
        }
        source = min(sorted(remaining), key=lambda v: len(options[v]))
        for target in options[source]:
            image[source] = target
            result = walk(remaining - {source})
            if result is not None:
                return result
        image.pop(source, None)
        return None

    return walk(set(range(n)))


def clebsch_group():
    for images in permutations((1, 2, 4, 8, 15)):
        linear = [0] * 16
        for x in range(1, 16):
            low = x & -x
            linear[x] = linear[x - low] ^ images[low.bit_length() - 1]
        for shift in range(16):
            yield tuple(linear[x] ^ shift for x in range(16))


def schlafli_group():
    pairs = list(combinations(range(6), 2))
    index = {pair: i + 12 for i, pair in enumerate(pairs)}
    generators = []
    for i in range(5):
        indices = list(range(6))
        indices[i], indices[i + 1] = indices[i + 1], indices[i]
        generators.append(tuple(indices + [a + 6 for a in indices] +
                                [index[tuple(sorted((indices[a], indices[b])))]
                                 for a, b in pairs]))
    generators.append(tuple(range(6, 12)) + tuple(range(6)) + tuple(range(12, 27)))
    cremona = list(range(27))
    for a, b in [(0, index[1, 2]), (1, index[0, 2]), (2, index[0, 1]),
                 (9, index[4, 5]), (10, index[3, 5]), (11, index[3, 4])]:
        cremona[a], cremona[b] = cremona[b], cremona[a]
    generators.append(tuple(cremona))

    identity = tuple(range(27))
    group = {identity}
    pending = [identity]
    while pending:
        old = pending.pop()
        for generator in generators:
            new = tuple(generator[x] for x in old)
            if new not in group:
                group.add(new)
                pending.append(new)
    return group


def mask_vertices(mask, n):
    return [i for i in range(n) if mask >> i & 1]


def read_lean_masks(path, name, n):
    source = path.read_text()
    match = re.search(rf"def {name}LargeFigures.*?maskVertices {n} '' "
                      r"\{mask \| mask ∈ \(\[([^\]]*)\] : List Nat\)\}",
                      source, flags=re.S)
    ensure(match is not None, f"{path}: cannot identify {name} masks")
    return [int(token.strip(), 0) for token in match[1].split(",")]


FAMILIES = (
    ("clebsch", clebsch_rows, clebsch_group, 5),
    ("schlafli", schlafli_rows, schlafli_group, 14),
)


def adjacency_masks(rows):
    return [sum(1 << v for v in adjacent) for adjacent in rows]


def check_permutation(image, left, right):
    n = len(left)
    if sorted(image) != list(range(n)):
        return False
    return all({image[v] for v in left[u]} == right[image[u]] for u in range(n))


def image_mask(mask, permutation):
    return sum(1 << permutation[v] for v in mask_vertices(mask, len(permutation)))


def generate_panel(path, host, group, expected):
    drawing, selected = read_panel(path, len(host))
    relabel = isomorphism(drawing, host)
    ensure(relabel is not None, f"{path.name}: no isomorphism of the ambient graph")
    selection = sum(1 << v for v in selected)
    relabelled = image_mask(selection, relabel)
    matches = {}
    for permutation in group:
        target = image_mask(relabelled, permutation)
        if target in expected:
            matches.setdefault(target, permutation)
    ensure(len(matches) == 1, f"{path.name}: missing or ambiguous figure orbit")
    representative, normalize = next(iter(matches.items()))
    return {
        "file": path.name,
        "sha256": sha256(path.read_bytes()).hexdigest(),
        "edges": adjacency_masks(drawing),
        "selected": selection,
        "ambient_isomorphism": relabel,
        "host_automorphism": normalize,
        "lean_representative": representative,
    }


def check_panel(record, host, pdf_dir):
    name = record["file"]
    n = len(host)
    ensure(re.fullmatch(r"[0-9a-f]{64}", record["sha256"]) is not None,
           f"{name}: invalid PDF digest")
    edges = record["edges"]
    ensure(len(edges) == n and all(0 <= x < 1 << n for x in edges),
           f"{name}: invalid adjacency masks")
    drawing = [set(mask_vertices(x, n)) for x in edges]
    relabel = record["ambient_isomorphism"]
    normalize = record["host_automorphism"]
    ensure(check_permutation(relabel, drawing, host),
           f"{name}: invalid ambient isomorphism")
    ensure(check_permutation(normalize, host, host),
           f"{name}: invalid host automorphism")
    selected = record["selected"]
    ensure(0 <= selected < 1 << n, f"{name}: invalid selected-vertex mask")
    relabelled = image_mask(selected, relabel)
    ensure(image_mask(relabelled, normalize) == record["lean_representative"],
           f"{name}: ambient isomorphism does not map selection to representative")
    if pdf_dir is not None:
        path = pdf_dir / name
        ensure(sha256(path.read_bytes()).hexdigest() == record["sha256"],
               f"{name}: the PDF hash differs")
        pdf_graph, pdf_selection = read_panel(path, n)
        ensure(adjacency_masks(pdf_graph) == edges
               and selected == sum(1 << v for v in pdf_selection),
               f"{name}: the drawing differs from the manifest")
    return relabelled


def check_manuscript(path, names):
    included_pdfs = re.findall(r"^[^%\n]*?\\includegraphics(?:\[[^]]*\])?"
                              r"\{Pictures/((?:clebsch|schlafli)-\d+\.pdf)\}",
                              path.read_text(), flags=re.M)
    ensure(included_pdfs == names, f"{path.name}: the panel filenames/order differ")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--pdf-dir", type=Path, help="directory of the 19 panel PDFs")
    parser.add_argument("--manuscript", type=Path, help="check the TeX panel filenames")
    parser.add_argument("--write", action="store_true", help="extract a new manifest from PDFs")
    parser.add_argument("--lean-masks", type=Path, default=Path(
        "EPPAIII/Primitive/ClebschSchlafliModels.lean"))
    args = parser.parse_args()
    if args.write and args.pdf_dir is None:
        parser.error("--write requires --pdf-dir")

    all_panels = [] if args.write else json.loads(args.manifest.read_text())
    cursor = 0
    all_names = []
    print("| Panel | Size | Relabelled mask | Lean representative | SHA-256 |")
    print("|---|---:|---:|---:|---|")
    for family, make_host, make_group, count in FAMILIES:
        host = make_host()
        names = [f"{family}-{i}.pdf" for i in range(1, count + 1)]
        all_names.extend(names)
        expected = set(read_lean_masks(args.lean_masks, family, len(host)))
        ensure(len(expected) == count, f"{family}: unexpected number of Lean masks")
        if args.write:
            group = sorted(make_group())
            all_panels.extend(generate_panel(args.pdf_dir / name, host, group, expected)
                              for name in names)
        records = all_panels[cursor:cursor + count]
        cursor += count
        ensure([record["file"] for record in records] == names,
               f"{family}: missing or misordered panel records")
        ensure({record["lean_representative"] for record in records} == expected,
               f"{family}: Lean and manifest representative sets differ")
        for record in records:
            relabelled = check_panel(record, host, args.pdf_dir)
            print(f"| {record['file']} | {record['selected'].bit_count()} | {relabelled} "
                  f"| {record['lean_representative']} | {record['sha256']} |")
    ensure(cursor == len(all_panels), "unexpected additional panels")
    if args.manuscript is not None:
        check_manuscript(args.manuscript, all_names)
    if args.write:
        args.manifest.write_text(json.dumps(all_panels, indent=2) + "\n")


if __name__ == "__main__":
    main()
