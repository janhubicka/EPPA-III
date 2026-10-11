#!/usr/bin/env python3
"""Exhaust the size histograms behind the two-partial-coordinate lemma.

No external dependencies. This is a finite corroboration, not a proof
of the unrestricted wreath-product orbit-size formula or EPPA statement.
"""
from collections import Counter
from itertools import combinations_with_replacement
from math import comb, factorial, prod


def orbit_size(s: int, t: int, sizes: tuple[int, ...]) -> int:
    hist = Counter(sizes)
    coefficient = factorial(s) // prod(factorial(c) for c in hist.values())
    return coefficient * prod(comb(t, k) ** c for k, c in hist.items())


def main() -> None:
    examined = 0
    multiple = 0
    mixed = 0
    short = []
    for s in range(2, 16):
        for t in range(2, 16):
            if s * t > 30:
                continue
            for sizes in combinations_with_replacement(range(t + 1), s):
                examined += 1
                p = sum(0 < k < t for k in sizes)
                if p < 2:
                    continue
                multiple += 1
                orbit = orbit_size(s, t, sizes)
                if 1 in sizes and t - 1 in sizes and t >= 3:
                    mixed += 1
                    assert orbit > s * t, (s, t, sizes, orbit)
                if orbit <= s * t:
                    short.append((s, t, sizes, orbit))
    assert short == [(2, 2, (1, 1), 4)], short
    print(f"Short-profile check: {examined} size histograms, "
          f"{multiple} with >=2 partial coordinates, "
          f"{mixed} mixed types; unique exception (2,2,(1,1)).")


if __name__ == "__main__":
    main()
