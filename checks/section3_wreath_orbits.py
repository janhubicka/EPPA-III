"""Independent exhaustive check of Aut(sK_t)=S_t wr S_s orbits.

Generate orbits using adjacent block swaps and adjacent swaps inside
each block, rather than assuming the combinatorial orbit formula.
Check all profiles on s*t <= 12 points, the closed cardinal formula,
and the Claim 3.9 lower bounds. Uses Python standard library only.
"""
from collections import Counter
from math import comb, factorial


def generators(s, t):
    moves = []
    for i in range(s - 1):
        perm = list(range(s * t))
        for a in range(t):
            x, y = i * t + a, (i + 1) * t + a
            perm[x], perm[y] = perm[y], perm[x]
        moves.append(tuple(perm))
    for i in range(s):
        for a in range(t - 1):
            perm = list(range(s * t))
            x, y = i * t + a, i * t + a + 1
            perm[x], perm[y] = perm[y], perm[x]
            moves.append(tuple(perm))
    return moves


def apply_to_mask(mask, perm):
    result = 0
    for old, new in enumerate(perm):
        if mask >> old & 1:
            result |= 1 << new
    return result


def profile_sizes(mask, s, t):
    return [((mask >> (i * t)) & ((1 << t) - 1)).bit_count()
            for i in range(s)]


def expected_orbit_size(s, t, sizes):
    counts = Counter(sizes)
    result = factorial(s)
    for multiplicity in counts.values():
        result //= factorial(multiplicity)
    for k in sizes:
        result *= comb(t, k)
    return result


def main():
    orbit_count = profile_count = partial_checks = 0
    for s in range(1, 7):
        for t in range(2, 7):
            if s * t > 12:
                continue
            moves = generators(s, t)
            unseen = set(range(1 << (s * t)))
            while unseen:
                seed = min(unseen)
                orbit = {seed}
                todo = [seed]
                while todo:
                    old = todo.pop()
                    for move in moves:
                        new = apply_to_mask(old, move)
                        if new not in orbit:
                            orbit.add(new)
                            todo.append(new)
                assert orbit <= unseen
                unseen -= orbit
                orbit_count += 1
                profile_count += len(orbit)
                sizes = profile_sizes(seed, s, t)
                expected = expected_orbit_size(s, t, sizes)
                assert len(orbit) == expected, (s, t, sizes, len(orbit), expected)
                for k in range(1, t):
                    r = sizes.count(k)
                    if r == 0:
                        continue
                    partial_checks += 1
                    bound = comb(s, r) * comb(t, k) ** r
                    assert len(orbit) >= bound, (s, t, sizes, k, r)
                    assert bound >= s * comb(t, k), (s, t, sizes, k, r)
                    if len(orbit) <= s * t:
                        assert k in (1, t - 1)
                        assert r == 1 or (s, t, r, k) == (2, 2, 2, 1)
    assert (orbit_count, profile_count, partial_checks) == (269, 19724, 257)
    print("WREATH ORBITS PASS: 269 orbits, 19,724 profiles, 257 partial checks")


if __name__ == "__main__":
    main()
