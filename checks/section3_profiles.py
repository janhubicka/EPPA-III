"""Exact finite orbit-size audit for neighbourhood profiles under S_t wr S_s.

For each s,t>=2 with st<=14, enumerate every subset of sK_t.
For each profile compute its orbit size via the wreath-product formula.
If the orbit fits into the complementary half (at most st vertices),
verify the precise classification used in partition-half-lemma.tex.
This is a finite check, not a substitute for the general counting proof.
"""
from collections import Counter
from math import factorial, comb


def orbit_size(s, t, profile_sizes):
    counts = Counter(profile_sizes)
    orbit = factorial(s)
    for amount in counts.values():
        orbit //= factorial(amount)
    for k in profile_sizes:
        orbit *= comb(t, k)
    return orbit


def main():
    tested = accepted = 0
    types = {}
    for s in range(2, 9):
        for t in range(2, 8):
            n = s * t
            if n > 14:
                continue
            for mask in range(1 << n):
                sizes = tuple(sum((mask >> (i*t+j)) & 1 for j in range(t))
                              for i in range(s))
                orbit = orbit_size(s, t, sizes)
                p = sum(0 < k < t for k in sizes)
                tested += 1
                if orbit > n:
                    continue
                accepted += 1
                if p == 0:
                    kind = 'whole cliques'
                elif p == 1:
                    kind = 'single partial'
                    k = next(k for k in sizes if 0 < k < t)
                    assert k in (1, t-1) and orbit == n, (s,t,sizes,orbit)
                    assert len(set(k for k in sizes if k in (0,t))) <= 1, (s,t,sizes)
                else:
                    kind = 'exceptional square'
                    assert (s,t,p,orbit) == (2,2,2,4), (s,t,sizes,orbit)
                types[kind] = types.get(kind,0) + 1
    print('Profile subsets examined:', tested)
    print('Orbit-size-at-most-half cases:', accepted)
    print('Types:', types)
    assert tested == 52368 and accepted == 586
    assert types == {
        'whole cliques':142,
        'single partial':440,
        'exceptional square':4,
    }
    print('SECTION 3 PROFILE ORBIT CLASSIFICATION PASS')


if __name__ == '__main__':
    main()
