#!/usr/bin/env python3
"""Finite regression for the named unequal-clique Taylor host.

For G=K_a disjoint union K_b the Taylor inter-fibre pattern (with an
optional matching between mates) is two K_{a+b}'s, optionally joined by
the canonical perfect matching. This is a finite check; the proof for
all a,b is in validation/section6-sophia-review-2026-10-17.md.
"""


def component(x: int, a: int) -> int:
    return int(x >= a)


def taylor_adj(u: tuple[int, int], v: tuple[int, int],
               a: int, mate: bool) -> bool:
    layer_u, x = u
    layer_v, y = v
    if u == v:
        return False
    if layer_u == layer_v:
        return x != y and component(x, a) == component(y, a)
    return (x != y and component(x, a) != component(y, a)) or (
        x == y and mate
    )


def named_adj(u: tuple[int, int], v: tuple[int, int],
              a: int, mate: bool) -> bool:
    layer_u, x = u
    layer_v, y = v
    half_u = layer_u ^ component(x, a)
    half_v = layer_v ^ component(y, a)
    return (u != v and half_u == half_v) or (
        half_u != half_v and x == y and mate
    )


def run() -> None:
    tested = 0
    for a in range(1, 11):
        for b in range(1, 11):
            n = a + b
            vertices = [(layer, x) for layer in (0, 1) for x in range(n)]
            for mate in (False, True):
                for u in vertices:
                    for v in vertices:
                        assert taylor_adj(u, v, a, mate) == named_adj(
                            u, v, a, mate
                        ), (a, b, mate, u, v)
                        tested += 1
                # Mate-free is a cluster graph; the mate-present host
                # contains the induced P3: (1,a0) -- (0,a0) -- (1,b0).
                x, y = (1, 0), (0, 0)
                z = (1, a)
                if mate:
                    assert taylor_adj(x, y, a, mate)
                    assert taylor_adj(y, z, a, mate)
                    assert not taylor_adj(x, z, a, mate)
                else:
                    assert not taylor_adj(x, y, a, mate)
    assert tested == 110_000, tested
    print(f"Unequal clique Taylor naming PASS: {tested} ordered pairs")


if __name__ == "__main__":
    run()
