#!/usr/bin/env python3
"""Finite checks for the 2026-11-04 factorial/halved q=2 validation note.
These are regressions, not a proof of the general perfectness result.
No third-party dependencies.
"""
from itertools import combinations
from functools import lru_cache

def cover(s, t, x, y):
    n = 2 * s * t
    def edge(a, b):
        if a == b: return False
        aa, ia, pa = a // (s*t), (a % (s*t)) // t, a % t
        ab, ib, pb = b // (s*t), (b % (s*t)) // t, b % t
        if aa == ab: return ia == ib
        if ia != ib: return y == 1
        return x == "1" or (x == "M" and pa == pb) or (x == "m" and pa != pb)
    return tuple(sum(1 << b for b in range(n) if edge(a, b)) for a in range(n))

def complement(A):
    n=len(A)
    return tuple(((1 << n)-1) ^ (1 << i) ^ a for i, a in enumerate(A))

def odd_hole(A):
    n=len(A)
    for k in range(5,n+1,2):
        for vs in combinations(range(n),k):
            mask=sum(1 << v for v in vs)
            if any((A[v] & mask).bit_count() != 2 for v in vs): continue
            seen=1 << vs[0]
            todo=[vs[0]]
            while todo:
                v=todo.pop()
                rest=(A[v] & mask) & ~seen
                while rest:
                    b=rest & -rest
                    seen |= b
                    todo.append(b.bit_length()-1)
                    rest &= rest-1
            if seen == mask: return vs
    return None

def alpha_omega_fail(A):
    n=len(A)
    B=complement(A)
    def max_clique(neigh):
        @lru_cache(None)
        def go(mask):
            if mask == 0: return 0
            v=(mask & -mask).bit_length()-1
            return max(go(mask & ~(1 << v)),1 + go(mask & neigh[v]))
        return go
    omega=max_clique(A)
    alpha=max_clique(B)
    for mask in range(1 << n):
        if alpha(mask)*omega(mask) < mask.bit_count(): return mask
    return None

def divisors(n):
    return (t for t in range(1,n+1) if n % t == 0)

def halved_q2():
    q=2
    v=(q**4+1)*(q**3+1)*(q**2+1)*(q+1)
    k=q*(q**2+1)*(q**5-1)//(q-1)
    lam=q-1 + q**2*(q+1)*(q**2+q+1)
    mu=k*(k-lam-1)//(v-k-1)
    assert (v,k,lam,mu)==(2295,310,85,35)
    for n,d in [(k,lam),(v-k-1,k-mu)]:
        assert all(d not in (t-1,n-t) for t in divisors(n))
        m=n//2
        for t in divisors(m):
            degrees={t-1,t,2*t-2,2*t-1,m-1,m,m+t-2,m+t-1}
            assert d not in degrees
            assert n-1-d not in degrees
        print("halved q=2, N=%d, degree=%d: excluded" % (n,d))

def main():
    families=[(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),
              (3,1),(3,2),(3,3),(4,1),(4,2)]
    models=0
    subset_checks=0
    for s,t in families:
        for x in ("0","1","M","m"):
            for y in (0,1):
                A=cover(s,t,x,y)
                for G in (A,complement(A)):
                    assert odd_hole(G) is None,(s,t,x,y)
                    if len(G)<=12:
                        assert alpha_omega_fail(G) is None,(s,t,x,y)
                        subset_checks+=1 << len(G)
                models+=1
    print("PASS: %d covers, %d odd-hole/antihole screens, %d alpha*omega checks" %
          (models,2*models,subset_checks))
    halved_q2()
if __name__ == "__main__": main()
