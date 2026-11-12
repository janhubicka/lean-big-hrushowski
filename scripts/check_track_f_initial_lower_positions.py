#!/usr/bin/env python3
"""Independent finite verification of fixed-old-position equivalence.

P is an initial segment in both complete orders. Same comparisons
on old vertices then imply they occupy the same numeric positions.
Test all permutations of up to 5 labels, every possible lower set.
"""
from itertools import permutations, combinations


def subsets(points):
    points=tuple(points)
    return (frozenset(x) for k in range(len(points)+1)
            for x in combinations(points,k))


def initial(order, P):
    return tuple(order[:len(P)]) == tuple(x for x in order if x in P)


def test(n):
    orders=list(permutations(range(n)))
    count=0
    for e in orders:
        pe={x:i for i,x in enumerate(e)}
        for u in range(n):
            assert pe[u]==sum(pe[v]<pe[u] for v in range(n))
        for P in subsets(range(n)):
            if set(e[:len(P)]) != P:
                continue
            for f in orders:
                if set(f[:len(P)]) != P:
                    continue
                pf={x:i for i,x in enumerate(f)}
                old_order=all((pe[x]<pe[y])==(pf[x]<pf[y])
                              for x in P for y in P)
                fixed=all(pe[x]==pf[x] for x in P)
                assert old_order == fixed, (e,f,P)
                count+=1
    return count


def negatives():
    # With no initiality assumption, order on a singleton old
    # set is vacuously the same while its position can move.
    e=(0,1,2)
    f=(1,0,2)
    P={0}
    assert all((e.index(x)<e.index(y))==(f.index(x)<f.index(y))
               for x in P for y in P)
    assert e.index(0)!=f.index(0)
    assert set(f[:len(P)])!=P


def main():
    negatives()
    checks=sum(test(n) for n in range(6))
    print(f"PASS: {checks} ordered-initial-prefix pair tests "
          "up to 5 vertices; predecessor-card identities and "
          "non-initial negative control")


if __name__=="__main__":
    main()
