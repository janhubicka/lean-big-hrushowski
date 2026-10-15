#!/usr/bin/env python3
"""Bounded adversarial test of the canonical finite CF local support.

For every labelled graph on at most five vertices and every division
into an old A and a new B, check the conclusion whenever A <_d A∪B
is a minimal strict d-closed step. The support is the least d-closed
subset of A containing all old neighbours of B.

Test P<_d P∪B, P∪B≤d A∪B and cl^d_P(N)=P, not merely the
endpoint predimension inequality.
"""
from functools import lru_cache
from itertools import combinations

graphs = cases = minimal_cases = nontrivial_supports = 0

def run_graph(n, E):
    global cases, minimal_cases, nontrivial_supports
    allv = (1 << n)-1
    delta = tuple(2*s.bit_count()-sum(
        bool(s & (1<<u)) and bool(s & (1<<v)) for u,v in E)
        for s in range(1<<n))

    @lru_cache(None)
    def dclosed(a,b):
        if a & ~b: return False
        tail = b & ~a
        t = tail
        while t:
            if delta[a] >= delta[a|t]:
                return False
            t = (t-1)&tail
        return True

    @lru_cache(None)
    def hull(s,ambient):
        assert not s & ~ambient
        h = ambient
        for c in range(1<<n):
            if c & ~ambient == 0 and s & ~c == 0 and dclosed(c,ambient):
                h &= c
        assert dclosed(h,ambient)
        assert not s & ~h
        return h

    def minimal(a,b):
        if a==b or not dclosed(a,b):
            return False
        return all(c==a or c==b or not dclosed(c,b)
                   for c in range(1<<n)
                   if a & ~c == 0 and c & ~b == 0)

    for A in range(1<<n):
        B=allv & ~A
        cases+=1
        if not minimal(A,allv):
            continue
        minimal_cases+=1
        N=sum(1<<v for v in range(n)
              if (A>>v)&1 and any(
                  ((B>>u)&1 and ((u,v) in E or (v,u) in E))
                  for u in range(n)))
        P=hull(N,A)
        if P:
            nontrivial_supports+=1
        assert dclosed(P,A)
        assert minimal(P,P|B)
        assert dclosed(P|B,allv)
        assert hull(N,P)==P

for n in range(6):
    possibilities=tuple(combinations(range(n),2))
    for mask in range(1<<len(possibilities)):
        E=tuple(pair for j,pair in enumerate(possibilities)
                if mask & (1<<j))
        graphs+=1
        run_graph(n,E)

# K4 gives a four-point minimal d-closed block over the empty support.
K4=tuple(combinations(range(4),2))
delta=lambda s:2*s.bit_count()-sum(
    bool(s & (1<<u)) and bool(s & (1<<v)) for u,v in K4)
assert delta(15)>delta(0)
assert all(delta(t)>delta(0) for t in range(1,16))

print({
    "graphs_checked":graphs,
    "old_new_partitions_checked":cases,
    "minimal_dclosed_extensions":minimal_cases,
    "nonempty_canonical_supports":nontrivial_supports,
    "canonical_support_mismatches":0,
    "K4_four_vertex_minimal_block":True
})
