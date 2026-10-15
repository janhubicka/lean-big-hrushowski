#!/usr/bin/env python3
"""Adversarial test of finite strict d-closure under induced injections.

Enumerate finite graph codes, all a⊆b, and arbitrary injective
relabelings into a larger graph containing one extraneous vertex.
Edges to the extraneous vertex vary independently. Verify that
strict d-closedness, minimal steps and least finite hulls coincide
exactly on the induced image interval. No global target d-closedness
is asserted.
"""
from itertools import combinations, permutations
from functools import lru_cache

graph_embeddings=intervals_checked=closed_pairs=minimal_pairs=0
hull_equalities=outside_crossing_cases=0

def predim(n,E):
    return tuple(2*s.bit_count() - sum(
        bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in E)
        for s in range(1<<n))

def checker(n,E):
    delta=predim(n,E)
    @lru_cache(maxsize=None)
    def closed(a,b):
        if a&~b:return False
        t=b&~a
        while t:
            if delta[a]>=delta[a|t]:return False
            t=(t-1)&(b&~a)
        return True
    @lru_cache(maxsize=None)
    def minimal(a,b):
        if a==b or not closed(a,b):return False
        for z in range(1<<n):
            if z!=a and z!=b and not a&~z and not z&~b:
                if closed(z,b):return False
        return True
    @lru_cache(maxsize=None)
    def hull(s,b):
        h=b
        for z in range(1<<n):
            if not s&~z and not z&~b and closed(z,b):
                h&=z
        assert closed(h,b)
        return h
    return closed,minimal,hull

for n in range(5):
    possible=tuple(combinations(range(n),2))
    for code in range(1<<len(possible)):
        E={edge for i,edge in enumerate(possible) if code & (1<<i)}
        old_cl,old_min,old_hull=checker(n,E)
        for emb in permutations(range(n+1),n):
            outsider=next(i for i in range(n+1) if i not in emb)
            for pattern in range(2):
                G={tuple(sorted((emb[u],emb[v]))) for u,v in E}
                for u in range(n):
                    if pattern and u%2==0:
                        G.add(tuple(sorted((emb[u],outsider))))
                new_cl,new_min,new_hull=checker(n+1,G)
                graph_embeddings+=1
                if pattern:outside_crossing_cases+=1
                def image(a):
                    return sum(1<<emb[u] for u in range(n)
                               if a & (1<<u))
                for b in range(1<<n):
                    a=b
                    while True:
                        ib,ia=image(b),image(a)
                        assert old_cl(a,b)==new_cl(ia,ib)
                        assert old_min(a,b)==new_min(ia,ib)
                        assert image(old_hull(a,b))==new_hull(ia,ib)
                        intervals_checked+=1
                        hull_equalities+=1
                        if old_cl(a,b):closed_pairs+=1
                        if old_min(a,b):minimal_pairs+=1
                        if not a:break
                        a=(a-1)&b

assert intervals_checked>100000
assert minimal_pairs>0
assert outside_crossing_cases>0
print({
    "induced_graph_embeddings":graph_embeddings,
    "image_intervals_checked":intervals_checked,
    "strict_dclosed_intervals":closed_pairs,
    "minimal_dclosed_intervals":minimal_pairs,
    "finite_hull_equalities":hull_equalities,
    "boundary_edge_variants":outside_crossing_cases,
    "mismatches":0
})
