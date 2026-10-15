#!/usr/bin/env python3
"""Audit intrinsic CF old-neighbour support under induced relabellings.

Enumerate every small graph G on n<=4 vertices, every partition
into old A and fresh B, and all injections into n+1 vertices.
The extra target vertex has separately chosen boundary edges.
Check both exact old-neighbour images and their finite strict
d-closed hull images. The result compares only induced image
ambient structures, not closure in the entire larger target.
"""
from itertools import combinations, permutations
from functools import lru_cache

cases=neighbor_images=hull_images=external_edge_cases=0

def delta(n,edges):
    return tuple(2*s.bit_count()-sum(
        bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in edges)
        for s in range(1<<n))

def hull_function(n,edges):
    d=delta(n,edges)
    @lru_cache(None)
    def closed(a,b):
        if a&~b:return False
        tail=b&~a
        t=tail
        while t:
            if d[a]>=d[a|t]:return False
            t=(t-1)&tail
        return True
    @lru_cache(None)
    def hull(a,b):
        h=b
        for t in range(1<<n):
            if not a&~t and not t&~b and closed(t,b):
                h&=t
        return h
    return hull

for n in range(5):
    pairs=tuple(combinations(range(n),2))
    for graph_code in range(1<<len(pairs)):
        E={e for i,e in enumerate(pairs) if graph_code&(1<<i)}
        old_hull=hull_function(n,E)
        for emb in permutations(range(n+1),n):
            outsider=next(i for i in range(n+1) if i not in emb)
            for pattern in range(2):
                G={tuple(sorted((emb[u],emb[v]))) for u,v in E}
                for u in range(n):
                    if pattern and not u%2:
                        G.add(tuple(sorted((emb[u],outsider))))
                if pattern:external_edge_cases+=1
                new_hull=hull_function(n+1,G)
                def image(s):
                    return sum(1<<emb[x] for x in range(n)
                               if s&(1<<x))
                def neighbors(edges,A,B,n):
                    return sum(1<<a for a in range(n)
                               if A&(1<<a) and any(
                                   B&(1<<b) and
                                   tuple(sorted((a,b))) in edges
                                   for b in range(n)))
                for A in range(1<<n):
                    B=((1<<n)-1)&~A
                    N=neighbors(E,A,B,n)
                    Aimg,Bimg=image(A),image(B)
                    Nimg=neighbors(G,Aimg,Bimg,n+1)
                    assert image(N)==Nimg
                    neighbor_images+=1
                    assert image(old_hull(N,A))==new_hull(Nimg,Aimg)
                    hull_images+=1
                    cases+=1

assert hull_images>100000
print({
    "small_induced_support_diagrams":cases,
    "exact_old_neighbour_images":neighbor_images,
    "exact_dclosed_support_images":hull_images,
    "target_extra_edge_variants":external_edge_cases,
    "support_image_mismatches":0
})
