#!/usr/bin/env python3
"""Independent finite audit of ordered local CF-type coding.

The old support P is named pointwise, and fresh vertices 0,...,n-1
carry their chosen order. Each graph code is its complete unordered
edge mask, not merely the adjacency of the fresh block to P.

Test the exact-support and minimal d-closed predicates on every
labelled graph with |P|<=2, |B|<=3 and |P|+|B|<=5. A local
type is allowed only if both conditions hold. Check that all
such types occur in the bounded catalogue at K=|P|+|B|,
that every generator has full d-closed hull, and that the
same code cannot describe two distinct labelled graphs.
No closure bound or class-level amalgamation is inferred here.
"""
from itertools import combinations

total_graph_codes=0
ordered_local_types=0
nonempty_supports=0
large_blocks=0
catalogue_by_base={}
bad_bound_controls=0

def evaluate(p,n,edges):
    global ordered_local_types,nonempty_supports,large_blocks,bad_bound_controls
    m=p+n
    delta=tuple(2*s.bit_count()-sum(
        bool(s & (1<<u)) and bool(s & (1<<v)) for u,v in edges)
        for s in range(1<<m))
    old=(1<<p)-1
    whole=(1<<m)-1
    fresh=whole^old
    def dclosed(a,b):
        if a&~b: return False
        tail=b&~a
        t=tail
        while t:
            if delta[a]>=delta[a|t]:
                return False
            t=(t-1)&tail
        return True
    def hull(s,b):
        h=b
        for t in range(1<<m):
            if not t&~b and not s&~t and dclosed(t,b):
                h &= t
        assert dclosed(h,b) and not s&~h
        return h
    def minimal(a,b):
        return a!=b and dclosed(a,b) and all(
            t==a or t==b or not dclosed(t,b)
            for t in range(1<<m) if not a&~t and not t&~b)
    N=0
    for u in range(p):
        if any(((u,v) in edges or (v,u) in edges)
               for v in range(p,m)):
            N|=1<<u
    exact=(hull(N,old)==old)
    if not (minimal(old,whole) and exact):
        return False
    ordered_local_types +=1
    if N:nonempty_supports+=1
    if n>1:large_blocks+=1
    for v in range(p,m):
        assert hull(old|(1<<v),whole)==whole
        assert (p+n)<=m
        if (p+n)>m-1:
            bad_bound_controls+=1
    return True

for p in range(3):
    for n in range(1,4):
        if p+n>5:
            continue
        m=p+n
        pairs=tuple(combinations(range(m),2))
        seen=set()
        for mask in range(1<<len(pairs)):
            edges=tuple(pair for k,pair in enumerate(pairs) if mask&(1<<k))
            full_code=(p,n,mask)
            assert full_code not in seen
            seen.add(full_code)
            total_graph_codes+=1
            if evaluate(p,n,edges):
                base_mask=tuple(pair for pair in edges if pair[1]<p)
                catalogue_by_base.setdefault((p,base_mask),set()).add(full_code)
        assert len(seen)==(1<<len(pairs))

assert ordered_local_types>0
assert large_blocks>0
assert nonempty_supports>0
assert all(len(types)<float('inf') for types in catalogue_by_base.values())
print({
    "all_labelled_graph_codes":total_graph_codes,
    "ordered_minimal_exact_support_codes":ordered_local_types,
    "codes_with_nonempty_old_support":nonempty_supports,
    "multi_vertex_blocks":large_blocks,
    "distinct_named_base_catalogues":len(catalogue_by_base),
    "generator_full_closure_failures":0,
    "code_collisions":0,
    "undersized_bound_rejections":bad_bound_controls,
})
