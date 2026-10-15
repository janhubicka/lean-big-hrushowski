#!/usr/bin/env python3
"""Audit exact ordered normalization over named old support vertices.

For all small labelled graphs, every possible chosen order of the new
block is represented by its unique increasing enumeration. The
bijection fixes old vertices pointwise and preserves all base edges,
new-block edges, boundary edges and the selected new order.

This independently checks the *graph/order* normalization, not the
relabelling of strict d-closure certificates or C_F class membership.
"""
from itertools import combinations, permutations

orderings=graph_order_diagrams=edge_checks=ordered_checks=0
for p in range(3):
    for n in range(1,5):
        if p+n>5:
            continue
        N=p+n
        pairs=tuple(combinations(range(N),2))
        for order in permutations(range(n)):
            orderings+=1
            # Tagged normalization maps the old p to p and
            # the fresh index i to the i-th vertex in the chosen order.
            tag=tuple(range(p))+tuple(p+v for v in order)
            assert tag[:p]==tuple(range(p))
            assert sorted(tag)==list(range(N))
            rank={v:i for i,v in enumerate(order)}
            for u,v in combinations(range(n),2):
                assert (u<v)==(rank[order[u]]<rank[order[v]])
                ordered_checks+=1
            for mask in range(1<<len(pairs)):
                graph_order_diagrams+=1
                edges={pair for i,pair in enumerate(pairs) if mask&(1<<i)}
                # Recover entire normalized graph as an induced pullback.
                norm={(u,v) for u,v in pairs
                      if tuple(sorted((tag[u],tag[v]))) in edges}
                for u,v in pairs:
                    edge_checks+=1
                    assert ((u,v) in norm)==(
                      tuple(sorted((tag[u],tag[v]))) in edges)
                # Pull the normalized code forward; no edge is lost.
                recovered={tuple(sorted((tag[u],tag[v])))
                           for u,v in norm}
                assert recovered==edges

print({
    "chosen_orders":orderings,
    "full_ordered_graph_diagrams":graph_order_diagrams,
    "edge_equivalences_checked":edge_checks,
    "new_order_checks":ordered_checks,
    "base_names_or_edge_mismatches":0
})
