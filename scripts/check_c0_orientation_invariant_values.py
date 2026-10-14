#!/usr/bin/env python3
"""Canonical C0 unary values are invariant under compatible component orders.

Across every graph on ≤4 vertices and every assignment of component
positions from {0,...,m-1} with m≤4, group chronological presentations
by their component partition and the orientation of each edge joining
distinct components. Within each group, all complete vertex-valued
backward dependency closures must be identical.

The checker also exhibits failures when either the common partition
or graph-edge orientation hypothesis is omitted.
"""
from itertools import combinations, product

def edges_of(n, bits):
    edges=list(combinations(range(n),2))
    return [p for k,p in enumerate(edges) if bits & (1<<k)]

def values(edges, ind, m):
    components=[sum(1<<u for u in range(len(ind)) if ind[u]==j)
                for j in range(m)]
    deps=[set() for _ in range(m)]
    for u,v in edges:
        i,j=ind[u],ind[v]
        if i>j: deps[i].add(j)
        elif j>i: deps[j].add(i)
    out=[]
    for i in range(m):
        reach,queue={i},[i]
        for j in queue:
            for k in deps[j]:
                if k not in reach: reach.add(k);queue.append(k)
        out.append(sum(components[j] for j in reach))
    return tuple(out[ind[u]] for u in range(len(ind)))

graphs=presentations=compatible_pairs=alternative_orders=0
for n in range(5):
    pairs=list(combinations(range(n),2))
    for mask in range(1 << len(pairs)):
        graphs+=1
        E=edges_of(n,mask)
        partitions={}
        for m in range(1,5):
            for ind in product(range(m),repeat=n):
                presentations+=1
                part=tuple(ind[u]==ind[v] for u in range(n)
                           for v in range(n))
                edge_dirs=tuple((ind[u]<ind[v],ind[v]<ind[u])
                                for u,v in E)
                key=(part,edge_dirs)
                val=values(E,ind,m)
                if key in partitions:
                    previous,index=partitions[key]
                    assert previous==val,(
                        "orientation-preserving order changed C0 value",
                        E,index,ind,previous,val)
                    compatible_pairs+=1
                    alternative_orders+=index!=ind
                else:
                    partitions[key]=(val,ind)

# Same components, reversed direction of an edge changes its closure.
assert values([(0,1)],(0,1),2)!=values([(0,1)],(1,0),2)
# Same oriented edge data (empty), different partitions changes closure.
assert values([], (0,0), 1)!=values([], (0,1), 2)
assert compatible_pairs>0 and alternative_orders>0
print({"labelled_graphs":graphs,"chronological_presentations":presentations,
       "compatible_order_pairs":compatible_pairs,
       "nonidentical_compatible_indexings":alternative_orders,
       "missing_partition_and_orientation_counterexamples":2})
