#!/usr/bin/env python3
"""Old C0 unary values persist across arbitrary appended finite components.

For all labelled simple graphs on at most four vertices and all
chronological component-index assignments (up to four positions),
verify that every canonical dependency ancestor of a vertex in A_k
also lies in A_k. Recompute the full set-valued unary function in
the induced prefix using the same index labels and check exact
equality with the function in the final graph.

No strongness or minimality is assumed here, so the test isolates
the purely combinatorial temporal persistence statement.
"""
from itertools import combinations, product

def edges_of(n, bits):
    pairs=list(combinations(range(n),2))
    return [p for k,p in enumerate(pairs) if bits & (1<<k)]

def canonical_values(edges, labels, m, selected):
    blocks=[sum(1<<u for u,i in enumerate(labels)
                if i==k and selected&(1<<u)) for k in range(m)]
    deps=[set() for _ in range(m)]
    for u,v in edges:
        if not (selected&(1<<u) and selected&(1<<v)):
            continue
        i,j=labels[u],labels[v]
        if i>j: deps[i].add(j)
        elif j>i: deps[j].add(i)
    values=[]
    for root in range(m):
        reached,queue={root},[root]
        for i in queue:
            for j in deps[i]:
                if j not in reached:
                    reached.add(j);queue.append(j)
        value=0
        for j in reached: value |= blocks[j]
        values.append(value)
    return values

graphs=indexings=prefixes=unary_equalities=0
for n in range(5):
    full=(1<<n)-1
    for bits in range(1 << (n*(n-1)//2)):
        edges=edges_of(n,bits);graphs+=1
        for m in range(1,5):
            for labels in product(range(m),repeat=n):
                indexings+=1
                original=canonical_values(edges,labels,m,full)
                for k in range(m+1):
                    old=sum(1<<u for u,i in enumerate(labels) if i<k)
                    restricted=canonical_values(edges,labels,m,old)
                    prefixes+=1
                    for u in range(n):
                        if not old&(1<<u): continue
                        assert original[labels[u]] & ~old == 0, (
                            "new ancestor",n,labels,edges,k,u)
                        assert original[labels[u]] == restricted[labels[u]], (
                            "old unary changed",n,labels,edges,k,u)
                        unary_equalities+=1
assert all(z>0 for z in [indexings,prefixes,unary_equalities])
print({"labelled_graphs":graphs,
       "arbitrary_component_indexings":indexings,
       "induced_prefixes":prefixes,
       "old_unary_value_equalities":unary_equalities})
