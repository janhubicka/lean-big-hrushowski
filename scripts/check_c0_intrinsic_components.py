#!/usr/bin/env python3
"""Recover the finite C0 component partition from full unary values.

For every labelled graph on at most four vertices and every assignment
of vertices to one of up to four chronological component positions,
compute the full backward-reachability closure of each vertex.
Check that two vertices have identical values iff their component
indices agree. Group distinct presentations by their complete
unary-function tuples and confirm that each group has one partition
of the vertex set, independent of chronological order.

No two-sparsity or strongness is needed for this identity; it is
caused solely by strict backward orientation of dependencies.
"""
from itertools import combinations, product

def edges_of(n,mask):
    pairs=list(combinations(range(n),2))
    return [p for k,p in enumerate(pairs) if mask>>k&1]

def value_tuple(e,idx,m):
    n=len(idx)
    blocks=[sum(1<<u for u,i in enumerate(idx) if i==j)
            for j in range(m)]
    deps=[set() for _ in range(m)]
    for u,v in e:
        i,j=idx[u],idx[v]
        if i>j:deps[i].add(j)
        elif j>i:deps[j].add(i)
    closure=[]
    for i in range(m):
        reached,queue={i},[i]
        for j in queue:
            for k in deps[j]:
                if k not in reached:
                    reached.add(k);queue.append(k)
        closure.append(sum(blocks[j] for j in reached))
    return tuple(closure[idx[u]] for u in range(n))

graphs=presentations=pairs_checked=coinciding_functions=0
for n in range(5):
    for g in range(1<<(n*(n-1)//2)):
        graphs+=1
        e=edges_of(n,g)
        by_function={}
        for m in range(1,5):
            for idx in product(range(m),repeat=n):
                presentations+=1
                closure=value_tuple(e,idx,m)
                partition=tuple(idx[u]==idx[v] for u in range(n)
                                for v in range(n))
                for u in range(n):
                    for v in range(n):
                        assert (closure[u]==closure[v])==(idx[u]==idx[v]),(
                            "value class mismatch",n,e,idx,u,v)
                        pairs_checked+=1
                if closure in by_function:
                    assert by_function[closure]==partition
                    coinciding_functions+=1
                else:
                    by_function[closure]=partition
assert presentations and pairs_checked and coinciding_functions
print({"labelled_graphs":graphs,"all_component_indexings":presentations,
       "unary_value_pair_checks":pairs_checked,
       "same_function_alternative_indexings":coinciding_functions})
