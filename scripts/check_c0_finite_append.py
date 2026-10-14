#!/usr/bin/env python3
"""Finite C0 appends: exact old stages and complete unary values.

Check all simple graphs on at most four vertices, all old vertex
subsets, and all old chronological index assignments using up to
three indices. Newly appended vertices all receive the final index.
Every old unary value and every old prefix stays literally unchanged,
regardless of the new edges. When the old and new inclusions are
minimal strong (allowing empty old positions), the full extended
index is again a minimal strong block presentation.

Inducedness of the old graph and putting new vertices *last* are both
necessary; explicit two-vertex counterexamples are tested.
"""
from itertools import combinations, product

def edges_of(n,bits):
    pairs = list(combinations(range(n),2))
    return [e for i,e in enumerate(pairs) if bits & (1<<i)]

def delta(edges,subset):
    return 2*subset.bit_count()-sum(
        bool(subset&(1<<u)) and bool(subset&(1<<v)) for u,v in edges)

def strong(edges,a,b):
    if a & ~b: return False
    rest=t=b&~a
    while True:
        if delta(edges,a)>delta(edges,a|t): return False
        if t==0: return True
        t=(t-1)&rest

def minimal(edges,a,b):
    if a==b or not strong(edges,a,b): return False
    rest=t=b&~a
    while True:
        c=a|t
        if c not in (a,b) and strong(edges,c,b): return False
        if t==0: return True
        t=(t-1)&rest

def unary(edges,labels,selected,nb_indices):
    blocks=[sum(1<<v for v in range(len(labels))
                if selected&(1<<v) and labels[v]==i)
            for i in range(nb_indices)]
    deps=[set() for _ in blocks]
    for u,v in edges:
        if not (selected&(1<<u) and selected&(1<<v)): continue
        i,j=labels[u],labels[v]
        if i>j: deps[i].add(j)
        elif j>i: deps[j].add(i)
    values=[0]*nb_indices
    for i in range(nb_indices):
        reached,queue={i},[i]
        for j in queue:
            for k in deps[j]:
                if k not in reached:
                    reached.add(k);queue.append(k)
        for j in reached:
            values[i]|=blocks[j]
    return values

graphs=append_diagrams=old_value_equalities=old_stage_equalities=strong_extension_presentations=0
for n in range(5):
    full=(1<<n)-1
    for bits in range(1 << (n*(n-1)//2)):
        edges=edges_of(n,bits)
        graphs+=1
        for old in range(1<<n):
            old_vertices=[v for v in range(n) if old&(1<<v)]
            for m in range(4):
                if m==0 and old_vertices: continue
                for assignment in product(range(m),repeat=len(old_vertices)):
                    labels=[m]*n
                    for v,i in zip(old_vertices,assignment):
                        labels[v]=i
                    old_values=unary(edges,labels,old,m)
                    final_values=unary(edges,labels,full,m+1)
                    append_diagrams+=1
                    for k in range(m+1):
                        old_stage=sum(1<<v for v in old_vertices if labels[v]<k)
                        final_stage=sum(1<<v for v in range(n) if labels[v]<k)
                        assert old_stage==final_stage
                        old_stage_equalities+=1
                    assert sum(1<<v for v in range(n) if labels[v]<m)==old
                    for v in old_vertices:
                        assert old_values[labels[v]]==final_values[labels[v]]
                        old_value_equalities+=1
                    old_stages=[sum(1<<v for v in old_vertices if labels[v]<k)
                                for k in range(m+1)]
                    if all(a==b or minimal(edges,a,b)
                           for a,b in zip(old_stages,old_stages[1:])) \
                       and minimal(edges,old,full):
                        full_stages=old_stages+[full]
                        assert all(a==b or minimal(edges,a,b)
                                   for a,b in zip(full_stages,full_stages[1:]))
                        strong_extension_presentations+=1

# Adding an edge between OLD vertices changes an old unary value.
no_edges=[]
new_old_edge=[(0,1)]
labels=[0,1,2]
old=0b011
assert unary(no_edges,labels,old,2)[1]==0b010
assert unary(new_old_edge,labels,0b111,3)[1]==0b011
# Giving a NEW vertex an earlier index is another failure mode.
labels_wrong=[1,0]
assert unary([], [1,1],0b01,2)[1]==0b01
assert unary([(0,1)], labels_wrong,0b11,2)[1]==0b11
print({'labelled_graphs':graphs,
       'one_block_append_diagrams':append_diagrams,
       'old_prefix_set_equalities':old_stage_equalities,
       'complete_old_unary_value_equalities':old_value_equalities,
       'minimal_strong_appends':strong_extension_presentations,
       'two_missing_hypothesis_counterexamples':2})
