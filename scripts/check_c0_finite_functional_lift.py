#!/usr/bin/env python3
"""Finite C0 canonical expansion across arbitrary strong graph inclusions.

For every simple graph on up to four vertices, every strong old
subset a≤V, and every old finite chronological indexing with empty
or minimal strong steps, extract a literal sequence of minimal strong
fresh blocks and assign each its chronological index after all old
components.

Check that the new indexing is empty/minimal strong at every stage,
that the old part occurs at exactly the previous terminal index,
and that the full set-valued canonical unary function on every old
vertex is unchanged. This checks multi-block extensions, not only
a single final component.
"""
from itertools import combinations, product

def edges_of(n,bits):
    e=list(combinations(range(n),2))
    return [x for j,x in enumerate(e) if bits & (1<<j)]

def delta(edges,s):
    return 2*s.bit_count()-sum(bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in edges)

def strong(edges,a,b):
    if a & ~b:return False
    z=tail=b&~a
    while True:
        if delta(edges,a)>delta(edges,a|z):return False
        if z==0:return True
        z=(z-1)&tail

def minimal(edges,a,b):
    if a==b or not strong(edges,a,b):return False
    z=tail=b&~a
    while True:
        t=a|z
        if t not in (a,b) and strong(edges,t,b):return False
        if z==0:return True
        z=(z-1)&tail

def values(edges,labels,m,selected):
    components=[sum(1<<u for u,i in enumerate(labels)
                 if i==j and selected&(1<<u)) for j in range(m)]
    back=[set() for _ in range(m)]
    for u,v in edges:
        if not (selected&(1<<u) and selected&(1<<v)):continue
        i,j=labels[u],labels[v]
        if i>j:back[i].add(j)
        elif j>i:back[j].add(i)
    vals=[]
    for i in range(m):
        reached,queue={i},[i]
        for k in queue:
            for j in back[k]:
                if j not in reached:reached.add(j);queue.append(j)
        vals.append(sum(components[j] for j in reached))
    return vals

def blocks_from_strong(edges,a,b):
    blocks=[]
    while a!=b:
        possible=[c for c in range(b+1) if c&~b==0 and c&a==a
                  and c!=a and strong(edges,c,b)]
        assert possible
        c=min(possible,key=lambda z:(z.bit_count(),z))
        assert minimal(edges,a,c)
        B=c&~a
        assert B and not (B&a)
        blocks.append(B)
        a=c
    return blocks

graphs=strong_spans=old_presentations=multiblock=old_values=all_stages=0
for nv in range(5):
    full=(1<<nv)-1
    for bits in range(1<<(nv*(nv-1)//2)):
        edges=edges_of(nv,bits)
        graphs+=1
        for a in range(1<<nv):
            if not strong(edges,a,full):continue
            strong_spans+=1
            blocks=blocks_from_strong(edges,a,full)
            multiblock+=len(blocks)>1
            old_vertices=[v for v in range(nv) if a&(1<<v)]
            for m in range(4):
                if not m and old_vertices:continue
                for assignment in product(range(m),repeat=len(old_vertices)):
                    old=[m]*nv
                    for v,k in zip(old_vertices,assignment):old[v]=k
                    stages=[sum(1<<v for v in old_vertices if old[v]<k)
                            for k in range(m+1)]
                    if any(x!=y and not minimal(edges,x,y)
                           for x,y in zip(stages,stages[1:])):
                        continue
                    old_presentations+=1
                    fresh={}
                    for j,B in enumerate(blocks):
                        for v in range(nv):
                            if B&(1<<v):
                                assert v not in fresh
                                fresh[v]=m+j
                    extended=[old[v] if a&(1<<v) else fresh[v]
                              for v in range(nv)]
                    assert all(extended[v]==old[v] for v in old_vertices)
                    assert sum(1<<v for v in range(nv) if extended[v]<m)==a
                    final_stages=[sum(1<<v for v in range(nv) if extended[v]<k)
                                  for k in range(m+len(blocks)+1)]
                    assert final_stages[:m+1]==stages
                    assert final_stages[-1]==full
                    for x,y in zip(final_stages,final_stages[1:]):
                        assert x==y or minimal(edges,x,y), (
                            'not minimal',nv,edges,a,blocks,extended,x,y)
                        all_stages+=1
                    old_values_arr=values(edges,old,m,a)
                    final_values=values(edges,extended,m+len(blocks),full)
                    for v in old_vertices:
                        assert old_values_arr[old[v]]==final_values[extended[v]],(
                            'old unary changed',nv,edges,a,blocks,extended,v)
                        old_values+=1
assert graphs and strong_spans and old_presentations and multiblock and old_values
print({'labelled_graphs':graphs,'strong_graph_spans':strong_spans,
       'canonical_old_presentations':old_presentations,
       'multi_block_extension_spans':multiblock,
       'verified_indexed_steps':all_stages,
       'complete_old_unary_equalities':old_values})
