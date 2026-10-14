#!/usr/bin/env python3
"""Exhaustive finite audit: interchange of independent minimal blocks.

For every labelled graph on at most five vertices and every assignment
of vertices to disjoint old/new block sets A,B,C (unassigned vertices
may remain outside their union), check:

If A<A∪B<A∪B∪C are minimal strong steps and no edge connects B,C,
then A<A∪C<A∪C∪B are minimal strong.

The complete graph K4 supplies a counterexample to omitting the
no-edge hypothesis: ∅<{0}<K4 is a pair of minimal strong steps,
but the 3-vertex complementary triangle is not minimal over ∅.
"""
from itertools import combinations, product

def edges_of(n,mask):
    return [e for k,e in enumerate(combinations(range(n),2))
            if mask>>k&1]

def delta(edges,s):
    return 2*s.bit_count()-sum(bool(s&(1<<u)) and bool(s&(1<<v))
        for u,v in edges)

def strong(edges,a,b):
    if a & ~b:return False
    t=rest=b&~a
    while True:
        if delta(edges,a)>delta(edges,a|t):return False
        if not t:return True
        t=(t-1)&rest

def minimal(edges,a,b):
    if a==b or not strong(edges,a,b):return False
    t=rest=b&~a
    while True:
        x=a|t
        if x not in (a,b) and strong(edges,x,b):return False
        if not t:return True
        t=(t-1)&rest

graphs=independent_swaps=nontrivial_middle=0
for n in range(6):
    for mask in range(1<<(n*(n-1)//2)):
        edges=edges_of(n,mask)
        graphs+=1
        for labels in product(range(4),repeat=n):
            a=sum(1<<v for v,t in enumerate(labels) if t==0)
            b=sum(1<<v for v,t in enumerate(labels) if t==1)
            c=sum(1<<v for v,t in enumerate(labels) if t==2)
            if not b or not c:continue
            if any(((b>>u&1) and (c>>v&1)) or
                   ((c>>u&1) and (b>>v&1)) for u,v in edges):
                continue
            if not minimal(edges,a,a|b):continue
            if not minimal(edges,a|b,a|b|c):continue
            assert minimal(edges,a,a|c),("first step",n,edges,a,b,c)
            assert minimal(edges,a|c,a|b|c),("second step",n,edges,a,b,c)
            independent_swaps+=1
            nontrivial_middle+=b.bit_count()+c.bit_count()>2

k4=list(combinations(range(4),2))
assert minimal(k4,0,1)
assert minimal(k4,1,15)
assert not minimal(k4,0,14)
assert any((u==0 and v>0) for u,v in k4)
assert independent_swaps>0
print({"labelled_graphs":graphs,
       "independent_minimal_component_swaps":independent_swaps,
       "swaps_with_nonsingleton_blocks":nontrivial_middle,
       "K4_no_edge_hypothesis_counterexample":1})
