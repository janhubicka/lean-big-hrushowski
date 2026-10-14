#!/usr/bin/env python3
"""Canonical C0 heredity: compare *actual unary values* after restriction.

For each small minimal strong block presentation, choose each subset
closed under complete backwards component reachability. Restrict the
graph, retain the old chronological component indices (including now
empty fibres), and recompute the unary closures from the induced
graph. Every value must be exactly the original value, not merely
a subset. Check that the restricted nonempty stage cuts remain
minimal strong.

This tests the finite functional-age heredity theorem rather than
only its graph reduct.
"""
from itertools import combinations, product

def edge_sets(n, bits):
    pairs=list(combinations(range(n),2))
    return [p for k,p in enumerate(pairs) if bits & (1<<k)]

def delta(edges, subset):
    return 2*subset.bit_count() - sum(bool(subset&(1<<u)) and
        bool(subset&(1<<v)) for u,v in edges)

def strong(edges,a,b):
    if a & ~b: return False
    rest=t=b & ~a
    while True:
        if delta(edges,a) > delta(edges,a|t): return False
        if t==0: return True
        t=(t-1)&rest

def minimal(edges,a,b):
    if a==b or not strong(edges,a,b): return False
    rest=t=b & ~a
    while True:
        c=a|t
        if c not in (a,b) and strong(edges,c,b): return False
        if t==0: return True
        t=(t-1)&rest

def values(edges, labels, m, selected):
    blocks=[sum(1<<u for u,i in enumerate(labels)
                if i==k and (selected&(1<<u))) for k in range(m)]
    dep=[set() for _ in range(m)]
    for u,v in edges:
        if not (selected&(1<<u) and selected&(1<<v)): continue
        i,j=labels[u],labels[v]
        if i>j: dep[i].add(j)
        elif j>i: dep[j].add(i)
    closures=[]
    for i in range(m):
        reached,queue={i},[i]
        for j in queue:
            for k in dep[j]:
                if k not in reached:
                    reached.add(k);queue.append(k)
        closure=0
        for j in reached: closure |= blocks[j]
        closures.append(closure)
    return closures

graphs=presentations=closed_sets=unary_equalities=retained_steps=0
for n in range(5):
    full=(1<<n)-1
    for bits in range(1 << (n*(n-1)//2)):
        edges=edge_sets(n,bits);graphs+=1
        for m in range(1,5):
            for labels in product(range(m), repeat=n):
                blocks=[sum(1<<u for u,j in enumerate(labels) if j==k)
                        for k in range(m)]
                stages=[0]
                for block in blocks: stages.append(stages[-1]|block)
                if any(a!=b and not minimal(edges,a,b)
                       for a,b in zip(stages,stages[1:])):
                    continue
                presentations+=1
                original=values(edges, labels, m, full)
                for s in range(1<<n):
                    if not all(original[labels[u]] & ~s == 0
                               for u in range(n) if s&(1<<u)):
                        continue
                    closed_sets+=1
                    restricted=values(edges, labels, m, s)
                    for u in range(n):
                        if s&(1<<u):
                            assert original[labels[u]] == restricted[labels[u]], (
                                'unary changed', edges, labels,s,u)
                            unary_equalities+=1
                    for a,b in zip(stages,stages[1:]):
                        x,y=s&a,s&b
                        assert x==y or minimal(edges,x,y)
                        retained_steps+=x!=y
assert all(z>0 for z in [presentations,closed_sets,unary_equalities])
print({'labelled_graphs':graphs,
       'minimal_indexed_presentations':presentations,
       'closed_substructures':closed_sets,
       'inherited_unary_value_equalities':unary_equalities,
       'retained_minimal_steps':retained_steps})
