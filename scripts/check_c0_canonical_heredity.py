#!/usr/bin/env python3
"""Check heredity for every finite canonical C0 minimal block enumeration.

Exhaustively enumerate simple graphs with <=4 vertices and chronological
component-index assignments. Retain assignments in which each successive
block is empty or minimal strong. Compute the *complete* unary
reachability values. For every closed set, verify that each retained
component produces a minimal strong induced extension and that
omitted components give identical successive cuts.

Empty chronological positions are deliberately permitted: they can be
removed from the witnessing presentation without changing unary values.
"""
from itertools import combinations, product

def edges_of(n, mask):
    pairs = list(combinations(range(n),2))
    return [pair for k,pair in enumerate(pairs) if mask & (1<<k)]

def delta(edges,s):
    return 2*s.bit_count() - sum(bool(s&(1<<u)) and bool(s&(1<<v))
                               for u,v in edges)

def strong(edges,a,b):
    if a & ~b: return False
    t = tail = b & ~a
    while True:
        if delta(edges,a) > delta(edges,a|t): return False
        if t == 0: return True
        t = (t-1)&tail

def minimal(edges,a,b):
    if a == b or not strong(edges,a,b): return False
    t = tail = b & ~a
    while True:
        c = a|t
        if c not in (a,b) and strong(edges,c,b): return False
        if t == 0: return True
        t = (t-1)&tail

def check(edges, labels, m):
    n=len(labels)
    blocks=[sum(1<<v for v,i in enumerate(labels) if i==k)
            for k in range(m)]
    old=[0]
    for block in blocks: old.append(old[-1]|block)
    if any(a!=b and not minimal(edges,a,b)
           for a,b in zip(old,old[1:])):
        return (0,0,0)
    dep=[set() for _ in range(m)]
    for u,v in edges:
        i,j=labels[u],labels[v]
        if i>j: dep[i].add(j)
        elif j>i: dep[j].add(i)
    values=[0]*m
    for i in range(m):
        reached,queue={i},[i]
        for k in queue:
            for j in dep[k]:
                if j not in reached: reached.add(j);queue.append(j)
        values[i]=sum(blocks[j] for j in reached)
    checked=retained=0
    for s in range(1<<n):
        if not all(values[labels[v]] & ~s == 0
                   for v in range(n) if s&(1<<v)):
            continue
        for a,b in zip(old,old[1:]):
            x,y=s&a,s&b
            assert x==y or minimal(edges,x,y), (edges, labels,s,x,y)
            retained += x!=y
        assert strong(edges,s,old[-1])
        checked+=1
    return (1,checked,retained)

graphs=presentations=closed=retained=0
for n in range(5):
    for mask in range(1 << (n*(n-1)//2)):
        edges=edges_of(n,mask)
        graphs+=1
        for m in range(1,5):
            for labels in product(range(m),repeat=n):
                good,c,r=check(edges,labels,m)
                presentations+=good
                closed+=c
                retained+=r

assert presentations and closed and retained
print({"labelled_graphs": graphs, "minimal_indexed_presentations": presentations,
       "closed_selected_presentations": closed,
       "retained_minimal_steps": retained})
