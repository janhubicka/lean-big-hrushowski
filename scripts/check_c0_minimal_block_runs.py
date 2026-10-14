#!/usr/bin/env python3
"""Audit literal fresh-block runs for every finite strong graph pair.

For every strong pair A≤B in every labelled simple graph with at
most five vertices, select cardinality-minimal strong intermediates
and record exactly their disjoint fresh vertex differences.
Check that each block is nonempty, disjoint from the current old
prefix, a minimal strong extension, and that the final union is
literally B. Test reconstruction of the chain from the same blocks.
"""
from itertools import combinations

def edges_of(n,bits):
    pairs=list(combinations(range(n),2))
    return [p for i,p in enumerate(pairs) if bits & (1<<i)]

def delta(edges,s):
    return 2*s.bit_count()-sum(bool(s&(1<<u)) and bool(s&(1<<v))
                             for u,v in edges)

def strong(edges,a,b):
    if a & ~b:return False
    t=rest=b&~a
    while True:
        if delta(edges,a)>delta(edges,a|t):return False
        if t==0:return True
        t=(t-1)&rest

def minimal(edges,a,b):
    if a==b or not strong(edges,a,b):return False
    t=rest=b&~a
    while True:
        c=a|t
        if c not in (a,b) and strong(edges,c,b):return False
        if t==0:return True
        t=(t-1)&rest

graphs=pairs_checked=blocks_checked=empty_runs=0
for n in range(6):
    for bits in range(1 << (n*(n-1)//2)):
        edges=edges_of(n,bits);graphs+=1
        for b in range(1<<n):
            for a in range(1<<n):
                if not strong(edges,a,b):continue
                original=a
                blocks=[]
                while a!=b:
                    options=[c for c in range(1<<n)
                             if c&~b==0 and c&a==a and c!=a
                             and strong(edges,c,b)]
                    assert options
                    c=min(options,key=lambda v:(v.bit_count(),v))
                    B=c&~a
                    assert B and not(B&a)
                    assert a|B==c and minimal(edges,a,c)
                    blocks.append(B);a=c
                    blocks_checked+=1
                now=original
                for B in blocks:
                    assert B and not(B&now)
                    assert minimal(edges,now,now|B)
                    now|=B
                assert now==b
                pairs_checked+=1
                empty_runs+=not blocks
assert graphs and pairs_checked and blocks_checked and empty_runs
print({"labelled_graphs":graphs,"finite_strong_pairs":pairs_checked,
       "literal_fresh_minimal_blocks":blocks_checked,
       "empty_reflexive_runs":empty_runs})
