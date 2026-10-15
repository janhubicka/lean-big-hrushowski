#!/usr/bin/env python3
"""Adversarial finite checks for class membership under d-closed free joins.

For every labelled simple graph on at most four vertices and every
pair of actual finite vertex sets A,B, test the conditional growth
membership statement for the constant F(n)=0 class:
  no edges between the disjoint tails,
  P=A∩B is strictly d-closed in A and in B,
  both A and B satisfy δ(X)>=0 for all induced X,
  hence the free union satisfies δ(X)>=0.

Separately, the five-vertex free union of two triangles over one
strictly d-closed vertex fails the stronger F(n)=n class condition.
This protects the published paper from inadvertently assuming
that arbitrary monotone growth bounds preserve free amalgamation.

The universal Lean batch theorem is conditional on the exact
growth-class free-amalgamation hypothesis. These finite tests
supplement its proof; they are not a proof of the published
growth-function free-amalgamation criterion.
"""
from itertools import combinations
from fractions import Fraction

graphs=pairs=applicable=joins=nontrivial_base=0

def delta(n,edges,s):
    return 2*s.bit_count()-sum(bool(s&(1<<u)) and bool(s&(1<<v))
                                for u,v in edges)
def closed(n,edges,a,b):
    if a&~b:return False
    tail=b&~a
    t=tail
    while t:
        if delta(n,edges,a)>=delta(n,edges,a|t):return False
        t=(t-1)&tail
    return True
def member(n,edges,a,F):
    s=a
    while True:
        if Fraction(delta(n,edges,s))<F(s.bit_count()):return False
        if not s:break
        s=(s-1)&a
    return True
def no_cross(edges,A,B):
    return all(not (
        (A&(1<<u) and not B&(1<<u) and
         B&(1<<v) and not A&(1<<v)) or
        (A&(1<<v) and not B&(1<<v) and
         B&(1<<u) and not A&(1<<u))
    ) for u,v in edges)

for n in range(5):
    possibilities=tuple(combinations(range(n),2))
    for mask in range(1<<len(possibilities)):
        edges={e for i,e in enumerate(possibilities) if mask&(1<<i)}
        graphs+=1
        for A in range(1<<n):
            for B in range(1<<n):
                pairs+=1
                P=A&B
                if not no_cross(edges,A,B):continue
                if not closed(n,edges,P,A) or not closed(n,edges,P,B):
                    continue
                if not member(n,edges,A,lambda n:Fraction(0)):continue
                if not member(n,edges,B,lambda n:Fraction(0)):continue
                applicable+=1
                if P:nontrivial_base+=1
                assert member(n,edges,A|B,lambda n:Fraction(0))
                joins+=1

triA={(0,1),(0,2),(1,2)}
triB={(0,3),(0,4),(3,4)}
P=1
A=0b00111
B=0b11001
F=lambda n:Fraction(n)
assert no_cross(triA|triB,A,B)
assert closed(5,triA,P,A) and closed(5,triB,P,B)
assert member(5,triA,A,F) and member(5,triB,B,F)
assert not member(5,triA|triB,A|B,F)

assert applicable>0 and nontrivial_base>0
print({
    "graphs_to_four_vertices":graphs,
    "finite_free_join_pairs_tested":pairs,
    "applicable_dclosed_growth_joins":applicable,
    "verified_F_zero_growth_unions":joins,
    "joins_with_nonempty_closed_intersection":nontrivial_base,
    "F_equals_n_free_amalgamation_counterexample":True,
    "conditional_class_join_mismatches":0
})
