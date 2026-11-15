#!/usr/bin/env python3
"""Finite falsification of the functional local-order transport lemma.

The nontrivial local type is the canonical C0 presentation
  empty < {a} < K4,
where the three new vertices form a minimal strong component whose
complete lower part is {a}. Its pointwise lower-part automorphism
group is S3, not the trivial group. There is no labelled linear order
fixed by all of S3, but the six transports of one representative
form one free orbit.

Enumerate all 36 pairs of automorphisms to verify the exact change
of local coordinates, its pointwise fixation of the lower part,
induced adjacency, *complete* canonical unary values and rank order.
Also check that no nonidentity automorphism preserves all ranks.

This is an independent finite regression, not a proof of the Lean
statements for arbitrary finite functional structures.
"""
from itertools import permutations, combinations

V = tuple(range(4))
P = frozenset({0})
B = frozenset({1, 2, 3})
edges = {frozenset(e) for e in combinations(V, 2)}
C = {0: frozenset({0}),
     1: frozenset(V), 2: frozenset(V), 3: frozenset(V)}
delta = lambda S: 2 * len(S) - sum(e <= S for e in edges)
assert delta(frozenset()) == 0
assert delta(P) == 2
assert delta(frozenset(V)) == 2
for r in (1, 2):
    for S in combinations(B, r):
        assert delta(P | frozenset(S)) == 3

aut = [{0: 0, **dict(zip((1, 2, 3), perm))}
       for perm in permutations((1, 2, 3))]
assert len(aut) == 6
rank = {x: x for x in V}

def inverse(g):
    return {g[x]: x for x in V}

def compose(f, g):
    return {x: f[g[x]] for x in V}

orders = set()
checked = 0
for e1 in aut:
    key = tuple(rank[e1[x]] for x in (1, 2, 3))
    orders.add(key)
    for e2 in aut:
        g = compose(inverse(e2), e1)
        assert all(g[p] == p for p in P)
        assert all(e2[g[x]] == e1[x] for x in V)
        assert all((frozenset({x,y}) in edges) ==
                   (frozenset({g[x],g[y]}) in edges)
                   for x in V for y in V if x != y)
        assert all(C[g[x]] == frozenset(g[y] for y in C[x])
                   for x in V)
        assert all((rank[e1[x]] < rank[e1[y]]) ==
                   (rank[e2[g[x]]] < rank[e2[g[y]]])
                   for x in V for y in V)
        checked += 1

assert checked == 36
assert len(orders) == 6
for e in aut:
    if all((rank[x] < rank[y]) == (rank[e[x]] < rank[e[y]])
           for x in V for y in V):
        assert all(e[x] == x for x in V)
print("local-order orbit regression: K4, S3, six free transports,",
      checked, "ordered pairs verified")
