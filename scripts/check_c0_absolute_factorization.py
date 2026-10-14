#!/usr/bin/env python3
"""Check absolute finite minimal strong factorization in small graphs.

This checks every strong pair A≤B in all labelled graphs of size ≤5,
without assuming B globally strong in any ambient graph.
It constructs cardinal-minimal strong intermediate sets and verifies
that each chosen step is minimal and that the finite chain terminates.
"""
from itertools import combinations


def graph_edges(n, bits):
    es = list(combinations(range(n), 2))
    return tuple(es[i] for i in range(len(es)) if bits & (1 << i))


def delta(edges, s):
    return 2*s.bit_count() - sum(
        bool(s & (1 << u)) and bool(s & (1 << v)) for u, v in edges
    )


def strong(edges, a, b):
    if a & ~b:
        return False
    sub, rest = b & ~a, b & ~a
    while True:
        if delta(edges, a) > delta(edges, a | sub):
            return False
        if sub == 0:
            return True
        sub = (sub - 1) & rest


def minimal(edges, a, b):
    if a == b or not strong(edges, a, b):
        return False
    rest, sub = b & ~a, b & ~a
    while True:
        c = a | sub
        if c != a and c != b and strong(edges, c, b):
            return False
        if sub == 0:
            return True
        sub = (sub - 1) & rest


def absolute_chain(edges, a, b):
    stages = [a]
    while a != b:
        candidates = [c for c in range(b+1)
                      if c & ~b == 0 and c & a == a and c != a
                      and strong(edges, c, b)]
        assert candidates
        c = min(candidates, key=lambda z: (z.bit_count(), z))
        assert minimal(edges, a, c)
        assert strong(edges, c, b)
        stages.append(c)
        assert len(stages) <= b.bit_count() + 1
        a = c
    return stages


graphs = strong_pairs = minimal_steps = proper_pairs = 0
for n in range(6):
    for mask in range(1 << (n*(n-1)//2)):
        edges = graph_edges(n, mask)
        graphs += 1
        for b in range(1 << n):
            for a in range(1 << n):
                if a & ~b or not strong(edges, a, b):
                    continue
                stages = absolute_chain(edges, a, b)
                assert stages[0] == a and stages[-1] == b
                assert len(stages) >= 1
                strong_pairs += 1
                minimal_steps += len(stages) - 1
                if a != b:
                    proper_pairs += 1

# A strong finite inclusion whose upper endpoint is not globally
# strong in its ambient graph: a graph of a 3-leaf star.
star = ((0,3),(1,3),(2,3))
a, b, full = 0, 0b0111, 0b1111
assert strong(star, a, b)
assert not strong(star, b, full)
assert absolute_chain(star, a, b)[-1] == b
print({"labelled_graphs": graphs, "finite_strong_pairs": strong_pairs,
       "proper_strong_pairs": proper_pairs,
       "minimal_steps": minimal_steps,
       "non_global_endpoint_counterexample": 1})
