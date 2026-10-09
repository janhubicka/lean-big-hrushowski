"""Finite six-vertex closure-component example from the manuscript.

Three isolated old vertices are joined to distinct vertices of a new
triangle. This verifies the displayed predimension calculations and the
nontrivial one-generator strong closure, but is not a formal proof.
"""
from itertools import combinations

old = {0, 1, 2}
new = {3, 4, 5}
full = old | new
edges = {(3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)}

def powerset(s):
    ls = sorted(s)
    return [set(t) for k in range(len(ls)+1) for t in combinations(ls,k)]

def delta(s):
    return 2 * len(s) - sum({a, b} <= s for a, b in edges)

def strong(a, c):
    return all(delta(a) <= delta(x)
               for x in powerset(c) if a <= x)

assert all(delta(s) >= 0 for s in powerset(full)), "example is not 2-sparse"
assert delta(old) == 6
assert delta(full) == 6
assert strong(old, full)
for s in powerset(new):
    internal = sum({u, v} <= s for u, v in [(3,4),(4,5),(3,5)])
    assert delta(old | s) - delta(old) == len(s) - internal
    if s and s != new:
        assert delta(old | s) > delta(old)
for x in new:
    candidates = [d for d in powerset(full)
                  if old | {x} <= d and strong(d, full)]
    assert candidates == [full], (x, candidates)

print("Verified the six-vertex triangle-component example and its three closures.")
