#!/usr/bin/env python3
"""Hostile finite regression for induced-image preservation of minimal strong steps.

Checks every simple graph on <=4 labelled vertices, every strong or weak
a⊆b pair, and every induced injection into a one-vertex-larger graph,
with all choices of extra-vertex adjacencies. Also exhibits explicit
failures if either injectivity or inducedness is removed.
"""

def pairs(n):
    return [(u, v) for v in range(n) for u in range(v)]


def masks_included(n):
    yield from range(1 << n)


def delta(edges, subset):
    return 2 * subset.bit_count() - sum(
        bool(subset & (1 << u)) and bool(subset & (1 << v))
        for u, v in edges)


def strong(edges, a, b):
    if a & ~b:
        return False
    tail = b & ~a
    t = tail
    while True:
        if delta(edges, a | t) < delta(edges, a):
            return False
        if t == 0:
            return True
        t = (t - 1) & tail


def minimal(edges, a, b):
    if a == b or not strong(edges, a, b):
        return False
    tail = b & ~a
    t = tail
    while True:
        c = a | t
        if c != a and c != b and strong(edges, c, b):
            return False
        if t == 0:
            return True
        t = (t - 1) & tail


def image_mask(s, f):
    return sum(1 << f[i] for i in range(len(f)) if s & (1 << i))


checks = 0
for n in range(5):
    E = pairs(n)
    for graph_mask in range(1 << len(E)):
        edges = {uv for k, uv in enumerate(E) if graph_mask & (1 << k)}
        for missing in range(n + 1):
            f = tuple(i if i < missing else i + 1 for i in range(n))
            fixed_edges = {tuple(sorted((f[u], f[v]))) for u, v in edges}
            for outside in range(1 << n):
                induced_edges = fixed_edges | {
                    tuple(sorted((missing, f[i]))) for i in range(n)
                    if outside & (1 << i)
                }
                for b in masks_included(n):
                    for a in masks_included(n):
                        if a & ~b:
                            continue
                        ai, bi = image_mask(a, f), image_mask(b, f)
                        assert minimal(edges, a, b) == minimal(induced_edges, ai, bi)
                        checks += 1

# Without inducedness: K4 contains the minimal strong step
# {0} < {0,1,2,3}; its image in the edgeless graph is not minimal.
complete4 = set(pairs(4))
a, b = 1, 15
assert minimal(complete4, a, b)
assert not minimal(set(), a, b)
# Without injectivity: a singleton minimal step can be collapsed.
assert minimal(set(), 1, 3)
assert not minimal(set(), 1, 1)
print({'induced_minimality_checks': checks, 'noninduced_counterexamples': 1,
       'noninjective_counterexamples': 1})
