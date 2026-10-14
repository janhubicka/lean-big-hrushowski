#!/usr/bin/env python3
"""Independent exhaustive audit of strict d-closure in no-cross free joins.

For every graph on up to five labelled vertices and every partition of
the whole carrier into P, A\P and a fresh block B, if there are no edges
between B and A\P, check the equivalence

    P <=_d P ∪ B   iff   A <=_d A ∪ B.

Strict d-closure means δ grows on EVERY proper intermediate set.
This is a counterexample search, independent of the Lean proof.
"""
from itertools import combinations, product

def predim(n, edge_list, vertices):
    e = sum((vertices >> u) & 1 and (vertices >> v) & 1
            for u, v in edge_list)
    return 2 * vertices.bit_count() - e

def dclosed(delta, a, b):
    assert a & ~b == 0
    tail = b & ~a
    t = tail
    while t:
        if delta(a | t) <= delta(a):
            return False
        t = (t - 1) & tail
    return True

def has_cross(edge_list, old_only, fresh):
    return any(((old_only >> u) & 1 and (fresh >> v) & 1) or
               ((old_only >> v) & 1 and (fresh >> u) & 1)
               for u, v in edge_list)

checked = 0
for n in range(6):
    pairs = list(combinations(range(n), 2))
    all_vertices = (1 << n) - 1
    for mask in range(1 << len(pairs)):
        E = tuple(e for k, e in enumerate(pairs) if (mask >> k) & 1)
        delta_cache = tuple(predim(n, E, s) for s in range(1 << n))
        delta = delta_cache.__getitem__
        for categories in product((0, 1, 2), repeat=n):
            p = sum(1 << v for v in range(n) if categories[v] == 0)
            old_only = sum(1 << v for v in range(n)
                           if categories[v] == 1)
            b = all_vertices & ~(p | old_only)
            if has_cross(E, old_only, b):
                continue
            a = p | old_only
            local = dclosed(delta, p, p | b)
            global_ = dclosed(delta, a, a | b)
            assert local == global_, (
                "strict d-closure transfer fails", n, E,
                p, old_only, b, local, global_)
            checked += 1

# Hypothesis necessity: P is empty, A={0,1} and B={2}.
# Each new edge to an omitted old vertex reduces the strict increment.
E = ((0, 2), (1, 2))
delta = lambda s: predim(3, E, s)
assert dclosed(delta, 0, 4)
assert not dclosed(delta, 3, 7)
assert has_cross(E, 3, 4)

print({
    "graphs_up_to_vertices": 5,
    "no_cross_partition_cases": checked,
    "strict_local_global_dclosed_mismatches": 0,
    "no_cross_hypothesis_is_necessary": True
})
