#!/usr/bin/env python3
"""Independent exhaustive audit of weak, strict and minimal no-cross joins.

For every graph on up to five labelled vertices and every partition of
the whole carrier into P, A\P and a fresh block B, if there are no edges
between B and A\P, check the equivalence

    P <=_s P ∪ B   iff   A <=_s A ∪ B,
    P <=_d P ∪ B   iff   A <=_d A ∪ B,
    P <min_s P∪B   iff   A <min_s A∪B.

Strict d-closure means δ grows on EVERY proper intermediate set.
Minimal strongness excludes any proper strong intermediate vertex set.
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

def strong(delta, a, b):
    assert a & ~b == 0
    tail = b & ~a
    t = tail
    while True:
        if delta(a | t) < delta(a):
            return False
        if not t:
            return True
        t = (t - 1) & tail

def minimal_strong(delta, a, b):
    if a == b or not strong(delta, a, b):
        return False
    tail = b & ~a
    t = (tail - 1) & tail
    while t:
        if strong(delta, a | t, b):
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
            assert strong(delta, p, p | b) == strong(delta, a, a | b), (
                "weak strongness transfer fails", n, E, p, old_only, b)
            assert minimal_strong(delta, p, p | b) == minimal_strong(
                delta, a, a | b), (
                "minimal strong step transfer fails", n, E,
                p, old_only, b)
            if dclosed(delta, p, a):
                assert dclosed(delta, p | b, a | b), (
                    "right factor strict d-closedness failed",
                    n, E, p, old_only, b)
            checked += 1

# Hypothesis necessity: P is empty, A={0,1} and B={2}.
# Each new edge to an omitted old vertex reduces the strict increment.
E = ((0, 2), (1, 2))
delta = lambda s: predim(3, E, s)
assert dclosed(delta, 0, 4)
assert not dclosed(delta, 3, 7)
assert has_cross(E, 3, 4)

E = ((0, 3), (1, 3), (2, 3))
delta = lambda s: predim(4, E, s)
assert strong(delta, 0, 8)
assert not strong(delta, 7, 15)
assert minimal_strong(delta, 0, 8)
assert not minimal_strong(delta, 7, 15)
assert has_cross(E, 7, 8)

# The base d-closedness condition is necessary for the second factor.
# P=empty, A=K5, B={5} isolated: the ambient 2-sparse K5 has delta 0.
K5 = tuple(combinations(range(5), 2))
k5delta = lambda s: predim(6, K5, s)
assert not dclosed(k5delta, 0, (1 << 5) - 1)
assert dclosed(k5delta, (1 << 5) - 1, (1 << 6) - 1)
assert dclosed(k5delta, 0, 1 << 5)
assert not dclosed(k5delta, 1 << 5, (1 << 6) - 1)

print({
    "graphs_up_to_vertices": 5,
    "no_cross_partition_cases": checked,
    "strict_local_global_dclosed_mismatches": 0,
    "weak_local_global_strong_mismatches": 0,
    "minimal_strong_step_mismatches": 0,
    "right_factor_dclosed_failures_with_dclosed_base": 0,
    "base_closedness_hypothesis_is_necessary": True,
    "no_cross_hypothesis_is_necessary": True
})
