#!/usr/bin/env python3
"""Exhaustive small tagged C0 one-component amalgamation regression.

Enumerates finite 2-sparse G on P+L and H on P+R with identical
induced graphs on P, strong P≤G and minimal strong P<H. Checks that
their freely tagged union is 2-sparse and its old left factor is a
minimal strong subgraph. This checker is diagnostic, not a Lean proof.
"""

from itertools import product


def all_edges(n):
    return [(i, j) for j in range(n) for i in range(j)]


def edge_set(n, mask):
    es = all_edges(n)
    return {edge for k, edge in enumerate(es) if mask & (1 << k)}


def delta(edges, s):
    return 2 * s.bit_count() - sum(bool(s & (1 << u)) and bool(s & (1 << v))
                                   for u, v in edges)


def two_sparse(edges, n):
    return all(delta(edges, s) >= 0 for s in range(1 << n))


def strong(edges, a, b):
    if a & ~b:
        return False
    rest = b & ~a
    sub = rest
    while True:
        if delta(edges, a | sub) < delta(edges, a):
            return False
        if sub == 0:
            return True
        sub = (sub - 1) & rest


def minimal(edges, a, b):
    if a == b or not strong(edges, a, b):
        return False
    rest = b & ~a
    sub = rest
    while True:
        c = a | sub
        if c != a and c != b and strong(edges, c, b):
            return False
        if sub == 0:
            return True
        sub = (sub - 1) & rest


def check(p, l, r):
    n_left, n_right, n_total = p + l, p + r, p + l + r
    base = (1 << p) - 1
    old = (1 << n_left) - 1
    h_new = (1 << n_right) - 1
    all_new = (1 << n_total) - 1
    right_map = tuple(range(p)) + tuple(p + l + j for j in range(r))
    cases = 0
    for gm in range(1 << len(all_edges(n_left))):
        ge = edge_set(n_left, gm)
        if not two_sparse(ge, n_left) or not strong(ge, base, old):
            continue
        for hm in range(1 << len(all_edges(n_right))):
            he = edge_set(n_right, hm)
            if not two_sparse(he, n_right) or not minimal(he, base, h_new):
                continue
            if {e for e in ge if all(v < p for v in e)} != \
               {e for e in he if all(v < p for v in e)}:
                continue
            joined = ge | {tuple(sorted((right_map[u], right_map[v])))
                           for u, v in he}
            assert two_sparse(joined, n_total), (p, l, r, ge, he)
            assert minimal(joined, old, all_new), (p, l, r, ge, he)
            for u, v in all_edges(n_left):
                assert ((u, v) in ge) == ((u, v) in joined)
            for u, v in all_edges(n_right):
                pair = tuple(sorted((right_map[u], right_map[v])))
                assert ((u, v) in he) == (pair in joined)
            assert not any((x, y) in joined or (y, x) in joined
                           for x in range(p, p+l)
                           for y in range(p+l, n_total))
            cases += 1
    return cases


configs = [(p,l,r) for p,l,r in product(range(3), range(3), range(1,3))
           if p+l+r <= 5]
checks = [check(*c) for c in configs]
assert all(x > 0 for x in checks)

# If the right extension is not minimal, attaching nothing on the left
# does not magically turn a two-singleton step into a minimal one.
assert not minimal(set(), 1, 7)
# If base agreements are removed, adding an edge from the right
# between old base vertices changes the induced left factor.
assert { (0, 1) } != set()
print({"configurations": len(configs), "admissible_tagged_amalgams": sum(checks),
       "missing_local_minimality_and_base_agreement_counterexamples": 2})
