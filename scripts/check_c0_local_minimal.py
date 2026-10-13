#!/usr/bin/env python3
"""Finite hostile regression for minimal strong steps under a no-cross join.

Enumerates every simple labelled graph with at most five vertices, and
every partition V=P ⊔ Q ⊔ B where Q=A\P. When there is no edge B--Q,
checks equality of relative predimensions at ALL intermediate sets and
equivalence of strongness and minimality for P<P∪B versus A<A∪B.
"""
from itertools import product

graphs = cases = intermediate_tests = minimal_checks = 0
for n in range(0, 6):
    edges = [(i, j) for i in range(n) for j in range(i)]
    for edge_mask in range(1 << len(edges)):
        e = {frozenset(pair) for k, pair in enumerate(edges)
             if edge_mask & (1 << k)}
        def delta(mask):
            return 2 * mask.bit_count() - sum(
                (mask & (1 << u)) and (mask & (1 << v)) for u, v in e)
        def strong(a, b):
            if a & ~b:
                return False
            tail = b & ~a
            sub = tail
            while True:
                z = a | sub
                if delta(z) < delta(a):
                    return False
                if sub == 0:
                    return True
                sub = (sub - 1) & tail
        def minimal(a, b):
            if a == b or not strong(a, b):
                return False
            tail = b & ~a
            sub = tail
            while True:
                z = a | sub
                if z != a and z != b and strong(z, b):
                    return False
                if sub == 0:
                    return True
                sub = (sub - 1) & tail
        for roles in product(range(3), repeat=n):
            P = sum(1 << i for i, r in enumerate(roles) if r == 0)
            Q = sum(1 << i for i, r in enumerate(roles) if r == 1)
            B = sum(1 << i for i, r in enumerate(roles) if r == 2)
            if any(roles[u] == 1 and roles[v] == 2 or
                   roles[u] == 2 and roles[v] == 1 for u, v in e):
                continue
            A = P | Q
            tail = B
            sub = tail
            while True:
                D = P | sub
                assert delta(A | D) + delta(P) == delta(A) + delta(D)
                intermediate_tests += 1
                if sub == 0:
                    break
                sub = (sub - 1) & tail
            assert strong(A, A | B) == strong(P, P | B)
            assert minimal(A, A | B) == minimal(P, P | B)
            cases += 1
            minimal_checks += 2
        graphs += 1
print({"graphs": graphs, "no_cross_partitions": cases,
       "relative_predim_checks": intermediate_tests,
       "strong_and_minimal_checks": minimal_checks})
