#!/usr/bin/env python3
"""Adversarial finite tests for intrinsic C0 top components and lower closures.

These controls re-use the finite minimal-strong-step predicate from the
existing Track D regression. In particular minimality excludes intermediate
z that is strong in the final graph, not intermediate z with a strong base.
They do not certify a particular internal ordered representative.
"""
from itertools import permutations, product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)

def test():
    finite_presentations = generated_values = chronological_orders = multi = 0
    for n in range(1, 5):
        for edges in graphs(n):
            for m in range(1, n + 1):
                for kappa in product(range(m), repeat=n):
                    if set(kappa) != set(range(m)):
                        continue
                    stages = [
                        frozenset(v for v in range(n) if kappa[v] < i)
                        for i in range(m + 1)
                    ]
                    if not all(finite_minimal_step(stages[i], stages[i + 1], edges)
                               for i in range(m)):
                        continue
                    finite_presentations += 1
                    if len(set(kappa)) != n:
                        multi += 1
                    C = finite_component_values(kappa, edges)
                    for a in range(n):
                        generated_values += 1
                        top = {v for v in range(n) if C[v] == C[a]}
                        lower = C[a] - top
                        assert top == {v for v in range(n)
                                       if kappa[v] == kappa[a]}
                        assert C[a] == top | lower and not (top & lower)
                        assert all(kappa[v] < kappa[a] for v in lower)
                        assert all(C[v] <= lower for v in lower)
                    for ordered in permutations(range(n)):
                        rank = {v: i for i, v in enumerate(ordered)}
                        chronological = all(
                            rank[x] < rank[y]
                            for x in range(n) for y in range(n)
                            if kappa[x] < kappa[y]
                        )
                        if not chronological:
                            continue
                        chronological_orders += 1
                        for a in range(n):
                            top = {v for v in range(n) if C[v] == C[a]}
                            lower = C[a] - top
                            assert all(rank[x] < rank[y]
                                       for x in lower for y in top)
    assert (finite_presentations, generated_values,
            chronological_orders, multi) == (1401, 5545, 1421, 4)
    # A closed two-point support may have two independent singleton
    # components, hence cannot be identified with either point's closure.
    C = [{0}, {1}]
    assert all(C[v] <= {0, 1} for v in range(2))
    assert not any(C[v] == {0, 1} for v in range(2))
    print("PASS intrinsic C0 top/lower: 1401 finite presentations, "
          "5545 one-generated closures, 1421 chronological orders, "
          "4 presentations with multivertex increments; negative control")

if __name__ == "__main__":
    test()
