#!/usr/bin/env python3
"""Independent finite closed-overlap regression for preliminary raw C0 host.

Check that two finite C-closed families inherit EXACT full C-values
on their common closed base, and that there are no graph edges
between their exclusive parts. Not a substitute for a Lean proof
or a converse finite-age theorem.
"""
from itertools import combinations, product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)
from check_c0_raw_host_graph import make_code, closure, raw_adj, back


def subsets(items):
    return [frozenset(a) for n in range(len(items) + 1)
            for a in combinations(items, n)]


def is_closed(s):
    return all(closure(q) <= s for q in s)


def c_on(s, q):
    return frozenset(r for r in s if r in closure(q))


def j_on(s, q):
    return frozenset(r for r in s if r in back(q))


def main():
    presentations = overlaps = base_vertices = cross_pairs = 0
    for n in range(1, 5):
        for edges in graphs(n):
            for levels in range(1, n + 1):
                for kappa in product(range(levels), repeat=n):
                    if set(kappa) != set(range(levels)):
                        continue
                    cuts = [frozenset(u for u in range(n) if kappa[u] < i)
                            for i in range(levels + 1)]
                    if not all(finite_minimal_step(cuts[i], cuts[i+1], edges)
                               for i in range(levels)):
                        continue
                    presentations += 1
                    C = finite_component_values(kappa, edges)
                    order = sorted(range(n), key=lambda u: (kappa[u], u))
                    index = {v:i for i,v in enumerate(order)}
                    E = {tuple(sorted((index[u], index[v]))) for u,v in edges}
                    CV = [frozenset(index[v] for v in C[order[i]])
                          for i in range(n)]
                    for gap in (2, 7):
                        lab = {u:gap*(u+1) for u in range(n)}
                        vertices = [make_code(E, CV, CV[a], a, lab)
                                    for a in range(n)]
                        assert len(set(vertices)) == n
                        closed_sets = [s for s in subsets(vertices)
                                       if is_closed(s)]
                        for s in closed_sets:
                            for t in closed_sets:
                                P = s & t
                                overlaps += 1
                                assert is_closed(P) and is_closed(s | t)
                                for q in P:
                                    base_vertices += 1
                                    assert c_on(P,q) == c_on(s,q) == c_on(t,q) == closure(q)
                                    assert j_on(P,q) == j_on(s,q) == j_on(t,q) == back(q)
                                for q in s - t:
                                    for r in t - s:
                                        cross_pairs += 1
                                        assert not raw_adj(q,r)
                                for q in P:
                                    for r in P:
                                        # Both induced factor graphs are the
                                        # restriction of the SAME raw E.
                                        assert (raw_adj(q,r) == raw_adj(r,q))
    assert presentations == 1401
    print(f"PASS raw closed overlaps: {presentations} finite "
          f"minimal-strong presentations, {overlaps} pairs of closed "
          f"factors, {base_vertices} complete C/J base-vertex "
          f"comparisons, {cross_pairs} exclusive cross-pairs")


if __name__ == "__main__":
    main()
