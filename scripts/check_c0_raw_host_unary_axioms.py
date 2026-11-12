#!/usr/bin/env python3
"""Adversarial finite test of reflexive, nested raw C0 host unary values.

All minimal-strong canonical C0 presentations with at most four vertices
and two increasing coordinate maps are checked. The raw host vertex is
a complete pointed code of a C-closure, not merely its generating point.
"""
from itertools import product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)


def code(edges, C, S, root, e):
    return (
        frozenset(e[v] for v in S),
        e[root],
        frozenset((e[u], e[v]) for u in S for v in S
                  if u != v and tuple(sorted((u, v))) in edges),
        frozenset((e[u], e[v]) for u in S for v in C[u] if v in S),
    )


def named_value(q, x):
    S, _, _, C = q
    return frozenset(y for y in S if (x, y) in C)


def child(q, x):
    S, _, E, C = q
    assert x in S
    T = named_value(q, x)
    assert x in T, "C reflexivity is essential"
    return (T, x,
            frozenset((u, v) for u, v in E if u in T and v in T),
            frozenset((u, v) for u, v in C if u in T and v in T))


def closed_value(q):
    return frozenset(child(q, x) for x in q[0])


def main():
    presentations = roots = member_pairs = nested_pairs = 0
    for n in range(1, 5):
        for edges in graphs(n):
            for levels in range(1, n + 1):
                for stages in product(range(levels), repeat=n):
                    if set(stages) != set(range(levels)):
                        continue
                    cuts = [frozenset(v for v in range(n) if stages[v] < k)
                            for k in range(levels + 1)]
                    if not all(finite_minimal_step(cuts[k], cuts[k + 1], edges)
                               for k in range(levels)):
                        continue
                    presentations += 1
                    C = finite_component_values(stages, edges)
                    for gap in (2, 7):
                        e = {v: gap * (v + 1) for v in range(n)}
                        for a in range(n):
                            q = code(edges, C, C[a], a, e)
                            roots += 1
                            assert q in closed_value(q)
                            assert {r[1] for r in closed_value(q)} == q[0]
                            assert len(closed_value(q)) == len(q[0])
                            for r in closed_value(q):
                                member_pairs += 1
                                Cr = closed_value(r)
                                assert Cr <= closed_value(q)
                                for s in Cr:
                                    nested_pairs += 1
                                    assert s in closed_value(q)
    assert presentations == 1401 and roots == 11090

    # Root generation and complete support alone do not imply the
    # raw host closure axioms. A nonreflexive C-row breaks the child.
    malformed = (
        frozenset({0, 1}), 0, frozenset(),
        frozenset({(0, 0), (0, 1)}),
    )
    assert named_value(malformed, 0) == malformed[0]
    try:
        closed_value(malformed)
    except AssertionError:
        pass
    else:
        raise AssertionError("negative control: missing C(1) reflexivity")

    # Reflexivity alone is insufficient: C(1) contains 2 while C(2)
    # contains 0, which makes the child-of-child at 2 differ from
    # the child of the parent at 2.
    nonnested = (
        frozenset({0, 1, 2}), 0, frozenset(),
        frozenset({(0, 0), (0, 1), (0, 2),
                   (1, 1), (1, 2), (2, 0), (2, 2)}),
    )
    cq = closed_value(nonnested)
    c1 = child(nonnested, 1)
    assert c1 in cq and not closed_value(c1) <= cq

    print(f"PASS raw C0 host unary laws: {presentations} minimal-strong "
          f"presentations, {roots} complete pointed codes, "
          f"{member_pairs} child memberships, {nested_pairs} nested "
          "memberships; two nonadmissible negative controls")


if __name__ == "__main__":
    main()
