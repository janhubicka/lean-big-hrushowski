#!/usr/bin/env python3
"""Adversarial finite regressions for presented, one-generated C0 coordinate codes.

All minimal-strong finite component presentations on up to four points are
canonically relabelled in chronological order before testing complete
one-generated coordinate codes under two increasing coordinate embeddings.
Actual C0 presentations form a strictly smaller class than supported,
root-generated arbitrary incidence records.
"""
from itertools import product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)


def check():
    presentations = roots = codes = full_pairs = 0
    for n in range(1, 5):
        for edges in graphs(n):
            for levels in range(1, n + 1):
                for stages in product(range(levels), repeat=n):
                    if set(stages) != set(range(levels)):
                        continue
                    cuts = [
                        frozenset(v for v in range(n) if stages[v] < i)
                        for i in range(levels + 1)
                    ]
                    if not all(finite_minimal_step(
                            cuts[i], cuts[i+1], edges)
                            for i in range(levels)):
                        continue
                    presentations += 1
                    values = finite_component_values(stages, edges)
                    order = tuple(sorted(range(n), key=lambda v: (stages[v], v)))
                    idx = {v: j for j, v in enumerate(order)}
                    indexed_stages = tuple(stages[v] for v in order)
                    assert list(indexed_stages) == sorted(indexed_stages)
                    numbered_edges = {tuple(sorted((idx[u], idx[v])))
                                      for u, v in edges}
                    C = [frozenset(idx[v] for v in values[order[i]])
                         for i in range(n)]
                    assert all(i in C[i] for i in range(n))
                    assert all(C[j] <= C[i] for i in range(n) for j in C[i])
                    for a in range(n):
                        roots += 1
                        S = C[a]
                        assert all(C[u] <= S for u in S)
                        for gap in (3, 11):
                            e = {v: gap * (v + 1) for v in range(n)}
                            support = frozenset(e[v] for v in S)
                            point = e[a]
                            adj = frozenset((e[u], e[v])
                                for u in S for v in S if u != v and
                                tuple(sorted((u,v))) in numbered_edges)
                            closure = frozenset((e[u], e[v])
                                for u in S for v in C[u])
                            square = {(x,y) for x in support for y in support}
                            assert point in support
                            assert adj <= square and closure <= square
                            assert all(((point,y) in closure) == (y in support)
                                       for y in support)
                            for u in S:
                                for v in S:
                                    assert (((e[u],e[v]) in adj) ==
                                       (u != v and tuple(sorted((u,v))) in numbered_edges))
                                    assert (((e[u],e[v]) in closure) == (v in C[u]))
                                    full_pairs += 1
                            # Every inherited step is either empty or
                            # minimal strong in the induced graph.
                            subedges = {tuple(sorted((u,v))) for u,v
                                        in numbered_edges if u in S and v in S}
                            for j in range(levels):
                                old = frozenset(v for v in S if indexed_stages[v] < j)
                                new = frozenset(v for v in S if indexed_stages[v] <= j)
                                assert old == new or finite_minimal_step(old,new,subedges)
                            codes += 1
    assert (presentations, roots, codes) == (1401, 5545, 11090)
    # Even a fully supported and root-generated record may be invalid
    # as a finite graph: a loop is impossible in GraphOn.
    support = {0}
    root, closure = 0, {(0,0)}
    phantom_graph = {(0,0)}
    assert root in support and phantom_graph <= {(0,0)}
    assert all(((root,v) in closure) == (v in support) for v in support)
    assert any(u == v for u,v in phantom_graph)
    print(f"PASS: {presentations} minimal-strong presentations, "
          f"{roots} roots, {codes} increasing generated codes, "
          f"{full_pairs} exact full-pair checks and a supported-but-invalid "
          "loop negative control")


if __name__ == "__main__":
    check()
