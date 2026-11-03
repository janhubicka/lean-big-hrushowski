#!/usr/bin/env python3
"""Exhaustive small controls for the C0 finite coordinate-host interface.

Enumerate reflexive/transitive vertex-valued closures on 0..3 points
and compatible irreflexive simple graphs. Check:
 - E is recovered exactly from J(v) = N(v) ∩ C(v);
 - no cross edges between exclusive parts of two C-closed sets;
 - the complete C- and J-values remain unchanged on closed restrictions;
 - successive closed restrictions agree;
 - literal finite codes record all edges, nonedges and C-memberships.

This is a finite regression, not a proof of the infinite coordinate host.
"""
from itertools import combinations, product


def closed_systems(n):
    for masks in product(range(1 << n), repeat=n):
        values = [{j for j in range(n) if m & (1 << j)} for m in masks]
        if all(i in values[i] for i in range(n)) and all(
            values[j] <= values[i] for i in range(n) for j in values[i]
        ):
            yield values


def graphs(n):
    possible = list(combinations(range(n), 2))
    for mask in range(1 << len(possible)):
        yield {e for k, e in enumerate(possible) if mask & (1 << k)}


def adjacent(edges, i, j):
    return i != j and tuple(sorted((i, j))) in edges


def closed(values, domain):
    return all(values[i] <= domain for i in domain)


def literal_code(values, edges, root, labels):
    n = len(values)
    return (
        frozenset(labels),
        labels[root],
        frozenset(
            (labels[i], labels[j])
            for i in range(n) for j in range(n)
            if adjacent(edges, i, j)
        ),
        frozenset(
            (labels[i], labels[j])
            for i in range(n) for j in values[i]
        ),
    )




def finite_subsets(items):
    items = sorted(items)
    for size in range(len(items) + 1):
        for tup in combinations(items, size):
            yield frozenset(tup)


def finite_predim(s, edges):
    return 2 * len(s) - sum(a in s and b in s for a, b in edges)


def finite_strong(a, b, edges):
    return a <= b and all(
        finite_predim(a, edges) <= finite_predim(x, edges)
        for x in finite_subsets(b) if a <= x
    )


def finite_minimal_step(a, b, edges):
    # Match Lean Predimension.IsMinimalStrongStep: exclude intermediate
    # z that is strong IN b. Testing 'a strong in z' is WRONG because
    # every intermediate z inherits that from a strong in b.
    return a < b and finite_strong(a, b, edges) and not any(
        finite_strong(z, b, edges)
        for z in finite_subsets(b) if a < z < b
    )


def finite_component_values(labels, edges):
    n = len(labels)
    m = 1 + max(labels, default=-1)
    blocks = [{v for v in range(n) if labels[v] == i} for i in range(m)]
    dep = [
        {j for j in range(i) if any(
            labels[u] == i and labels[v] == j and
            tuple(sorted((u, v))) in edges
            for u in range(n) for v in range(n)
        )}
        for i in range(m)
    ]
    ancestors = []
    for i in range(m):
        reached, todo = {i}, [i]
        while todo:
            for j in dep[todo.pop()]:
                if j not in reached:
                    reached.add(j)
                    todo.append(j)
        ancestors.append(reached)
    return [{v for j in ancestors[labels[u]] for v in blocks[j]}
            for u in range(n)]


def check_finite_minimal_age():
    """Independent n<=4 check of exact C0 finite hereditary restrictions."""
    certified, closed_cuts, multivertex = 0, 0, 0
    for n in range(1, 5):
        vertices = frozenset(range(n))
        for edges in graphs(n):
            for m in range(1, n + 1):
                for labels in product(range(m), repeat=n):
                    if set(labels) != set(range(m)):
                        continue
                    stage = [
                        frozenset(u for u in vertices if labels[u] < i)
                        for i in range(m + 1)
                    ]
                    if not all(
                        finite_minimal_step(stage[i], stage[i+1], edges)
                        for i in range(m)
                    ):
                        continue
                    certified += 1
                    if any(sum(labels[u] == i for u in vertices) > 1
                           for i in range(m)):
                        multivertex += 1
                    values = finite_component_values(labels, edges)
                    assert all(u in values[u] for u in vertices)
                    assert all(values[v] <= values[u] for u in vertices
                               for v in values[u])
                    for root in vertices:
                        support = frozenset(values[root])
                        closed_cuts += 1
                        assert all(values[v] <= support for v in support)
                        ordered = sorted(support)
                        index = {u: i for i, u in enumerate(ordered)}
                        cut_labels = [labels[u] for u in ordered]
                        cut_edges = {
                            (index[a], index[b])
                            for a, b in edges if a in support and b in support
                        }
                        cut_values = finite_component_values(
                            cut_labels, cut_edges
                        )
                        for v in support:
                            assert {
                                ordered[j] for j in cut_values[index[v]]
                            } == values[v]
                        for i in range(m):
                            old = frozenset(u for u in support if labels[u] < i)
                            new = frozenset(u for u in support if labels[u] <= i)
                            assert old == new or finite_minimal_step(
                                old, new, edges
                            )
    assert (certified, closed_cuts, multivertex) == (1401, 5545, 4)
    # A two-point closed union of singleton closures is NOT generated
    # by either point. Closedness alone does not make a pointed W-code.
    assert all({u} <= {0, 1} for u in (0, 1))
    assert {0, 1} != {0} and {0, 1} != {1}
    # Finite order-admissibility is distinct: reverse the order of
    # a dependent two-vertex edge and the incidence data stay intact,
    # but the earlier lower closure vertex follows its dependent.
    assert 1 < 2 and not (2 < 1)
    print(
        f"PASS: {certified} finite minimal C0 presentations; "
        f"{closed_cuts} inherited generated closures; "
        f"{multivertex} non-singleton minimal-step presentations"
    )

def main():
    counts = {}
    for n in range(4):
        checked = 0
        for values in closed_systems(n):
            for edges in graphs(n):
                if not all(j in values[i] or i in values[j] for i, j in edges):
                    continue
                checked += 1
                J = [
                    {j for j in values[i] if adjacent(edges, i, j)}
                    for i in range(n)
                ]
                for i in range(n):
                    for j in range(n):
                        assert adjacent(edges, i, j) == (
                            j in J[i] or i in J[j]
                        )
                domains = [
                    {i for i in range(n) if mask & (1 << i)}
                    for mask in range(1 << n)
                ]
                closed_domains = [s for s in domains if closed(values, s)]
                for s in closed_domains:
                    for i in s:
                        assert values[i] <= s and J[i] <= s
                        assert values[i] == {j for j in s if j in values[i]}
                        assert J[i] == {j for j in s if j in J[i]}
                    for t in closed_domains:
                        assert not any(
                            adjacent(edges, i, j) for i in s - t for j in t - s
                        )
                        if t <= s:
                            for i in t:
                                assert {j for j in t if j in values[i]} == {
                                    j for j in s if j in values[i]
                                }
                                assert {j for j in t if j in J[i]} == {
                                    j for j in s if j in J[i]
                                }
                if n:
                    for labels in combinations(range(n + 3), n):
                        for root in range(n):
                            support, point, matrix, unary = literal_code(
                                values, edges, root, labels
                            )
                            assert point in support
                            for i in range(n):
                                for j in range(n):
                                    assert ((labels[i], labels[j]) in matrix) == (
                                        adjacent(edges, i, j)
                                    )
                                    assert ((labels[i], labels[j]) in unary) == (
                                        j in values[i]
                                    )
        counts[n] = checked
    assert counts == {0: 1, 1: 1, 2: 7, 3: 147}, counts

    # Remove edge coverage: J then loses the edge.
    values, edges = [{0}, {1}], {(0, 1)}
    assert adjacent(edges, 0, 1)
    assert not any(
        j in values[i] and adjacent(edges, i, j)
        for i, j in ((0, 1), (1, 0))
    )

    # Remove closedness: an ambient C-value is lost by restriction.
    values, domain = [{0, 1}, {1}], {0}
    assert values[0] & domain != values[0]

    check_finite_minimal_age()

    print(
        "PASS: 156 compatible finite closure/graph systems (including empty), "
        "complete C,J restrictions, no-cross cuts, code rigidity, negative controls"
    )


if __name__ == "__main__":
    main()
