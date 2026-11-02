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

    print(
        "PASS: 156 compatible finite closure/graph systems (including empty), "
        "complete C,J restrictions, no-cross cuts, code rigidity, negative controls"
    )


if __name__ == "__main__":
    main()
