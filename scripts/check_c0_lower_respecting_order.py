#!/usr/bin/env python3
"""Exhaustively challenge the finite C0 strict-dependency order criterion.

All simple graphs on up to four labelled vertices, all old component
index maps into [0,n), and all new permutations of the nonempty
component fibres are considered. Empty index levels are allowed.
The tests compare *complete* transitive canonical values, not just
direct backward neighbours.
"""
from itertools import combinations, permutations, product

stats = dict(graphs=0, old_indices=0, alternate_orders=0,
             admissible_orders=0, vertex_value_checks=0,
             rejected_bad_orders=0)

def canonical_values(n, edges, index):
    values = []
    for x in range(n):
        reached = {index[x]}
        while True:
            old = len(reached)
            for a, b in edges:
                if index[a] in reached and index[b] < index[a]:
                    reached.add(index[b])
                if index[b] in reached and index[a] < index[b]:
                    reached.add(index[a])
            if len(reached) == old:
                break
        values.append(frozenset(v for v in range(n)
                                if index[v] in reached))
    return values

for n in range(1, 5):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        edges = [pair for k, pair in enumerate(pairs)
                 if mask >> k & 1]
        stats["graphs"] += 1
        for old_index in product(range(n), repeat=n):
            stats["old_indices"] += 1
            old_values = canonical_values(n, edges, old_index)
            classes = sorted(set(old_index))
            for ranks in permutations(range(len(classes))):
                rank = dict(zip(classes, ranks))
                new_index = tuple(rank[i] for i in old_index)
                # By construction, full index equality is preserved.
                assert all((old_index[u] == old_index[v]) ==
                           (new_index[u] == new_index[v])
                           for u in range(n) for v in range(n))
                stats["alternate_orders"] += 1
                good = all(
                    new_index[v] < new_index[u]
                    for u in range(n) for v in old_values[u]
                    if old_index[u] != old_index[v]
                )
                new_values = canonical_values(n, edges, new_index)
                if good:
                    assert old_values == new_values, (
                        n, edges, old_index, new_index,
                        old_values, new_values)
                    stats["admissible_orders"] += 1
                    stats["vertex_value_checks"] += n
                elif old_values != new_values:
                    stats["rejected_bad_orders"] += 1

# Negative regression: reversing an actual dependency fails.
edges = [(0, 1)]
assert canonical_values(2, edges, (1, 0)) != (
    canonical_values(2, edges, (0, 1))
)
assert stats["admissible_orders"] > 0
assert stats["rejected_bad_orders"] > 0
print("C0 lower-respecting chronology regression", stats)
