#!/usr/bin/env python3
"""Exhaustively test finite one-component minimal strongness for |V|<=4.

Enumerate every undirected simple graph and index map into finite
ordinals with possible empty slots. Keep exactly presentations whose
nonempty prefix increments are minimal strong, then test all closed S
whose complement is one complete component. Diagnostic only, not Lean.
"""
from functools import lru_cache
from itertools import combinations, product

stats = {
    "graphs": 0,
    "presentations": 0,
    "valid_presentations": 0,
    "closed_single_complement": 0,
}

for n in range(5):
    pairs = list(combinations(range(n), 2))
    for edge_code in range(1 << len(pairs)):
        stats["graphs"] += 1
        edges = {e for i, e in enumerate(pairs) if edge_code & (1 << i)}
        subsets = range(1 << n)

        @lru_cache(None)
        def predim(s):
            return 2 * s.bit_count() - sum(
                bool(s >> u & 1) and bool(s >> v & 1) for u, v in edges
            )

        def is_subset(a, b):
            return (a & ~b) == 0

        @lru_cache(None)
        def is_strong(a, b):
            return is_subset(a, b) and all(
                predim(c) >= predim(a)
                for c in subsets
                if is_subset(a, c) and is_subset(c, b)
            )

        def is_minimal_strong(a, b):
            return (
                is_strong(a, b)
                and a != b
                and all(
                    c == a or c == b
                    for c in subsets
                    if is_subset(a, c)
                    and is_subset(c, b)
                    and is_strong(c, b)
                )
            )

        for m in range(1, max(2, n + 1)):
            for idx in product(range(m), repeat=n):
                stats["presentations"] += 1
                old = [
                    sum(1 << v for v in range(n) if idx[v] < j)
                    for j in range(m + 1)
                ]
                if not all(
                    old[j] == old[j + 1]
                    or is_minimal_strong(old[j], old[j + 1])
                    for j in range(m)
                ):
                    continue
                stats["valid_presentations"] += 1
                blocks = [
                    sum(1 << v for v in range(n) if idx[v] == j)
                    for j in range(m)
                ]
                depends = [{j} for j in range(m)]
                for u, v in edges:
                    a, b = idx[u], idx[v]
                    if a != b:
                        depends[max(a, b)].add(min(a, b))
                ancestors = [set(d) for d in depends]
                for j in range(m):
                    for i in list(ancestors[j]):
                        ancestors[j].update(ancestors[i])
                closure = [
                    sum(blocks[j] for j in ancestors[idx[x]])
                    for x in range(n)
                ]
                for s in subsets:
                    if not all(
                        is_subset(closure[x], s)
                        for x in range(n)
                        if s >> x & 1
                    ):
                        continue
                    for x in range(n):
                        if (((1 << n) - 1) & ~s) != blocks[idx[x]]:
                            continue
                        stats["closed_single_complement"] += 1
                        assert is_minimal_strong(s, (1 << n) - 1), (
                            n, edges, m, idx, s, x, blocks, closure
                        )

assert stats == {
    "graphs": 76,
    "presentations": 22956,
    "valid_presentations": 1438,
    "closed_single_complement": 2899,
}, stats
print(stats)
