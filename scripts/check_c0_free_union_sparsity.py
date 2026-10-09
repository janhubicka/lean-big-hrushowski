"""Exhaustive test of 2-sparsity in strong no-crossing graph unions.

All simple labelled graphs on at most five vertices are examined. The
checks validate finite arithmetic, not the general Lean proof.
"""
from itertools import combinations

stats = {
    "graphs": 0, "no_cross_pairs": 0,
    "sparse_left_strong_base": 0,
    "sparse_right_strong_base": 0, "strong_extensions": 0,
}
for n in range(6):
    pairs = list(combinations(range(n), 2))
    subsets = list(range(1 << n))
    for graph in range(1 << len(pairs)):
        stats["graphs"] += 1
        edges = [(u, v) for k, (u, v) in enumerate(pairs)
                 if graph & (1 << k)]
        delta = [
            2 * s.bit_count() -
            sum(bool(s & (1 << u)) and bool(s & (1 << v))
                for u, v in edges)
            for s in subsets
        ]
        sparse = [
            all(delta[t] >= 0 for t in subsets if t & s == t)
            for s in subsets
        ]

        def strong(a, b):
            return a & b == a and all(
                delta[a] <= delta[t]
                for t in subsets if t & a == a and t & b == t
            )

        for a in subsets:
            for b in subsets:
                if strong(a, b) and sparse[a]:
                    assert sparse[b], ("strong extension", n, graph, a, b)
                    stats["strong_extensions"] += 1
                union = a | b
                crossing = any(
                    bool(union & (1 << u)) and bool(union & (1 << v))
                    and not (bool(a & (1 << u)) and bool(a & (1 << v)))
                    and not (bool(b & (1 << u)) and bool(b & (1 << v)))
                    for u, v in edges
                )
                if crossing:
                    continue
                stats["no_cross_pairs"] += 1
                overlap = a & b
                if sparse[a] and strong(overlap, b):
                    assert sparse[union], ("left factor", n, graph, a, b)
                    stats["sparse_left_strong_base"] += 1
                if sparse[b] and strong(overlap, a):
                    assert sparse[union], ("right factor", n, graph, a, b)
                    stats["sparse_right_strong_base"] += 1

assert stats == {
    "graphs": 1100,
    "no_cross_pairs": 635495,
    "sparse_left_strong_base": 624416,
    "sparse_right_strong_base": 624416,
    "strong_extensions": 244695,
}
print(stats)
