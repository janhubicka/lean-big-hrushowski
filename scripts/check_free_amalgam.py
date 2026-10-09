"""Exhaustive finite check of predimension under no-crossing unions.

Every labelled simple graph on at most five vertices is examined.
Tests modularity and self-sufficiency of both factors when the common
intersection is strong in the opposite factor.
This is a diagnostic, not a replacement for the Lean proof.
"""
from itertools import combinations

stats = {
    "graphs": 0, "no_cross_pairs": 0, "modular_pairs": 0,
    "strong_left_transfer": 0, "strong_right_transfer": 0,
}
for n in range(6):
    edges = list(combinations(range(n), 2))
    subsets = list(range(1 << n))
    for graph in range(1 << len(edges)):
        stats["graphs"] += 1
        selected = [
            (u, v) for i, (u, v) in enumerate(edges) if graph & (1 << i)
        ]
        delta = [
            2 * s.bit_count() -
            sum(bool(s & (1 << u)) and bool(s & (1 << v))
                for u, v in selected)
            for s in subsets
        ]

        def strong(a, b):
            return a & b == a and all(
                delta[a] <= delta[c]
                for c in subsets if c & a == a and c & b == c
            )

        for a in subsets:
            for b in subsets:
                union = a | b
                crossing = any(
                    (union & (1 << u)) and (union & (1 << v))
                    and not ((a & (1 << u)) and (a & (1 << v)))
                    and not ((b & (1 << u)) and (b & (1 << v)))
                    for u, v in selected
                )
                if crossing:
                    continue
                stats["no_cross_pairs"] += 1
                overlap = a & b
                assert delta[union] + delta[overlap] == delta[a] + delta[b]
                stats["modular_pairs"] += 1
                if strong(overlap, b):
                    assert strong(a, union), ("left", n, graph, a, b)
                    stats["strong_left_transfer"] += 1
                if strong(overlap, a):
                    assert strong(b, union), ("right", n, graph, a, b)
                    stats["strong_right_transfer"] += 1

assert stats == {
    "graphs": 1100,
    "no_cross_pairs": 635495,
    "modular_pairs": 635495,
    "strong_left_transfer": 624416,
    "strong_right_transfer": 624416,
}
print(stats)
