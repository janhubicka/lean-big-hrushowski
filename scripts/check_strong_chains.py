"""Independent finite regression for local-to-global strong chains.

For every labelled simple graph on at most four vertices, enumerate
all chains A <= B <= C, where C contains every vertex. Check that A
is strong in the full graph and that stage inclusion is monotone.
This is diagnostic evidence, not an infinite-model proof.
"""
from itertools import combinations

stats = {"graphs": 0, "covering_chains": 0, "strong_pairs": 0}
for n in range(5):
    edges = list(combinations(range(n), 2))
    full = (1 << n) - 1
    masks = list(range(1 << n))
    for graph in range(1 << len(edges)):
        stats["graphs"] += 1
        delta = [
            2 * s.bit_count() -
            sum(
                bool(graph & (1 << i)) and bool(s & (1 << u))
                and bool(s & (1 << v))
                for i, (u, v) in enumerate(edges)
            )
            for s in masks
        ]

        def strong(a, b):
            if a & b != a:
                return False
            return all(
                delta[a] <= delta[c]
                for c in masks if c & a == a and c & b == c
            )

        for a in masks:
            for b in masks:
                if strong(a, b):
                    stats["strong_pairs"] += 1
                if strong(a, b) and strong(b, full):
                    assert strong(a, full), (
                        "failure of finite strong-chain transfer",
                        n, graph, a, b,
                    )
                    assert (a & b) == a
                    stats["covering_chains"] += 1

assert stats["graphs"] == 76
assert stats["covering_chains"] == 5074
print(stats)
