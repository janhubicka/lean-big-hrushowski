"""Exhaustively check tagged free graph amalgams in canonical finite normal form.

Input graphs have vertex sets P+L and P+R; the output carrier is P+(L+R).
Different tails cannot be identified. The independent implementation uses
pairs of explicit tagged Python vertices and enumerates all graphs with
|P|, |L|, |R| at most two. Not a replacement for the Lean proof.
"""
from itertools import combinations

stats = {"all_inputs": 0, "compatible": 0, "strong_join_cases": 0,
         "no_cross": 0}

for np in range(3):
    for nl in range(3):
        for nr in range(3):
            p = [("p", i) for i in range(np)]
            l = [("l", i) for i in range(nl)]
            r = [("r", i) for i in range(nr)]
            a = p + l
            b = p + r
            carrier = p + l + r
            left_pairs = list(combinations(a, 2))
            right_pairs = list(combinations(b, 2))
            base_pairs = {frozenset(edge) for edge in combinations(p, 2)}

            def delta(vertices, edges):
                return 2 * len(vertices) - sum(edge <= vertices for edge in edges)

            def sparse(vertices, edges):
                return all(
                    delta(set(subset), edges) >= 0
                    for k in range(len(vertices) + 1)
                    for subset in combinations(vertices, k)
                )

            def strong(base, vertices, edges):
                return all(
                    delta(set(base), edges) <= delta(set(subset), edges)
                    for k in range(len(base), len(vertices) + 1)
                    for subset in combinations(vertices, k)
                    if set(base) <= set(subset)
                )

            for mask_left in range(1 << len(left_pairs)):
                el = {
                    frozenset(edge)
                    for k, edge in enumerate(left_pairs)
                    if mask_left >> k & 1
                }
                for mask_right in range(1 << len(right_pairs)):
                    stats["all_inputs"] += 1
                    er = {
                        frozenset(edge)
                        for k, edge in enumerate(right_pairs)
                        if mask_right >> k & 1
                    }
                    if (el & base_pairs) != (er & base_pairs):
                        continue
                    stats["compatible"] += 1
                    join = el | er
                    assert {e for e in join if e <= set(a)} == el
                    assert {e for e in join if e <= set(b)} == er
                    assert not any(
                        frozenset((x, y)) in join for x in l for y in r
                    )
                    assert set(a) & set(b) == set(p)
                    stats["no_cross"] += 1
                    if (sparse(a, el) and sparse(b, er)
                            and strong(p, a, el) and strong(p, b, er)):
                        assert sparse(carrier, join)
                        assert strong(a, carrier, join)
                        assert strong(b, carrier, join)
                        stats["strong_join_cases"] += 1

# Negative control: incompatible base graphs cannot both embed inducedly.
u, v = ("p", 0), ("p", 1)
left_edges = {frozenset((u, v))}
right_edges = set()
assert left_edges != right_edges
assert (left_edges | right_edges) != right_edges

assert stats == {
    "all_inputs": 5613,
    "compatible": 2875,
    "strong_join_cases": 2729,
    "no_cross": 2875,
}, stats
print(stats)
