#!/usr/bin/env python3
"""Exhaustive independent falsification of complete-unary finite layer claims.

All set-valued unary functions on 0..4 points are inspected. Only
reflexive-transitive functions are checked for closed finite prefix
unions, component-saturated layers, strict predecessor rank descent,
and all complete-unary rank cuts. Diagnostic, not Lean kernel checking.
"""
from itertools import product

stats = dict(operations=0, complete=0, layer_checks=0,
             component_checks=0, predecessors=0, rank_cuts=0,
             segments_inspected=0, lower_closed_segments=0)

for n in range(5):
    for C in product(range(1 << n), repeat=n):
        stats["operations"] += 1
        if not all(C[x] & (1 << x) for x in range(n)):
            continue
        if not all(
            (not C[x] & (1 << y)) or not (C[y] & ~C[x])
            for x in range(n) for y in range(n)
        ):
            continue
        stats["complete"] += 1
        components = [
            {y for y in range(n) if C[y] == C[x]} for x in range(n)
        ]

        def closed(s):
            return all(
                not(s >> x & 1) or (C[x] & ~s) == 0
                for x in range(n)
            )

        for k in range(n + 1):
            S = 0
            for i in range(k):
                S |= C[i]
            T = S | (C[k] if k < n else 0)
            layer = T & ~S
            assert closed(S) and closed(T)
            stats["layer_checks"] += 1
            for x in range(n):
                if not (layer >> x & 1):
                    continue
                stats["component_checks"] += 1
                assert all((layer >> y & 1) for y in components[x])
                for y in range(n):
                    if (C[x] >> y & 1) and y not in components[x]:
                        stats["predecessors"] += 1
                        assert (S >> y & 1) or (
                            (layer >> y & 1)
                            and C[y].bit_count() < C[x].bit_count()
                        )
            for rank in range(n + 1):
                rankcut = S
                for x in range(n):
                    if (layer >> x & 1) and C[x].bit_count() <= rank:
                        rankcut |= 1 << x
                stats["rank_cuts"] += 1
                assert closed(rankcut), (n, C, k, rank, rankcut)
            for t in range(1 << n):
                if t & ~layer:
                    continue
                stats["segments_inspected"] += 1
                whole = all(
                    all(t >> y & 1 for y in components[x])
                    for x in range(n) if t >> x & 1
                )
                lower = all(
                    (t >> y & 1)
                    or C[y].bit_count() >= C[x].bit_count()
                    for x in range(n) if t >> x & 1
                    for y in range(n) if layer >> y & 1
                )
                if whole and lower:
                    stats["lower_closed_segments"] += 1
                    assert closed(S | t), (n, C, k, t)

expected = dict(operations=66067, complete=390, layer_checks=1906,
                component_checks=1516, predecessors=1250, rank_cuts=9380,
                segments_inspected=4562, lower_closed_segments=3289)
assert stats == expected, (stats, expected)
print(stats)
