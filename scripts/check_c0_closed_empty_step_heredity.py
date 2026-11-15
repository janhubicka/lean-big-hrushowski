#!/usr/bin/env python3
"""Exhaustive finite falsification of complete C0 closed heredity with empty levels.

Enumerate every simple graph on <=4 labelled vertices and every map
κ:V→Fin m for 1<=m<=|V|+1 (unused index positions allowed). Retain
exactly empty-or-minimal-strong sequences. For every finite subset s
closed under the *entire* canonical C value, verify that the induced
graph on s has the same complete C values and the restricted index
has empty-or-minimal-strong increments. Nonclosed subsets with missing
full predecessors serve as independent negative controls.

The finite regression is not a proof of the general Lean theorem.
"""
from itertools import combinations, product
from functools import lru_cache

stats = dict(
    graphs=0, indexings=0, admissible=0, closed=0, cut_checks=0,
    value_checks=0, nonclosed_lost=0, empty_cuts=0,
)

def subset(a, b):
    return a & ~b == 0

for n in range(5):
    edges_all = list(combinations(range(n), 2))
    full = (1 << n) - 1
    for mask in range(1 << len(edges_all)):
        stats["graphs"] += 1
        edges = [e for i, e in enumerate(edges_all) if mask >> i & 1]

        @lru_cache(None)
        def delta(s):
            return 2 * s.bit_count() - sum(
                (s >> a & 1) and (s >> b & 1) for a, b in edges)

        @lru_cache(None)
        def strong(a, b):
            return subset(a, b) and all(
                delta(a) <= delta(c) for c in range(1 << n)
                if subset(a, c) and subset(c, b))

        @lru_cache(None)
        def minimal(a, b):
            return a != b and strong(a, b) and all(
                c in (a, b) for c in range(1 << n)
                if subset(a, c) and subset(c, b) and strong(c, b))

        for m in range(1, max(1, n + 1) + 1):
            for idx in product(range(m), repeat=n):
                stats["indexings"] += 1
                cuts = [
                    sum(1 << x for x in range(n) if idx[x] < k)
                    for k in range(m + 1)]
                if not all(cuts[k] == cuts[k + 1] or
                           minimal(cuts[k], cuts[k + 1]) for k in range(m)):
                    continue
                stats["admissible"] += 1

                def value_on(x, domain):
                    reached = {idx[x]}
                    while True:
                        before = len(reached)
                        for u, v in edges:
                            if not (domain >> u & 1 and domain >> v & 1):
                                continue
                            if idx[u] in reached and idx[v] < idx[u]:
                                reached.add(idx[v])
                            if idx[v] in reached and idx[u] < idx[v]:
                                reached.add(idx[u])
                        if len(reached) == before:
                            break
                    return sum(1 << y for y in range(n)
                               if domain >> y & 1 and idx[y] in reached)

                complete = [value_on(x, full) for x in range(n)]
                for s in range(1 << n):
                    closed = all(subset(complete[x], s)
                                 for x in range(n) if s >> x & 1)
                    if not closed:
                        if any(not subset(complete[x], s)
                               for x in range(n) if s >> x & 1):
                            stats["nonclosed_lost"] += 1
                        continue
                    stats["closed"] += 1
                    scuts = [
                        sum(1 << x for x in range(n)
                            if s >> x & 1 and idx[x] < k)
                        for k in range(m + 1)]
                    for k in range(m):
                        if scuts[k] == scuts[k + 1]:
                            stats["empty_cuts"] += 1
                        else:
                            assert minimal(scuts[k], scuts[k + 1]), (
                                n, edges, idx, s, k)
                        stats["cut_checks"] += 1
                    for x in range(n):
                        if s >> x & 1:
                            assert value_on(x, s) == complete[x], (
                                n, edges, idx, s, x,
                                value_on(x, s), complete[x])
                            stats["value_checks"] += 1

expected = dict(
    graphs=76, indexings=63488, admissible=8404, closed=67287,
    cut_checks=323577, value_checks=134631,
    nonclosed_lost=65008, empty_cuts=189106,
)
assert stats == expected, (stats, expected)
print("C0 canonical closed empty-or-minimal restriction:", stats)
