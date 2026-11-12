#!/usr/bin/env python3
"""Independent exhaustive regression: fair prefixes are canonical finite C0 stages.

All simple graphs and indexings on at most four vertices (including
unused index levels); retain only the empty-or-minimal-strong stage
presentations. No Lean definitions or PR implementation are imported.
"""
from functools import lru_cache
from itertools import combinations, product

stats = dict(graphs=0, indexings=0, valid=0, fair_cuts=0,
             induced_minimal=0, full_values=0, image_cuts=0)

for n in range(5):
    pairs = list(combinations(range(n), 2))
    subsets = range(1 << n)
    full = (1 << n) - 1
    for mask in range(1 << len(pairs)):
        stats["graphs"] += 1
        edges = [p for i, p in enumerate(pairs) if mask >> i & 1]

        @lru_cache(None)
        def delta(s):
            return 2 * s.bit_count() - sum(
                bool(s >> x & 1) and bool(s >> y & 1)
                for x, y in edges)

        def subset(a, b):
            return (a & ~b) == 0

        @lru_cache(None)
        def strong(a, b):
            return subset(a, b) and all(
                delta(s) >= delta(a) for s in subsets
                if subset(a, s) and subset(s, b))

        def minimal(a, b):
            return (
                strong(a, b) and a != b and
                all(s == a or s == b for s in subsets
                    if subset(a, s) and subset(s, b) and strong(s, b))
            )

        def canonical(ix, domain):
            result = {}
            occupied = {ix[v] for v in range(n) if domain >> v & 1}
            for x in range(n):
                if not (domain >> x & 1):
                    continue
                reached = {ix[x]}
                while True:
                    before = len(reached)
                    for u, v in edges:
                        if not (domain >> u & 1 and domain >> v & 1):
                            continue
                        if ix[u] in reached and ix[v] < ix[u]:
                            reached.add(ix[v])
                        if ix[v] in reached and ix[u] < ix[v]:
                            reached.add(ix[u])
                    if len(reached) == before:
                        break
                result[x] = sum(1 << v for v in range(n)
                                if domain >> v & 1 and ix[v] in reached)
                assert reached <= occupied
            return result

        for m in range(1, max(2, n + 1)):
            for ix in product(range(m), repeat=n):
                stats["indexings"] += 1
                old = [sum(1 << x for x in range(n) if ix[x] < j)
                       for j in range(m + 1)]
                if not all(old[j] == old[j + 1] or
                           minimal(old[j], old[j + 1])
                           for j in range(m)):
                    continue
                stats["valid"] += 1
                complete = canonical(ix, full)
                q = 0
                births = [-1] * n
                prefixes = [q]
                while q != full:
                    eligible = []
                    for x in range(n):
                        if q >> x & 1:
                            continue
                        comp = sum(1 << y for y in range(n)
                                   if complete[y] == complete[x])
                        lower = complete[x] & ~comp
                        if subset(lower, q):
                            eligible.append(x)
                    assert eligible, (n, edges, ix, q)
                    x = min(eligible)
                    comp = sum(1 << y for y in range(n)
                               if complete[y] == complete[x])
                    assert not (q & comp)
                    for y in range(n):
                        if comp >> y & 1:
                            assert births[y] < 0
                            births[y] = len(prefixes) - 1
                    new = q | comp
                    assert minimal(q, new), (n, edges, ix, q, new)
                    stats["induced_minimal"] += 1
                    q = new
                    prefixes.append(q)
                assert q == full
                for k, q in enumerate(prefixes):
                    assert all(complete[x] & ~q == 0
                               for x in range(n) if q >> x & 1)
                    curr = canonical(births, q)
                    for x in range(n):
                        if q >> x & 1:
                            assert curr[x] == complete[x], (
                                n, edges, ix, births, k, x)
                            stats["full_values"] += 1
                    for j in range(k + 1):
                        cut = sum(1 << x for x in range(n)
                                  if q >> x & 1 and births[x] < j)
                        assert cut == prefixes[j], (
                            n, edges, ix, births, j, k)
                        stats["image_cuts"] += 1
                    for j in range(k):
                        assert minimal(prefixes[j], prefixes[j + 1])
                    stats["fair_cuts"] += 1

# A real cross-component edge must not have its precedence reversed.
assert canonical((1, 0), 0b11) != canonical((0, 1), 0b11)
assert stats["valid"] > 0 and stats["full_values"] > 0
print("Track A fair canonical presentations exhaustive check:", stats)
