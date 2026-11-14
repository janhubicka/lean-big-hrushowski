#!/usr/bin/env python3
"""Independent finite regression of literal C0 closed-age transport.

Enumerate every simple graph on at most four labelled vertices and
every κ:V→Fin m, 1<=m<=|V|+1, retaining empty-or-minimal strong
presentations. For each complete-C-closed set s, independently
relabel its vertices through every permutation of its literal
carrier. Check on the relabelled induced graph:
(1) the original index restricts to an empty-or-minimal strong chain;
(2) every complete canonical unary value maps *exactly* to its
    original full C value under the chosen finite equivalence.

Includes truly unused index slots, the empty carrier and
nonclosed negative controls. This is finite falsification, not
a proof of the countable theorem.
"""
from functools import lru_cache
from itertools import combinations, permutations, product

stats = dict(graphs=0, indexings=0, canonical=0, closed_sets=0,
             relabellings=0, step_checks=0, value_checks=0,
             missing_values_nonclosed=0)

def subset(a, b):
    return a & ~b == 0

def minimal_steps_for_edges(n, edges):
    @lru_cache(None)
    def delta(s):
        return 2 * s.bit_count() - sum(
            (s >> x & 1) and (s >> y & 1) for x, y in edges)

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
    return minimal

def full_value(n, edges, levels, x):
    reached = {levels[x]}
    while True:
        old = len(reached)
        for u, v in edges:
            if levels[u] in reached and levels[v] < levels[u]:
                reached.add(levels[v])
            if levels[v] in reached and levels[u] < levels[v]:
                reached.add(levels[u])
        if len(reached) == old:
            return {y for y in range(n) if levels[y] in reached}

for n in range(5):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        stats["graphs"] += 1
        edges = [p for j, p in enumerate(pairs) if mask >> j & 1]
        edge_set = {frozenset(e) for e in edges}
        minimal = minimal_steps_for_edges(n, edges)

        for m in range(1, max(1, n + 1) + 1):
            for index in product(range(m), repeat=n):
                stats["indexings"] += 1
                oldcuts = [sum(1 << x for x in range(n) if index[x] < k)
                           for k in range(m + 1)]
                if not all(oldcuts[k] == oldcuts[k + 1] or
                           minimal(oldcuts[k], oldcuts[k + 1])
                           for k in range(m)):
                    continue
                stats["canonical"] += 1
                original = [full_value(n, edges, index, x)
                            for x in range(n)]

                for mask_s in range(1 << n):
                    members = [x for x in range(n) if mask_s >> x & 1]
                    s = set(members)
                    if any(not original[x] <= s for x in members):
                        stats["missing_values_nonclosed"] += 1
                        continue
                    stats["closed_sets"] += 1

                    for perm in permutations(members):
                        q = len(perm)
                        vals = [index[v] for v in perm]
                        e_relabel = [
                            (a, b) for a, b in combinations(range(q), 2)
                            if frozenset((perm[a], perm[b])) in edge_set]
                        min_new = minimal_steps_for_edges(q, e_relabel)

                        cuts = [
                            sum(1 << a for a in range(q) if vals[a] < k)
                            for k in range(m + 1)]
                        for k in range(m):
                            assert cuts[k] == cuts[k + 1] or min_new(
                                cuts[k], cuts[k + 1]), (
                                    n, edges, index, mask_s, perm, k)
                            stats["step_checks"] += 1

                        for a, x in enumerate(perm):
                            current = full_value(q, e_relabel, vals, a)
                            actual = {perm[b] for b in current}
                            assert actual == original[x], (
                                n, edges, index, mask_s, perm, x,
                                actual, original[x])
                            stats["value_checks"] += 1
                        stats["relabellings"] += 1

assert stats["graphs"] == 76, stats
assert stats["indexings"] == 63488, stats
assert stats["canonical"] == 8404, stats
assert stats["closed_sets"] == 67287, stats
assert stats["relabellings"] > stats["closed_sets"], stats
assert stats["missing_values_nonclosed"] > 0, stats
print("literal closed finite C0 age transport:", stats)
