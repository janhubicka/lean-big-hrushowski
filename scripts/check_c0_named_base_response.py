#!/usr/bin/env python3
"""Adversarial finite check of closed-base response composition.

For every canonical finite C0 graph with <=4 vertices and unused slots
allowed, choose closed induced stage T and a closed requested factor B.
Relabel B independently, and give the ambient canonical extension K a
new injective numeric placement which fixes every old T label exactly.

Check the SAME composed map on B preserves and reflects adjacency,
transports its whole canonical value, and fixes each common-base point.
This finite test does not establish existence of a countable response.
"""
from itertools import combinations, permutations, product

stats = dict(graphs=0, canonical_presentations=0,
             closed_stage_factor_pairs=0, composed_maps=0,
             induced_pair_checks=0, complete_value_checks=0,
             base_fix_checks=0, nonclosed_negative_controls=0)

def bits(s):
    return [x for x in range(s.bit_length()) if s >> x & 1]

def sub(a, b):
    return a & ~b == 0

for n in range(5):
    edges_list = list(combinations(range(n), 2))
    whole = (1 << n) - 1
    for mask in range(1 << len(edges_list)):
        stats["graphs"] += 1
        edges = {e for i, e in enumerate(edges_list) if mask >> i & 1}

        def predim(s):
            return 2 * s.bit_count() - sum(
                bool(s >> u & 1) and bool(s >> v & 1)
                for u, v in edges)

        def strong(a, b):
            return sub(a, b) and all(
                predim(a) <= predim(s)
                for s in range(1 << n) if sub(a, s) and sub(s, b))

        def minimal(a, b):
            return (
                a != b and strong(a, b) and
                all(s == a or s == b for s in range(1 << n)
                    if sub(a, s) and sub(s, b) and strong(s, b)))

        for levels in range(1, max(2, n + 1)):
            for index in product(range(levels), repeat=n):
                cuts = [
                    sum(1 << v for v in range(n) if index[v] < k)
                    for k in range(levels + 1)]
                if not all(cuts[k] == cuts[k + 1] or
                           minimal(cuts[k], cuts[k + 1])
                           for k in range(levels)):
                    continue
                stats["canonical_presentations"] += 1

                def values(domain):
                    result = {}
                    for x in bits(domain):
                        reached = {index[x]}
                        while True:
                            old = len(reached)
                            for u, v in edges:
                                if not (domain >> u & 1 and domain >> v & 1):
                                    continue
                                if index[u] in reached and index[v] < index[u]:
                                    reached.add(index[v])
                                if index[v] in reached and index[u] < index[v]:
                                    reached.add(index[u])
                            if len(reached) == old:
                                break
                        result[x] = {y for y in bits(domain)
                                     if index[y] in reached}
                    return result

                full_value = values(whole)
                closed = [s for s in range(1 << n) if all(
                    all(s >> v & 1 for v in full_value[x])
                    for x in bits(s))]
                for t in closed:
                    for b in closed:
                        stats["closed_stage_factor_pairs"] += 1
                        B = bits(b)
                        base = set(bits(t & b))
                        bvalue = values(b)
                        assert all(bvalue[x] == full_value[x] for x in B)
                        # Test independent permutations of the right
                        # factor's *abstract* coordinates.
                        candidates = list(permutations(B))
                        for order in candidates:
                            # Abstract coordinate a represents order[a]
                            g = dict(enumerate(order))
                            inv = {v: a for a, v in g.items()}
                            # Genuine injective target-stage response:
                            # old stage T labels must be literally fixed.
                            response = {
                                x: x if t >> x & 1 else n + 2*x + 1
                                for x in range(n)}
                            assert len(set(response.values())) == n
                            h = {a: response[g[a]] for a in g}
                            assert len(set(h.values())) == len(h)
                            stats["composed_maps"] += 1

                            # Ambient graph and full unary operation are
                            # the direct transport of K under response.
                            ambient_edges = {
                                frozenset((response[u], response[v]))
                                for u, v in edges}
                            ambient_value = {
                                response[x]: {response[v] for v in full_value[x]}
                                for x in range(n)}
                            for a in g:
                                for c in g:
                                    adjB = frozenset((g[a], g[c])) in {
                                        frozenset(e) for e in edges}
                                    adjAmbient = frozenset((h[a], h[c])) in ambient_edges
                                    assert adjB == adjAmbient
                                    stats["induced_pair_checks"] += 1
                                expected = {h[inv[x]] for x in bvalue[g[a]]}
                                assert ambient_value[h[a]] == expected
                                stats["complete_value_checks"] += 1
                            for x in base:
                                abstract = inv[x]
                                assert h[abstract] == x
                                stats["base_fix_checks"] += 1

                for b in range(1 << n):
                    if b in closed:
                        continue
                    restricted = values(b)
                    if any(restricted[x] != full_value[x] for x in bits(b)):
                        stats["nonclosed_negative_controls"] += 1

assert stats["canonical_presentations"] > 0, stats
assert stats["composed_maps"] > 0, stats
assert stats["nonclosed_negative_controls"] > 0, stats
print("Track A named-base response finite composition:", stats)
