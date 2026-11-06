#!/usr/bin/env python3
"""Finite adversarial tests of local representative order transport.

Enumerate all extensive/transitive complete unary closures and edge-covered
simple graphs on 1-3 vertices, every proper complete-value-closed lower part
whose remaining vertices generate the whole local structure, each compatible
reference order, and all pairs of permutations transporting that reference.
A transported order is *chosen*, not invariant under every raw automorphism.
"""
from itertools import combinations, permutations, product


def closures(n):
    for masks in product(range(1 << n), repeat=n):
        value = [frozenset(v for v in range(n) if masks[u] >> v & 1)
                 for u in range(n)]
        if all(u in value[u] for u in range(n)) and all(
                value[v] <= value[u] for u in range(n) for v in value[u]):
            yield value


def graphs(n):
    possible = list(combinations(range(n), 2))
    for mask in range(1 << len(possible)):
        yield frozenset(e for i, e in enumerate(possible) if mask >> i & 1)


def test():
    records = orders = transports = comparisons = 0
    for n in range(1, 4):
        U = frozenset(range(n))
        for value in closures(n):
            for edges in graphs(n):
                if any(v not in value[u] and u not in value[v]
                       for u, v in edges):
                    continue
                for mask in range((1 << n) - 1):
                    lower = frozenset(u for u in U if mask >> u & 1)
                    if any(not value[u] <= lower for u in lower):
                        continue
                    if any(value[b] != U for b in U - lower):
                        continue
                    records += 1
                    for reference_order in permutations(range(n)):
                        rank = {u: i for i, u in enumerate(reference_order)}
                        if any(rank[p] >= rank[b] for p in lower
                               for b in U - lower):
                            continue
                        orders += 1
                        for fvalues in permutations(range(n)):
                            f = dict(enumerate(fvalues))
                            fi = {f[u]: u for u in U}
                            lower_f = frozenset(f[u] for u in lower)
                            value_f = {
                                f[u]: frozenset(f[v] for v in value[u])
                                for u in U
                            }
                            edges_f = frozenset(tuple(sorted((f[u], f[v])))
                                                for u, v in edges)
                            assert all(value_f[v] <= lower_f for v in lower_f)
                            assert all(value_f[v] == U for v in U - lower_f)
                            assert all(rank[fi[p]] < rank[fi[b]]
                                       for p in lower_f for b in U - lower_f)
                            transports += 1
                            for gvalues in permutations(range(n)):
                                g = dict(enumerate(gvalues))
                                gi = {g[u]: u for u in U}
                                cmp = {v: g[fi[v]] for v in U}
                                lower_g = frozenset(g[u] for u in lower)
                                edges_g = frozenset(
                                    tuple(sorted((g[u], g[v])))
                                    for u, v in edges
                                )
                                value_g = {
                                    g[u]: frozenset(g[v] for v in value[u])
                                    for u in U
                                }
                                for v, w in product(U, repeat=2):
                                    assert (
                                        rank[fi[v]] < rank[fi[w]]
                                    ) == (
                                        rank[gi[cmp[v]]] < rank[gi[cmp[w]]]
                                    )
                                    assert (
                                        tuple(sorted((v, w))) in edges_f
                                        if v != w else False
                                    ) == (
                                        tuple(sorted((cmp[v], cmp[w])))
                                        in edges_g if v != w else False
                                    )
                                    assert (w in value_f[v]) == (
                                        cmp[w] in value_g[cmp[v]]
                                    )
                                for v in U:
                                    assert (v in lower_f) == (
                                        cmp[v] in lower_g
                                    )
                                comparisons += 1

    assert (records, orders, transports, comparisons) == (
        123, 273, 1601, 9537
    ), (records, orders, transports, comparisons)

    # An unordered two-vertex one-component structure can have a swap
    # automorphism that does NOT preserve a selected strict linear order.
    # This is why representative order is transported using a CHOSEN
    # isomorphism, not required invariant under all raw automorphisms.
    value = [{0, 1}, {0, 1}]
    lower, raw_swap = set(), {0: 1, 1: 0}
    assert value[0] == value[1] and not lower
    assert 0 < 1 and not (raw_swap[0] < raw_swap[1])

    print(
        f"PASS: {records} raw representative structures; {orders} chosen "
        f"orders; {transports} occurrences; {comparisons} coherent "
        "pairwise comparisons; unordered-automorphism negative control"
    )


if __name__ == "__main__":
    test()
