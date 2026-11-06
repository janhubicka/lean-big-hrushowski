#!/usr/bin/env python3
"""Exhaustive small-model checks for increasing coordinate relabellings.

All compatible extensive/transitive C and covered simple graphs on 1-3
vertices, all increasing original labels into n+2, and three increasing
reassignments. Includes arbitrary (possibly nonclosed) pointed restrictions.
This is regression evidence, not a proof of the countable host W.
"""
from itertools import combinations, product


def closures(n):
    for raw in product(range(1 << n), repeat=n):
        C = [frozenset(j for j in range(n) if raw[i] & (1 << j))
             for i in range(n)]
        if all(i in C[i] for i in range(n)) and all(
                C[j] <= C[i] for i in range(n) for j in C[i]):
            yield C


def graphs(n):
    pairs = list(combinations(range(n), 2))
    for bits in range(1 << len(pairs)):
        yield frozenset(e for k, e in enumerate(pairs) if bits & (1 << k))


def code(n, C, G, labels, root):
    S = frozenset(labels)
    return (
        S, labels[root],
        frozenset((labels[i], labels[j]) for i in range(n)
                  for j in range(n) if i != j
                  and tuple(sorted((i, j))) in G),
        frozenset((labels[i], labels[j]) for i in range(n)
                  for j in C[i]),
    )


def restrict(q, S, p):
    S = frozenset(S)
    assert S <= q[0] and p in S
    return (
        S, p,
        frozenset((u, v) for u, v in q[2] if u in S and v in S),
        frozenset((u, v) for u, v in q[3] if u in S and v in S),
    )


def relabel(q, h):
    return (
        frozenset(h(u) for u in q[0]), h(q[1]),
        frozenset((h(u), h(v)) for u, v in q[2]),
        frozenset((h(u), h(v)) for u, v in q[3]),
    )


def generated(q):
    return all(
        (u in q[0]) == ((q[1], u) in q[3])
        for u in q[0] | {b for _, b in q[3]}
    )


def main():
    systems = parents = restrictions = generators = 0
    maps = (lambda x: x, lambda x: 2*x+1, lambda x: x+7)
    for n in range(1, 4):
        for C in closures(n):
            for G in graphs(n):
                if not all(v in C[u] or u in C[v] for u, v in G):
                    continue
                systems += 1
                for labels in combinations(range(n + 2), n):
                    for root in range(n):
                        q = code(n, C, G, labels, root)
                        parents += 1
                        for h in maps:
                            qh = relabel(q, h)
                            for mask in range(1, 1 << n):
                                selected = {
                                    labels[i] for i in range(n)
                                    if mask >> i & 1
                                }
                                for i in range(n):
                                    if labels[i] not in selected:
                                        continue
                                    lhs = relabel(
                                        restrict(q, selected, labels[i]), h
                                    )
                                    rhs = restrict(
                                        qh, {h(v) for v in selected},
                                        h(labels[i])
                                    )
                                    assert lhs == rhs
                                    restrictions += 1
                            S = {labels[i] for i in C[root]}
                            g = restrict(q, S, labels[root])
                            assert generated(g) and generated(relabel(g, h))
                            generators += 1
    assert (systems, parents, restrictions, generators) == (
        155, 4497, 159777, 13491
    ), (systems, parents, restrictions, generators)

    # A non-injective map would collapse distinct support vertices.
    q = (frozenset({0, 1}), 0, frozenset(),
         frozenset({(0, 0), (1, 1)}))
    assert len(relabel(q, lambda _: 0)[0]) < len(q[0])
    print(
        f"PASS: {systems} compatible systems, {parents} parent codes, "
        f"{restrictions} relabel/restrict equalities, {generators} "
        "root-generated relabels and non-injective negative control"
    )


if __name__ == "__main__":
    main()
