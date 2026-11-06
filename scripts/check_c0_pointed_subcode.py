#!/usr/bin/env python3
"""Exhaustive pointed C0 subcode controls on at most three vertices.

For each finite extensive/transitive set-valued closure, each simple
edge-covered graph, and several increasing label assignments, compare
complete pointed codes with their induced closed restrictions. Also test
the literal equality of successive restrictions. This does not verify
the infinite coordinate host W or replace Lean kernel verification.
"""
from itertools import combinations, product


def closures(n):
    for masks in product(range(1 << n), repeat=n):
        C = [frozenset(j for j in range(n) if masks[i] & (1 << j))
             for i in range(n)]
        if all(i in C[i] for i in range(n)) and all(
            C[j] <= C[i] for i in range(n) for j in C[i]
        ):
            yield C


def graphs(n):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        yield frozenset(e for k, e in enumerate(pairs) if mask & (1 << k))


def adjacent(G, i, j):
    return i != j and tuple(sorted((i, j))) in G


def code(domain, root, labels, C, G):
    domain = frozenset(domain)
    assert root in domain
    return (
        frozenset(labels[i] for i in domain),
        labels[root],
        frozenset((labels[i], labels[j]) for i in domain for j in domain
                  if adjacent(G, i, j)),
        frozenset((labels[i], labels[j]) for i in domain for j in domain
                  if j in C[i]),
    )


def restrict(q, support, point):
    old_support, _, adj, unary = q
    support = frozenset(support)
    assert support <= old_support and point in support
    return (
        support, point,
        frozenset((a, b) for a, b in adj if a in support and b in support),
        frozenset((a, b) for a, b in unary if a in support and b in support),
    )


def is_closed(q, support):
    return all(b in support for a, b in q[3] if a in support)


def main():
    counts = {}
    diagrams = pointed = nested = 0
    for n in range(4):
        count = 0
        for C in closures(n):
            for G in graphs(n):
                if not all(b in C[a] or a in C[b] for a, b in G):
                    continue
                count += 1
                for coords in combinations(range(n + 3), n):
                    labels = dict(enumerate(coords))
                    for a in range(n):
                        parent = code(C[a], a, labels, C, G)
                        diagrams += 1
                        assert is_closed(parent, parent[0])
                        for v in C[a]:
                            sub = {labels[k] for k in C[v]}
                            assert is_closed(parent, sub)
                            q = restrict(parent, sub, labels[v])
                            assert q == code(C[v], v, labels, C, G)
                            pointed += 1
                            for w in C[v]:
                                support = {labels[k] for k in C[w]}
                                assert restrict(q, support, labels[w]) == (
                                    restrict(parent, support, labels[w]))
                                assert restrict(q, support, labels[w]) == (
                                    code(C[w], w, labels, C, G))
                                nested += 1
        counts[n] = count
    assert counts == {0: 1, 1: 1, 2: 7, 3: 147}, counts

    # A genuine transitive unary closure whose nonclosed singleton
    # loses a complete unary value after restriction.
    parent = code({0, 1}, 0, {0: 1, 1: 3},
                  [{0, 1}, {1}], frozenset())
    assert is_closed(parent, {3})
    assert not is_closed(parent, {1})
    assert (1, 3) in parent[3]
    assert (1, 3) not in restrict(parent, {1}, 1)[3]

    assert (diagrams, pointed, nested) == (8964, 18164, 34364)
    print(f"PASS: {sum(counts.values())} closure/graph systems, "
          f"{diagrams} pointed diagrams, {pointed} subcodes, "
          f"{nested} nested pointed restrictions and negative controls")


if __name__ == "__main__":
    main()
