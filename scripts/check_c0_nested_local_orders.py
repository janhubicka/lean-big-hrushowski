#!/usr/bin/env python3
"""Exhaustive finite controls for the nested one-generated C0 comparison.

For every finite canonical minimal-strong enumeration on up to four
vertices, check all nested closures C(b) within C(a). Their induced
graphs and full complete C/J values must agree under literal inclusion.

These small tests do not replace the five proposed Lean theorems,
nor do they choose a hereditary global catalogue or construct W.
"""
from itertools import combinations, product


def graphs(n):
    pairs = list(combinations(range(n), 2))
    for bits in range(1 << len(pairs)):
        yield frozenset(p for i, p in enumerate(pairs) if bits >> i & 1)


def subsets(s):
    a = sorted(s)
    for size in range(len(a) + 1):
        for x in combinations(a, size):
            yield frozenset(x)


def predim(s, edges):
    return 2 * len(s) - sum(u in s and v in s for u, v in edges)


def strong(a, b, edges):
    return a <= b and all(
        predim(a, edges) <= predim(z, edges)
        for z in subsets(b) if a <= z
    )


def minimal_step(a, b, edges):
    # Lean IsMinimalStrongStep excludes intermediate z strong IN b.
    return a < b and strong(a, b, edges) and all(
        not strong(z, b, edges)
        for z in subsets(b) if a < z < b
    )


def complete_values(kappa, edges):
    n, m = len(kappa), max(kappa) + 1
    blocks = [{v for v in range(n) if kappa[v] == i}
              for i in range(m)]
    deps = [
        {j for j in range(i) if any(
            kappa[u] == i and kappa[v] == j
            and tuple(sorted((u, v))) in edges
            for u in range(n) for v in range(n)
        )}
        for i in range(m)
    ]
    result = []
    for u in range(n):
        seen, todo = {kappa[u]}, [kappa[u]]
        while todo:
            for j in deps[todo.pop()]:
                if j not in seen:
                    seen.add(j)
                    todo.append(j)
        result.append(frozenset(v for j in seen for v in blocks[j]))
    return result


def adjacent(edges, u, v):
    return u != v and tuple(sorted((u, v))) in edges


def main():
    presentations = nested = values_checked = pairs_checked = 0
    for n in range(1, 5):
        for edges in graphs(n):
            for m in range(1, n + 1):
                for kappa in product(range(m), repeat=n):
                    if set(kappa) != set(range(m)):
                        continue
                    stages = [frozenset(u for u in range(n) if kappa[u] < i)
                              for i in range(m + 1)]
                    if not all(minimal_step(stages[i], stages[i + 1], edges)
                               for i in range(m)):
                        continue
                    presentations += 1
                    C = complete_values(kappa, edges)
                    for a in range(n):
                        for b in C[a]:
                            nested += 1
                            assert C[b] <= C[a]
                            big_edges = {
                                (x, y) for x in C[a] for y in C[a]
                                if adjacent(edges, x, y)
                            }
                            small_edges = {
                                (x, y) for x in C[b] for y in C[b]
                                if adjacent(edges, x, y)
                            }
                            assert small_edges == {
                                (x, y) for x, y in big_edges
                                if x in C[b] and y in C[b]
                            }
                            for u in C[b]:
                                values_checked += 1
                                assert C[u] <= C[b]
                                assert C[u] & C[b] == C[u] & C[a]
                                J = {v for v in C[u] if adjacent(edges, u, v)}
                                assert J & C[b] == J & C[a]
                                for v in C[b]:
                                    pairs_checked += 1
                                    assert ((u, v) in small_edges) == (
                                        (u, v) in big_edges
                                    )
    assert (presentations, nested, values_checked, pairs_checked) == (
        1401, 10125, 16157, 32793
    ), (presentations, nested, values_checked, pairs_checked)

    # Nonclosed restriction may delete a complete C and J member.
    C, edges = [{0, 1}, {1}], {(0, 1)}
    source, cut = {0, 1}, {0}
    J0 = {v for v in C[0] if adjacent(edges, 0, v)}
    assert C[0] <= source and not C[0] <= cut
    assert C[0] & cut != C[0] & source
    assert J0 & cut != J0 & source

    print("PASS: 1401 finite minimal-step presentations, "
          "10125 nested generated pairs, 16157 full C/J transports, "
          "32793 induced vertex-pair checks, and nonclosed counterexample")


if __name__ == "__main__":
    main()
