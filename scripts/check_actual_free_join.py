"""Exhaustive finite regression for the actual free-join construction.

For every pair of graphs on up to four labelled vertices and every pair
of finite vertex subsets on which the induced overlap graphs agree, form
the union of the edges internal to the respective factors. Verify that the
result is a no-crossing join, preserves the induced factor graphs, and
preserves 2-sparsity and strongness whenever the base is strong in both.

Independent Python bit-mask implementation; *not* a Lean proof certificate.
"""
from itertools import combinations

stats = dict(input_pairs=0, compatible=0, sparse_amalgams=0,
             strong_amalgams=0)

for n in range(5):
    edges = list(combinations(range(n), 2))
    edge_count = len(edges)
    masks = list(range(1 << n))
    inside = [
        sum(1 << k for k, (u, v) in enumerate(edges)
            if subset & (1 << u) and subset & (1 << v))
        for subset in masks
    ]
    delta = [
        [2 * subset.bit_count() - (graph & inside[subset]).bit_count()
         for subset in masks]
        for graph in range(1 << edge_count)
    ]

    def sparse(graph, vertices):
        return all(
            delta[graph][s] >= 0
            for s in masks if s & vertices == s
        )

    def strong(graph, a, b):
        return a & b == a and all(
            delta[graph][a] <= delta[graph][s]
            for s in masks if s & a == a and s & b == s
        )

    for left in range(1 << edge_count):
        for right in range(1 << edge_count):
            for a in masks:
                for b in masks:
                    stats["input_pairs"] += 1
                    p = a & b
                    if left & inside[p] != right & inside[p]:
                        continue
                    stats["compatible"] += 1
                    amalgam = (left & inside[a]) | (right & inside[b])
                    assert amalgam & inside[a] == left & inside[a]
                    assert amalgam & inside[b] == right & inside[b]
                    assert amalgam & inside[a | b] == (
                        (amalgam & inside[a]) | (amalgam & inside[b])
                    )
                    if (sparse(left, a) and sparse(right, b)
                            and strong(left, p, a)
                            and strong(right, p, b)):
                        stats["sparse_amalgams"] += 1
                        assert sparse(amalgam, a | b)
                        assert strong(amalgam, a, a | b)
                        assert strong(amalgam, b, a | b)
                        stats["strong_amalgams"] += 1

assert stats == {
    "input_pairs": 1052741,
    "compatible": 894763,
    "sparse_amalgams": 893483,
    "strong_amalgams": 893483,
}, stats
print(stats)


# Negative control: strongness of the common base is indispensable.
# Two K5's meeting in a K3 have seven vertices and seventeen edges.
# Each K5 is 2-sparse, but the free join has predimension -3.
p = {0, 1, 2}
a = p | {3, 4}
b = p | {5, 6}
e1 = {frozenset(x) for x in combinations(sorted(a), 2)}
e2 = {frozenset(x) for x in combinations(sorted(b), 2)}
joined_edges = e1 | e2

def delta_of_graph(vertices, edge_set):
    return 2 * len(vertices) - sum(e <= vertices for e in edge_set)

for vertices, edges_of_piece in [(a, e1), (b, e2)]:
    assert all(
        delta_of_graph(set(t), edges_of_piece) >= 0
        for k in range(len(vertices) + 1)
        for t in combinations(sorted(vertices), k)
    )
assert delta_of_graph(p, joined_edges) == 3
assert delta_of_graph(a, e1) == 0
assert delta_of_graph(b, e2) == 0
assert delta_of_graph(a | b, joined_edges) == -3
print("Negative control passed: two K5's glued over K3 are not 2-sparse.")
