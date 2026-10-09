"""Independent finite test of induced-embedding predimension and strongness.

For each labelled simple graph with at most four vertices, each injection
into a larger carrier, and four choices of edges outside the image,
check finite-subset predimension invariance and the equivalence of
relative strongness. This diagnostic does not replace the Lean proof.
"""
from itertools import combinations, permutations

stats = {
    "source_graphs": 0, "map_graph_pairs": 0,
    "subset_predims": 0, "relative_strong_checks": 0,
}
for n in range(5):
    m = n + 1
    source = list(range(n))
    target = list(range(m))
    pairs = list(combinations(source, 2))
    subsets = [
        set(t)
        for k in range(n + 1)
        for t in combinations(source, k)
    ]

    def delta(vertices, edges):
        return 2 * len(vertices) - sum(edge <= vertices for edge in edges)

    for graph in range(1 << len(pairs)):
        stats["source_graphs"] += 1
        original = {
            frozenset(pair)
            for i, pair in enumerate(pairs)
            if graph & (1 << i)
        }
        for image_tuple in permutations(target, n):
            mapping = dict(zip(source, image_tuple))
            image_set = set(image_tuple)
            image_edges = {
                frozenset(mapping[v] for v in edge)
                for edge in original
            }
            external = [
                frozenset(edge)
                for edge in combinations(target, 2)
                if not set(edge) <= image_set
            ]
            choices = [
                set(), set(external),
                set(external[::2]), set(external[1::2])
            ]
            for extra in choices:
                result_edges = image_edges | extra
                stats["map_graph_pairs"] += 1
                for subset in subsets:
                    image = {mapping[v] for v in subset}
                    assert delta(subset, original) == delta(
                        image, result_edges
                    )
                    stats["subset_predims"] += 1
                for a in subsets:
                    for b in subsets:
                        if not a <= b:
                            continue
                        aa = {mapping[v] for v in a}
                        bb = {mapping[v] for v in b}
                        source_strong = all(
                            delta(a, original) <= delta(t, original)
                            for t in subsets if a <= t <= b
                        )
                        target_strong = all(
                            delta(aa, result_edges) <= delta(
                                {mapping[v] for v in t}, result_edges)
                            for t in subsets if a <= t <= b
                        )
                        assert source_strong == target_strong
                        stats["relative_strong_checks"] += 1

# Negative controls showing why both hypotheses are necessary.
assert delta({0, 1}, set()) != delta(
    {0, 1}, {frozenset((0, 1))})
assert delta({0, 1}, set()) != delta({0}, set())

assert stats == {
    "source_graphs": 76,
    "map_graph_pairs": 31548,
    "subset_predims": 497876,
    "relative_strong_checks": 2509516,
}, stats
print(stats)
