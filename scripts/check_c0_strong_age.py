"""Independent regression for hereditary and joint-embedding properties of C0.

Enumerate all 76 labelled simple graphs on at most four vertices.
Check subset-wise 2-sparsity and strongness of the empty set; for
every pair construct their tagged disjoint union and verify both
canonical embeddings are strong. This is not a Lean proof.
"""
from itertools import combinations

def all_subsets(s):
    a = list(s)
    return (
        set(t) for k in range(len(a) + 1)
        for t in combinations(a, k)
    )

def delta(vertices, edges):
    return 2 * len(vertices) - sum(edge <= vertices for edge in edges)

def sparse(vertices, edges):
    return all(delta(t, edges) >= 0 for t in all_subsets(vertices))

def strong(base, carrier, edges):
    return base <= carrier and all(
        delta(base, edges) <= delta(t, edges)
        for t in all_subsets(carrier) if base <= t
    )

graphs = []
for n in range(5):
    all_edges = list(combinations(range(n), 2))
    for mask in range(1 << len(all_edges)):
        vertices = set(range(n))
        edges = {
            frozenset(pair) for k, pair in enumerate(all_edges)
            if (mask >> k) & 1
        }
        if sparse(vertices, edges):
            assert delta(set(), edges) == 0
            assert strong(set(), vertices, edges)
            assert all(sparse(s, edges) for s in all_subsets(vertices))
            graphs.append((n, edges))

assert len(graphs) == 76
pairs_checked = 0
for n, edges_a in graphs:
    va = {("a", k) for k in range(n)}
    ea = {
        frozenset(("a", x) for x in e) for e in edges_a
    }
    for m, edges_b in graphs:
        vb = {("b", k) for k in range(m)}
        eb = {
            frozenset(("b", x) for x in e) for e in edges_b
        }
        v = va | vb
        e = ea | eb
        assert va.isdisjoint(vb)
        assert sparse(v, e)
        assert strong(va, v, e)
        assert strong(vb, v, e)
        pairs_checked += 1

assert pairs_checked == 5776
k6_edges = {
    frozenset(edge) for edge in combinations(range(6), 2)
}
assert delta(set(range(6)), k6_edges) == -3
assert not sparse(set(range(6)), k6_edges)

print(f"Checked {len(graphs)} finite graphs and {pairs_checked} strong joint embeddings.")
print("Negative control: K6 is not 2-sparse.")
