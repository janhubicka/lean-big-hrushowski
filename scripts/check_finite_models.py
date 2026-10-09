"""Independent exhaustive bit-set sanity check, not a proof certificate.

Enumerates every graph on at most five labelled vertices; checks the exact
predimension inequalities and both strong and d-closed finite relations.
"""
from itertools import combinations

counts = {
    "graphs": 0, "submodularity": 0, "strong_inter": 0,
    "strong_trans": 0, "dclosed_inter": 0, "dclosed_trans": 0,
    "dclosed_implies_strong": 0,
}
for n in range(6):
    edges = list(combinations(range(n), 2))
    sets = list(range(1 << n))
    sub = {s: [t for t in sets if t & s == t] for s in sets}
    for graph in range(1 << len(edges)):
        counts["graphs"] += 1
        delta = [
            2 * s.bit_count() -
            sum(1 for i, (a, b) in enumerate(edges)
                if graph >> i & 1 and s >> a & 1 and s >> b & 1)
            for s in sets
        ]
        for p in sets:
            for q in sets:
                counts["submodularity"] += 1
                assert delta[p | q] + delta[p & q] <= delta[p] + delta[q]
        strong = [[False for _ in sets] for _ in sets]
        dc = [[False for _ in sets] for _ in sets]
        for c in sets:
            for p in sub[c]:
                extensions = [x for x in sub[c] if x & p == p]
                strong[p][c] = all(delta[p] <= delta[x] for x in extensions)
                dc[p][c] = all(delta[p] < delta[x] for x in extensions if x != p)
                if dc[p][c]:
                    counts["dclosed_implies_strong"] += 1
                    assert strong[p][c], (n, graph, p, c)
            ss = [p for p in sub[c] if strong[p][c]]
            ds = [p for p in sub[c] if dc[p][c]]
            for p in ss:
                for q in ss:
                    counts["strong_inter"] += 1
                    assert strong[p & q][c], (n, graph, p, q, c)
                for q in sub[c]:
                    if p & q == p and strong[q][c] and strong[p][q]:
                        counts["strong_trans"] += 1
                        assert strong[p][c], (n, graph, p, q, c)
            for p in ds:
                for q in ds:
                    counts["dclosed_inter"] += 1
                    assert dc[p & q][c], (n, graph, p, q, c)
                for q in sub[p]:
                    if dc[q][p]:
                        counts["dclosed_trans"] += 1
                        assert dc[q][c], (n, graph, q, p, c)
print(counts)
