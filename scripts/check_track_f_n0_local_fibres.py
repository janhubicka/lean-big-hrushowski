"""Adversarial test: local canonical codes have pointwise stabilizer size.

For every orientation on up to five vertices, every SCC and every order
on its strict lower successor part, enumerate all internal orders. Count
those attaining the lexicographically minimal complete directed
adjacency matrix. Compare with the group of orientation automorphisms
of the whole local successor closure fixing the lower part pointwise.

Finite diagnostic only; it does not prove the infinite Ramsey theorem.
"""
from itertools import combinations, permutations, product
from collections import Counter
import json

def run():
    stats = Counter()
    for n in range(6):
        pairs = tuple(combinations(range(n), 2))
        for choices in product(range(3), repeat=len(pairs)):
            out = [0] * n
            for (a, b), v in zip(pairs, choices):
                if v == 1:
                    out[a] |= 1 << b
                elif v == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            stats["orientations"] += 1
            reach = [(1 << i) | out[i] for i in range(n)]
            for k in range(n):
                for x in range(n):
                    if reach[x] >> k & 1:
                        reach[x] |= reach[k]
            seen = set()
            for x in range(n):
                B = tuple(y for y in range(n)
                          if reach[x] >> y & 1 and reach[y] >> x & 1)
                if B in seen:
                    continue
                seen.add(B)
                C = tuple(y for y in range(n) if reach[x] >> y & 1)
                P = tuple(y for y in C if y not in B)
                def adj(a, b):
                    return bool(out[a] >> b & 1)
                stabilizer = 0
                for q in permutations(B):
                    f = dict(zip(B, q)) | {p: p for p in P}
                    if all(adj(u, v) == adj(f[u], f[v])
                           for u in C for v in C):
                        stabilizer += 1
                assert stabilizer >= 1
                stats["component_groups"] += 1
                stats["stabilizer_total"] += stabilizer
                for porder in permutations(P):
                    codes = []
                    for b_order in permutations(B):
                        order = porder + b_order
                        codes.append(tuple(int(adj(u, v))
                                           for u in order for v in order))
                    least = min(codes)
                    count = sum(code == least for code in codes)
                    assert count == stabilizer, (out, B, P, porder, count, stabilizer)
                    stats["ordered_lower_parts"] += 1
                    stats["local_enumerations_checked"] += len(codes)
    assert stats == Counter({
        "orientations": 30887,
        "component_groups": 106264,
        "stabilizer_total": 114208,
        "ordered_lower_parts": 478199,
        "local_enumerations_checked": 1170649,
    }), stats
    return {"status": "PASS", "scope": "finite canonical local orders only",
            "checks": dict(stats)}

if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
