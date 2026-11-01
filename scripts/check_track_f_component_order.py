"""Independent finite SCC dependency and linear-extension regression.

Do not import the manuscript's degree checker or Lean-side functions.
Finite diagnostics are not a proof of an infinite Ramsey theorem.
"""
from itertools import combinations, permutations, product
from functools import lru_cache
from collections import Counter
import json

def check_orientation(out):
    n = len(out)
    reach = [(1 << x) | out[x] for x in range(n)]
    for k in range(n):
        for x in range(n):
            if reach[x] & (1 << k):
                reach[x] |= reach[k]
    unseen = set(range(n))
    components = []
    while unseen:
        x = min(unseen)
        comp = tuple(y for y in range(n) if y in unseen
                     and reach[x] >> y & 1 and reach[y] >> x & 1)
        unseen.difference_update(comp)
        components.append(comp)
    owner = {x: i for i, comp in enumerate(components) for x in comp}
    precedes = {(i, j) for i, comp in enumerate(components)
                for j, other in enumerate(components)
                if i != j and reach[other[0]] >> comp[0] & 1
                and not reach[comp[0]] >> other[0] & 1}
    assert all((i, i) not in precedes for i in range(len(components)))
    assert all((i, k) in precedes for i, j in precedes
               for j2, k in precedes if j == j2)
    assert all((j, i) not in precedes for i, j in precedes)
    assert all(bool(reach[x] >> y & 1 and not reach[y] >> x & 1)
               == ((owner[y], owner[x]) in precedes)
               for x in range(n) for y in range(n))
    count_permutations = 0
    for order in permutations(range(len(components))):
        rank = {c: i for i, c in enumerate(order)}
        count_permutations += all(rank[i] < rank[j] for i, j in precedes)
    @lru_cache(None)
    def count_downward_closed(mask):
        if mask == (1 << len(components)) - 1:
            return 1
        return sum(count_downward_closed(mask | (1 << i))
                   for i in range(len(components))
                   if not (mask >> i & 1)
                   and all(mask >> j & 1 for j in range(len(components))
                           if (j, i) in precedes))
    assert count_permutations == count_downward_closed(0)
    return len(components), count_permutations, len(precedes)

def run():
    stats = Counter()
    distribution = Counter()
    for n in range(6):
        pairs = tuple(combinations(range(n), 2))
        for directions in product(range(3), repeat=len(pairs)):
            out = [0] * n
            for (a, b), direction in zip(pairs, directions):
                if direction == 1:
                    out[a] |= 1 << b
                elif direction == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            ncomp, ell, dependencies = check_orientation(out)
            stats["orientations"] += 1
            stats["components"] += ncomp
            stats["strict_component_dependencies"] += dependencies
            distribution[(n, ell)] += 1
    assert stats["orientations"] == 30887
    return {"status": "PASS", "scope": "finite only",
            "checks": dict(stats),
            "linear_extension_distribution": {
                str(n): {str(ell): cnt for (m, ell), cnt in sorted(distribution.items())
                         if m == n} for n in range(6)
            }}
if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
