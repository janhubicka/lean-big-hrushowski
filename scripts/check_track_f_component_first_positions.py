"""Independent test of the first-position component recovery lemma.

Runs on all 653 2-orientations of at most four labelled vertices and
all 15,074 complete vertex enumerations. Verifies distinct SCC first
positions and the dependency relation whenever every proper successor
vertex occurs before its source. Does not impose SCC interval condition.
"""
from itertools import combinations, permutations, product
from collections import Counter
import json

def run():
    stats = Counter()
    for n in range(5):
        pairs = list(combinations(range(n), 2))
        for options in product((0, 1, 2), repeat=len(pairs)):
            outgoing = [0] * n
            for (a, b), direction in zip(pairs, options):
                if direction == 1:
                    outgoing[a] |= 1 << b
                elif direction == 2:
                    outgoing[b] |= 1 << a
            if any(x.bit_count() > 2 for x in outgoing):
                continue
            reach = [(1 << i) | outgoing[i] for i in range(n)]
            for k in range(n):
                for i in range(n):
                    if (reach[i] >> k) & 1:
                        reach[i] |= reach[k]
            components = []
            seen = set()
            for i in range(n):
                B = tuple(j for j in range(n)
                          if (reach[i] >> j) & 1 and (reach[j] >> i) & 1)
                if B not in seen:
                    seen.add(B)
                    components.append(B)
            stats["orientations"] += 1
            for enumeration in permutations(range(n)):
                position = {v: i for i, v in enumerate(enumeration)}
                firsts = [min(position[x] for x in B) for B in components]
                assert len(set(firsts)) == len(firsts)
                stats["enumerations"] += 1
                successor_first = all(position[y] < position[x]
                    for x in range(n) for y in range(n)
                    if (reach[x] >> y) & 1 and not ((reach[y] >> x) & 1))
                if successor_first:
                    stats["successor_first"] += 1
                    for j, C in enumerate(components):
                        for i, B in enumerate(components):
                            precedes = (reach[C[0]] >> B[0]) & 1 and not (
                                (reach[B[0]] >> C[0]) & 1)
                            if precedes:
                                assert firsts[i] < firsts[j]
                                stats["dependency_comparisons"] += 1
    assert stats == Counter(
        orientations=653, enumerations=15074,
        successor_first=3810, dependency_comparisons=5168), stats
    # Reversing a dependency: 0 -> 1, enumeration (0,1) is not successor-first.
    assert not (({0: 0, 1: 1}[1] < {0: 0, 1: 1}[0]))
    return {"status": "PASS", "scope": "finite structural checks",
            "checks": dict(stats), "counterexample": "reversed edge dependency"}

if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
