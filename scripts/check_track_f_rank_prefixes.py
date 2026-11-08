"""Adversarial finite check of strong prefixes from component rankings.

Independent of the manuscript's original orientation-degree checker.
The regression tests closure, not infinite recurrence or BRD.
"""
from itertools import combinations, permutations, product
import json


def components_and_dependencies(out):
    n = len(out)
    reach = [(1 << x) | out[x] for x in range(n)]
    for k in range(n):
        for x in range(n):
            if (reach[x] >> k) & 1:
                reach[x] |= reach[k]
    unseen = set(range(n))
    components = []
    while unseen:
        x = min(unseen)
        comp = tuple(y for y in unseen if (reach[x] >> y) & 1
                     and (reach[y] >> x) & 1)
        components.append(comp)
        unseen.difference_update(comp)
    owner = {x: i for i, block in enumerate(components) for x in block}
    lower = {(owner[y], owner[x]) for x in range(n) for y in range(n)
             if (reach[x] >> y) & 1 and not ((reach[y] >> x) & 1)}
    return components, owner, lower


def run():
    orientations = rankings = prefixes = 0
    for n in range(5):
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
            orientations += 1
            comps, owner, dependencies = components_and_dependencies(out)
            for order in permutations(range(len(comps))):
                rank = {c: i for i, c in enumerate(order)}
                if not all(rank[b] < rank[c] for b, c in dependencies):
                    continue
                rankings += 1
                for cutoff in range(len(comps) + 1):
                    chosen = {x for x in range(n) if rank[owner[x]] < cutoff}
                    assert all(not (out[x] & ~sum(1 << y for y in chosen))
                               for x in chosen)
                    prefixes += 1
    assert (orientations, rankings, prefixes) == (653, 1586, 7423)
    # Negative test: x -> y, with rank(x)=0 and rank(y)=1
    # violates the dependency condition and the rank-1 prefix is not closed.
    outgoing = (2, 0)
    prefix = {0}
    assert outgoing[0] & ~sum(1 << y for y in prefix)
    return {"status": "PASS", "orientations": orientations,
            "legal_rankings": rankings,
            "successor_closed_prefixes": prefixes,
            "negative_case": "reversed dependency on a directed edge",
            "scope": "finite only"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
