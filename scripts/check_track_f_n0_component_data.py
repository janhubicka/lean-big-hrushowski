"""Independent finite audit: SCC lower parts, component linear extension ranks.

All oriented simple graphs of out-degree at most two on up to five
labelled vertices are included. This is a finite diagnostic only:
no equivalence with all permitted vertex orders or infinite BRD is claimed.
"""
from itertools import combinations, product, permutations
from collections import Counter
import json

def reachability(out):
    n = len(out)
    reach = [(1 << i) | out[i] for i in range(n)]
    for k in range(n):
        for i in range(n):
            if reach[i] >> k & 1:
                reach[i] |= reach[k]
    return reach

def successor_closed(out, mask):
    return all(not (out[x] & ~mask)
               for x in range(len(out)) if mask >> x & 1)

def run():
    stats = Counter()
    for n in range(6):
        pairs = list(combinations(range(n), 2))
        for choices in product(range(3), repeat=len(pairs)):
            out = [0] * n
            for (a, b), c in zip(pairs, choices):
                if c == 1:
                    out[a] |= 1 << b
                elif c == 2:
                    out[b] |= 1 << a
            if any(x.bit_count() > 2 for x in out):
                continue
            stats["orientations"] += 1
            reach = reachability(out)
            comps = [
                sum(1 << z for z in range(n)
                    if reach[x] >> z & 1 and reach[z] >> x & 1)
                for x in range(n)
            ]
            component_sets = []
            unseen = set(range(n))
            while unseen:
                x = min(unseen)
                block = {v for v in unseen if comps[x] >> v & 1}
                component_sets.append(tuple(sorted(block)))
                unseen -= block
            owner = {v: i for i, b in enumerate(component_sets) for v in b}
            lower = {
                i: {owner[w] for w in range(n)
                    if reach[b[0]] >> w & 1 and w not in b}
                for i, b in enumerate(component_sets)
            }
            for x in range(n):
                proper = reach[x] & ~comps[x]
                assert successor_closed(out, proper)
                assert comps[x] | proper == reach[x]
                assert not (comps[x] & proper)
                assert all(not (reach[y] & comps[x])
                           for y in range(n) if proper >> y & 1)
                stats["lower_closed_checks"] += 1
                for y in range(n):
                    if comps[x] >> y & 1:
                        assert comps[x] == comps[y]
                        assert proper == (reach[y] & ~comps[y])
                        stats["same_component_checks"] += 1
            for e in permutations(range(len(component_sets))):
                rank = {c: i for i, c in enumerate(e)}
                if any(not lower[c].issubset(set(e[:rank[c]]))
                       for c in rank):
                    continue
                stats["rankings"] += 1
                for cutoff in range(len(component_sets) + 1):
                    mask = sum(1 << x for x in range(n)
                               if rank[owner[x]] < cutoff)
                    assert successor_closed(out, mask)
                    stats["strong_prefixes"] += 1
    assert stats == Counter({
        "orientations": 30887,
        "rankings": 94694,
        "strong_prefixes": 512869,
        "lower_closed_checks": 153742,
        "same_component_checks": 348658,
    }), stats
    return {"status": "PASS", "scope": "finite only", "checks": dict(stats)}

if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
