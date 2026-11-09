"""Adversarial finite check of component/global comparison reconstruction.
Independently generates SCCs, legal component rankings, and internal ranks.
Tests both directions for equality of actual labelled order relations.
"""
from itertools import combinations, permutations, product
from collections import Counter
import json


def orientations(n):
    pairs = tuple(combinations(range(n), 2))
    for bits in product(range(3), repeat=len(pairs)):
        out = [0] * n
        for (x, y), z in zip(pairs, bits):
            if z == 1:
                out[x] |= 1 << y
            if z == 2:
                out[y] |= 1 << x
        if all(x.bit_count() <= 2 for x in out):
            yield tuple(out)


def components(out):
    n = len(out)
    reach = [(1 << i) | out[i] for i in range(n)]
    for k in range(n):
        for i in range(n):
            if (reach[i] >> k) & 1:
                reach[i] |= reach[k]
    comps = sorted({tuple(j for j in range(n)
                          if (reach[i] >> j) & 1 and
                             (reach[j] >> i) & 1)
                    for i in range(n)})
    cid = {x: c for c, vs in enumerate(comps) for x in vs}
    return comps, cid, reach


def check(out, counts):
    n = len(out)
    comps, cid, reach = components(out)
    ranks = []
    for order in permutations(range(len(comps))):
        rank = {c: i for i, c in enumerate(order)}
        if all(rank[cid[y]] < rank[cid[x]]
               for x in range(n) for y in range(n)
               if cid[x] != cid[y] and ((reach[x] >> y) & 1)):
            ranks.append(rank)
    assert ranks
    local_orders = [tuple(range(n))]
    if n >= 2:
        local_orders.append(tuple(reversed(range(n))))
    pairs = []
    for r in ranks:
        for order in local_orders:
            localrank = {x: i for i, x in enumerate(order)}
            globalrel = {(x, y) for x in range(n) for y in range(n)
                         if (r[cid[x]], localrank[x]) <
                            (r[cid[y]], localrank[y])}
            between = {(x, y) for x in range(n) for y in range(n)
                       if cid[x] != cid[y] and r[cid[x]] < r[cid[y]]}
            within = {(x, y) for x in range(n) for y in range(n)
                      if cid[x] == cid[y] and
                      localrank[x] < localrank[y]}
            assert globalrel == between | within
            pairs.append((globalrel, between, within))
    for one, two in product(pairs, repeat=2):
        assert (one[0] == two[0]) == (
            one[1] == two[1] and one[2] == two[2]), (out, one, two)
        counts["relation_pairs"] += 1
    counts["orientations"] += 1
    counts["legal_rankings"] += len(ranks)
    counts["constructed_orders"] += len(pairs)


def main():
    counts = Counter()
    for n in range(5):
        for out in orientations(n):
            check(out, counts)
    print(json.dumps(dict(counts), sort_keys=True))


if __name__ == "__main__":
    main()
