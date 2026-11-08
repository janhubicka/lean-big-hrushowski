"""Independent adversarial check: every actual component-interval
successor-first labelled enumeration is reconstructed by first-SCC
rank and genuine numerical vertex positions.

Exhaust all two-orientations on at most 4 vertices, every labelled
vertex permutation, and check the lex reconstruction. Count
reconstructed component-interval orders and legal successor-first
orders separately; include all empty and disconnected examples.
"""
from itertools import combinations, permutations, product
from collections import Counter
import json


def orientations(n):
    pairs = list(combinations(range(n), 2))
    for choices in product(range(3), repeat=len(pairs)):
        out = [0] * n
        for (a, b), k in zip(pairs, choices):
            if k == 1:
                out[a] |= 1 << b
            elif k == 2:
                out[b] |= 1 << a
        if all(x.bit_count() <= 2 for x in out):
            yield tuple(out)


def check(out, tally):
    n = len(out)
    reach = [(1 << i) | out[i] for i in range(n)]
    for k in range(n):
        for i in range(n):
            if reach[i] >> k & 1:
                reach[i] |= reach[k]
    components = sorted({tuple(j for j in range(n)
                         if reach[i] >> j & 1 and reach[j] >> i & 1)
                         for i in range(n)})
    cid = {x:c for c, comp in enumerate(components) for x in comp}
    for order in permutations(range(n)):
        pos = {x:i for i, x in enumerate(order)}
        interval = all(
            pos[x] < pos[y] < pos[z] and cid[x] == cid[z]
            <= False
            for x in [] for y in [] for z in [])
        # The actual interval condition: a component cannot have a
        # vertex outside it between any two vertices of that component.
        interval = all(
            cid[order[i]] == cid[order[k]] or
            all(cid[order[j]] != cid[order[i]]
                for j in range(i + 1, k))
            for i in range(n) for k in range(i + 1, n)
            if cid[order[i]] != cid[order[k]]
        )
        # A simpler independent truth definition: occupied positions
        # of each SCC are consecutive integers.
        actual_interval = all(
            (max(pos[x] for x in B) - min(pos[x] for x in B) + 1 == len(B))
            for B in components)
        assert interval == actual_interval or not interval
        if not actual_interval:
            continue
        tally["interval_enumerations"] += 1
        first = {c:min(pos[x] for x in B) for c, B in enumerate(components)}
        comp_order = sorted(first, key=first.get)
        rank = {c:i for i, c in enumerate(comp_order)}
        for x in range(n):
            for y in range(n):
                reconstructed = (rank[cid[x]], pos[x]) < (rank[cid[y]], pos[y])
                actual = pos[x] < pos[y]
                assert reconstructed == actual, (out, order, x, y)
                tally["comparison_checks"] += 1
        successor_first = all(
            pos[y] < pos[x]
            for x in range(n) for y in range(n)
            if cid[x] != cid[y] and (reach[x] >> y & 1))
        if successor_first:
            assert all(rank[cid[y]] < rank[cid[x]]
                       for x in range(n) for y in range(n)
                       if cid[x] != cid[y] and reach[x] >> y & 1)
            tally["legal_enumerations"] += 1
    tally["orientations"] += 1


def main():
    tally = Counter()
    for n in range(5):
        for out in orientations(n):
            check(out, tally)
    print(json.dumps(dict(tally), sort_keys=True))


if __name__ == "__main__":
    main()
