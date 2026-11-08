"""Independently verify that the literal lower part P_B is an
initial segment in C_B for every legal SCC ranking.

Exhaust all admissible two-orientations on up to four vertices,
their legal SCC linear extensions and the two extremal internal
rankings. Include a negative example where a vertex outside C_B
may precede P_B, so the finite restriction cannot be dropped.
"""
from itertools import combinations, permutations, product
from collections import Counter
import json

def orientations(n):
    pairs = list(combinations(range(n), 2))
    for bits in product(range(3), repeat=len(pairs)):
        out = [0] * n
        for (i, j), a in zip(pairs, bits):
            if a == 1:
                out[i] |= 1 << j
            elif a == 2:
                out[j] |= 1 << i
        if all(x.bit_count() <= 2 for x in out):
            yield tuple(out)

def test(out, counter):
    n = len(out)
    reach = [(1 << i) | out[i] for i in range(n)]
    for k in range(n):
        for i in range(n):
            if reach[i] >> k & 1:
                reach[i] |= reach[k]
    components = sorted({tuple(j for j in range(n)
                     if (reach[i] >> j & 1) and (reach[j] >> i & 1))
                     for i in range(n)})
    cid = {x: c for c, B in enumerate(components) for x in B}
    ranked = [p for p in permutations(range(len(components)))
              if all(p.index(cid[y]) < p.index(cid[x])
                 for x in range(n) for y in range(n)
                 if cid[x] != cid[y] and reach[x] >> y & 1)]
    assert ranked
    for p in ranked:
        cr = {c: p.index(c) for c in range(len(components))}
        for local_order in (tuple(range(n)), tuple(reversed(range(n)))):
            local = {v:i for i,v in enumerate(local_order)}
            key = lambda v:(cr[cid[v]],local[v])
            for x in range(n):
                closure = {y for y in range(n) if reach[x] >> y & 1}
                B = set(components[cid[x]])
                P = closure-B
                assert P == {y for y in range(n) if
                             reach[x] >> y & 1 and
                             not (reach[y] >> x & 1)}
                for y in P:
                    for z in B:
                        assert key(y) < key(z)
                        counter["lower_top_pairs"] += 1
                    for z in closure:
                        if key(z) < key(y):
                            assert z in P
                            counter["initial_pairs"] += 1
            counter["component_orders"] += 1
    counter["orientations"] += 1
    counter["rankings"] += len(ranked)

def main():
    counter=Counter()
    for n in range(5):
        for out in orientations(n):
            test(out,counter)
    # A disconnected predecessor can occur before a sink without
    # belonging to the sink's closure; closure restriction matters.
    out=(0,0,0)
    closure0={0}
    global_order=(1,0,2)
    assert 1 not in closure0 and global_order.index(1)<global_order.index(0)
    print(json.dumps(dict(counter),sort_keys=True))

if __name__=="__main__":
    main()
