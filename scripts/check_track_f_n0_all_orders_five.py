"""Independent exhaustive canonical-order/product comparison through five vertices.

Enumerates every two-orientation on at most five labelled vertices,
computes its SCC dependency orders and local pointwise stabilizers,
and independently enumerates every complete vertex order satisfying:
(1) component intervals, (2) proper successors first, and
(3) canonical minimal complete adjacency codes on each C_B
    with the inherited ordering of its lower part P_B.

This is a finite regression, not a proof of the infinite Ramsey theorem.
"""
from itertools import combinations, permutations, product
from functools import lru_cache
from collections import Counter
import json

def run():
    stat = Counter()
    counts_by_size = Counter()
    for n in range(6):
        pairs = tuple(combinations(range(n), 2))
        orders = tuple(permutations(range(n)))
        for choices in product(range(3), repeat=len(pairs)):
            out = [0] * n
            for (a, b), c in zip(pairs, choices):
                if c == 1:
                    out[a] |= 1 << b
                elif c == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            stat["orientations"] += 1
            reach = [(1 << x) | out[x] for x in range(n)]
            for k in range(n):
                for x in range(n):
                    if reach[x] >> k & 1:
                        reach[x] |= reach[k]
            unseen = set(range(n))
            blocks = []
            while unseen:
                x = min(unseen)
                block = tuple(w for w in sorted(unseen)
                              if reach[x] >> w & 1 and reach[w] >> x & 1)
                blocks.append(block)
                unseen.difference_update(block)
            owner = {v: i for i, B in enumerate(blocks) for v in B}
            pbase = []
            predecessors = []
            stabilizers = []
            for B in blocks:
                p = tuple(x for x in range(n)
                          if reach[B[0]] >> x & 1 and x not in B)
                pbase.append(p)
                predecessors.append({owner[x] for x in p})
                C = p + B
                g = 0
                for pb in permutations(B):
                    mapping = dict(zip(B, pb)) | {x: x for x in p}
                    if all(bool(out[u] >> v & 1) ==
                           bool(out[mapping[u]] >> mapping[v] & 1)
                           for u in C for v in C):
                        g += 1
                stabilizers.append(g)
            ell = 0
            for pi in permutations(range(len(blocks))):
                done = set()
                for i in pi:
                    if not predecessors[i].issubset(done):
                        break
                    done.add(i)
                else:
                    ell += 1
            predicted = ell
            for g in stabilizers:
                predicted *= g
            assert predicted <= len(orders)

            def code(t):
                k = 0
                for u in t:
                    row = out[u]
                    for v in t:
                        k = (k << 1) | ((row >> v) & 1)
                return k

            @lru_cache(None)
            def canonical(i, lower_order):
                return min(code(lower_order + pb)
                           for pb in permutations(blocks[i]))

            actual = 0
            for order in orders:
                rank = {v: i for i, v in enumerate(order)}
                valid = True
                for i, B in enumerate(blocks):
                    inds = [rank[v] for v in B]
                    if max(inds) - min(inds) + 1 != len(B):
                        valid = False
                        break
                    lower_order = tuple(v for v in order if v in pbase[i])
                    if lower_order and rank[lower_order[-1]] >= min(inds):
                        valid = False
                        break
                    internal_order = tuple(v for v in order if v in B)
                    if code(lower_order + internal_order) != canonical(i, lower_order):
                        valid = False
                        break
                if valid:
                    actual += 1
                stat["candidate_orders"] += 1
            assert actual == predicted, (n, out, ell, stabilizers, predicted, actual)
            stat["permitted_orders"] += actual
            counts_by_size[(n, actual)] += 1
    assert stat == Counter({
        "orientations": 30887,
        "candidate_orders": 3643154,
        "permitted_orders": 106044,
    }), stat
    return {"status": "PASS", "scope": "exhaustive finite orientations through five vertices",
            "checks": dict(stat),
            "degree_distributions": {
                str(n): {str(k): v for (m, k), v in sorted(counts_by_size.items())
                         if m == n}
                for n in range(6)
            }}

if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
