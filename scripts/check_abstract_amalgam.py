"""Independent finite-model check of strong free amalgamation over injections.

Enumerates every labelled graph on at most three vertices, every base size
and every pair of injective base maps. In each applicable case it constructs
the tagged amalgam of the *original* graph vertices and checks induced
embeddings, exact overlap, 2-sparsity and strongness of both images.
This does not replace the Lean kernel proof.
"""
from itertools import combinations, permutations

def edges(n, mask):
    return {frozenset(e) for k, e in enumerate(combinations(range(n), 2))
            if (mask >> k) & 1}

def delta(s, graph):
    return 2 * len(s) - sum(e <= s for e in graph)

def subsets(s):
    a = list(s)
    return (set(v) for k in range(len(a) + 1) for v in combinations(a, k))

def sparse(s, graph):
    return all(delta(t, graph) >= 0 for t in subsets(s))

def strong(a, b, graph):
    return a <= b and all(
        delta(a, graph) <= delta(t, graph)
        for t in subsets(b) if a <= t
    )

counts = dict(total_spans=0, compatible=0,
              strong_input_spans=0, verified_amalgams=0)
for na in range(4):
    for nb in range(4):
        for np in range(min(na, nb) + 1):
            for ia in permutations(range(na), np):
                for ib in permutations(range(nb), np):
                    sa, sb = set(range(na)), set(range(nb))
                    pa, pb = set(ia), set(ib)
                    for ma in range(1 << (na * (na - 1) // 2)):
                        ea = edges(na, ma)
                        ea_base = {frozenset(ia.index(x) for x in e)
                                   for e in ea if e <= pa}
                        for mb in range(1 << (nb * (nb - 1) // 2)):
                            counts["total_spans"] += 1
                            eb = edges(nb, mb)
                            eb_base = {frozenset(ib.index(x) for x in e)
                                       for e in eb if e <= pb}
                            if ea_base != eb_base:
                                continue
                            counts["compatible"] += 1
                            if not (sparse(sa, ea) and sparse(sb, eb)
                                    and strong(pa, sa, ea)
                                    and strong(pb, sb, eb)):
                                continue
                            counts["strong_input_spans"] += 1
                            def left(u):
                                return ("p", ia.index(u)) if u in pa else ("l", u)
                            def right(u):
                                return ("p", ib.index(u)) if u in pb else ("r", u)
                            el = {frozenset(left(u) for u in e) for e in ea}
                            er = {frozenset(right(u) for u in e) for e in eb}
                            ejoin = el | er
                            a = {left(u) for u in sa}
                            b = {right(u) for u in sb}
                            union = a | b
                            assert a & b == {("p", k) for k in range(np)}
                            assert {e for e in ejoin if e <= a} == el
                            assert {e for e in ejoin if e <= b} == er
                            assert not any(frozenset((("l", u), ("r", v))) in ejoin
                                           for u in sa - pa for v in sb - pb)
                            assert sparse(union, ejoin)
                            assert strong(a, union, ejoin)
                            assert strong(b, union, ejoin)
                            counts["verified_amalgams"] += 1

assert counts == dict(total_spans=5993, compatible=2625,
                      strong_input_spans=2625, verified_amalgams=2625), counts

# Negative control: no strong K3 base in either K5; the free union fails C0.
k5 = edges(5, (1 << 10) - 1)
assert sparse(set(range(5)), k5)
assert not strong(set(range(3)), set(range(5)), k5)
e1 = {frozenset(("p", x) if x < 3 else ("l", x) for x in e)
      for e in k5}
e2 = {frozenset(("p", x) if x < 3 else ("r", x) for x in e)
      for e in k5}
assert delta({("p", p) for p in range(3)} |
             {("l", 3), ("l", 4), ("r", 3), ("r", 4)}, e1 | e2) == -3
print(counts)
print("Negative K5-over-K3 control passed.")
