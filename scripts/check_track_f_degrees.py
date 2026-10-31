"""Independent finite count of canonical component-interval vertex orders.

Count orders by direct lex-minimal local adjacency codes, independently
of the component linear-extension times stabiliser product formula.
No infinite Ramsey or recurrence conclusion follows from these tests.
"""
from itertools import combinations, permutations, product
from math import factorial
from collections import Counter
import json

def reach_components(out):
    n = len(out)
    reach = [(1 << i) | out[i] for i in range(n)]
    for k in range(n):
        for x in range(n):
            if reach[x] >> k & 1:
                reach[x] |= reach[k]
    unseen = set(range(n))
    components = []
    while unseen:
        x = min(unseen)
        c = tuple(y for y in range(n) if y in unseen
                  and reach[x] >> y & 1 and reach[y] >> x & 1)
        components.append(c)
        unseen.difference_update(c)
    return reach, components

def degree_product(out, reach, components):
    n = len(out)
    belongs = {v: i for i, comp in enumerate(components) for v in comp}
    lowers = [{belongs[w] for w in range(n)
               if reach[comp[0]] >> w & 1 and w not in comp}
              for comp in components]
    count = 0
    for order in permutations(range(len(components))):
        previous = set()
        for i in order:
            if not lowers[i] <= previous:
                break
            previous.add(i)
        else:
            count += 1
    kernels = []
    for comp in components:
        lower = tuple(w for w in range(n) if reach[comp[0]] >> w & 1
                      and w not in comp)
        carrier = lower + comp
        g = 0
        for p in permutations(comp):
            mapping = dict(zip(comp, p)) | {w: w for w in lower}
            if all(bool(out[x] >> y & 1) ==
                   bool(out[mapping[x]] >> mapping[y] & 1)
                   for x in carrier for y in carrier):
                g += 1
        kernels.append(g)
    for g in kernels:
        count *= g
    return count

def direct_count(out, reach, components):
    n = len(out)
    count = 0
    def adjacency_code(order):
        return tuple((out[x] >> y) & 1 for x in order for y in order)
    for order in permutations(range(n)):
        index = {x: i for i, x in enumerate(order)}
        ok = True
        for comp in components:
            positions = sorted(index[x] for x in comp)
            if positions[-1] - positions[0] + 1 != len(comp):
                ok = False
                break
            lower = tuple(x for x in order if reach[comp[0]] >> x & 1
                          and x not in comp)
            if lower and index[lower[-1]] >= positions[0]:
                ok = False
                break
            actual_comp = tuple(x for x in order if x in comp)
            actual = adjacency_code(lower + actual_comp)
            canonical = min(adjacency_code(lower + p)
                            for p in permutations(comp))
            if actual != canonical:
                ok = False
                break
        count += ok
    return count

def run():
    stats = Counter()
    counts_by_size = Counter()
    for n in range(6):
        pairs = tuple(combinations(range(n), 2))
        for i, choices in enumerate(product(range(3), repeat=len(pairs))):
            if n == 5 and i % 23 != 0:
                continue
            out = [0] * n
            for (a, b), choice in zip(pairs, choices):
                if choice == 1:
                    out[a] |= 1 << b
                elif choice == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            reach, components = reach_components(out)
            formula_count = degree_product(out, reach, components)
            enumeration_count = direct_count(out, reach, components)
            assert formula_count == enumeration_count, (out, formula_count, enumeration_count)
            assert formula_count <= factorial(n)
            stats["orientations"] += 1
            stats["candidate_orders"] += factorial(n)
            counts_by_size[n] += 1
    assert stats["orientations"] == 1965
    return {"status": "PASS", "scope": "finite order counting only",
            "checks": dict(stats), "instances_by_size": dict(counts_by_size)}
if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
