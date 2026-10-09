"""Exhaustive finite regression for minimal strong increments.

Tests every labelled simple graph on at most five vertices. It is deliberately
independent of the Lean implementation and is not a general proof certificate.
"""
from itertools import combinations

stats = dict(graphs=0, strong_pairs=0, steps=0, equal_closures=0,
             intermediate_checked=0)
for n in range(6):
    full = (1 << n) - 1
    edges = list(combinations(range(n), 2))
    subsets = range(1 << n)
    for graph in range(1 << len(edges)):
        stats["graphs"] += 1
        delta = [
            2 * mask.bit_count() -
            sum(bool(graph >> i & 1) and bool(mask >> u & 1)
                and bool(mask >> v & 1)
                for i, (u, v) in enumerate(edges))
            for mask in subsets
        ]

        def strong(a, b):
            return all(delta[a] <= delta[x]
                       for x in subsets if x & a == a and x & b == x)

        globally_strong = [strong(a, full) for a in subsets]
        closure = [0] * (full + 1)
        for a in subsets:
            supersets = [b for b in subsets
                         if globally_strong[b] and a & b == a]
            assert supersets
            hull = full
            for b in supersets:
                hull &= b
            assert globally_strong[hull] and hull & a == a
            closure[a] = hull

        for D in subsets:
            if not globally_strong[D]:
                continue
            for a in subsets:
                if a & D != a or not globally_strong[a]:
                    continue
                stats["strong_pairs"] += 1
                prefix = a
                while prefix != D:
                    remaining = [v for v in range(n)
                                 if D >> v & 1 and not prefix >> v & 1]
                    assert remaining
                    v = min(remaining, key=lambda x:
                            closure[prefix | (1 << x)].bit_count())
                    extension = closure[prefix | (1 << v)]
                    assert extension & prefix == prefix
                    assert extension & D == extension
                    assert extension != prefix
                    stats["steps"] += 1
                    for x in range(n):
                        if extension >> x & 1 and not prefix >> x & 1:
                            assert closure[prefix | (1 << x)] == extension
                            stats["equal_closures"] += 1
                    for z in subsets:
                        if (z & prefix) == prefix and (z & extension) == z \
                                and strong(z, extension):
                            assert z == prefix or z == extension
                            stats["intermediate_checked"] += 1
                    prefix = extension

assert stats["graphs"] == 1100
print(stats)
