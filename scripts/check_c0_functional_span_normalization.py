#!/usr/bin/env python3
"""Independent complete C0 unary-value transport under arbitrary base splits.

For every graph on <=4 vertices, every index map into a nonempty finite
ordinal of size <= n (including unused ranks), and every literal selected
base, place the base first in two different orders and the other vertices
after it. Compare ALL complete canonical vertex-valued unary closures
before and after the induced graph transport. Check closed-base cases
separately, including bases which are not an original initial segment.
This is diagnostic, not a Lean proof.
"""
from itertools import combinations, product


def complete_values(n, edges, index):
    dependencies = {k: set() for k in set(index)}
    for u, v in edges:
        a, b = index[u], index[v]
        if a > b:
            dependencies[a].add(b)
        if b > a:
            dependencies[b].add(a)
    result = []
    for v in range(n):
        reached, queue = {index[v]}, [index[v]]
        while queue:
            for j in dependencies[queue.pop()]:
                if j not in reached:
                    reached.add(j)
                    queue.append(j)
        result.append(sum(1 << u for u in range(n) if index[u] in reached))
    return tuple(result)


count = closed = noninitial = 0
for n in range(5):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        edges = [p for pos, p in enumerate(pairs) if (mask >> pos) & 1]
        for k in range(1, max(2, n + 1)):
            for ix in product(range(k), repeat=n):
                values = complete_values(n, edges, ix)
                for bits in range(1 << n):
                    base = [i for i in range(n) if (bits >> i) & 1]
                    tail = [i for i in range(n) if not (bits >> i) & 1]
                    for ordered in (base + tail, base[::-1] + tail[::-1]):
                        e = {old: new for new, old in enumerate(ordered)}
                        transported_edges = [
                            tuple(sorted((e[u], e[v]))) for u, v in edges]
                        transported_ix = tuple(ix[old] for old in ordered)
                        transported_values = complete_values(
                            n, transported_edges, transported_ix)
                        for v in range(n):
                            image = sum(1 << e[u] for u in range(n)
                                        if (values[v] >> u) & 1)
                            assert transported_values[e[v]] == image
                        count += 1
                        if all(values[v] & ~bits == 0 for v in base):
                            closed += 1
                            if any(ix[v] > ix[w] for v in base for w in tail):
                                noninitial += 1

assert count == 729686 and closed == 196810 and noninitial == 31188
print({"transported_complete_values": count,
       "unary_closed_base_cases": closed,
       "noninitial_closed_base_cases": noninitial,
       "failures": 0})
