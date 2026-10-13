#!/usr/bin/env python3
"""Finite regression for generated unary closure of downward DAG ancestry."""
from itertools import product

diagrams = 0
pairs_checked = 0
for n in range(1, 6):
    edges = [(i,j) for i in range(n) for j in range(i)]
    for bits in range(1 << len(edges)):
        older = [set() for _ in range(n)]
        for k,(i,j) in enumerate(edges):
            if bits & (1 << k):
                older[i].add(j)
        one = []
        for i in range(n):
            seen = {i}
            todo = [i]
            while todo:
                j = todo.pop()
                for k in older[j]:
                    if k not in seen:
                        seen.add(k)
                        todo.append(k)
            one.append(seen)
        def gen(s):
            return set().union(*(one[v] for v in s)) if s else set()
        subsets = [{i for i in range(n) if bits & (1 << i)}
                   for bits in range(1 << n)]
        for s in subsets:
            cl = gen(s)
            assert s <= cl and gen(cl) == cl
            for t in subsets:
                assert gen(s | t) == (cl | gen(t))
                if s <= t:
                    assert cl <= gen(t)
                if gen(s) == s and gen(t) == t:
                    assert gen(s & t) == s & t
                pairs_checked += 1
        diagrams += 1
print({"dependency_diagrams":diagrams, "finite_set_pairs":pairs_checked})
