#!/usr/bin/env python3
"""Finite check of unary ancestor closure under directed-component transports.

Every edge points towards an earlier component. Permutations need not
preserve the complete component order, only the direction of actual
dependencies. The structural theorem has a separate Lean proof.
"""
from itertools import permutations

checks = 0
rejected = 0
nontrivial = 0
for n in range(1, 6):
    edges = [(i, j) for i in range(n) for j in range(i)]
    for mask in range(1 << len(edges)):
        old = [set() for _ in range(n)]
        for k, (i, j) in enumerate(edges):
            if mask & (1 << k):
                old[i].add(j)
        def reachable(E, root):
            seen = set()
            todo = [root]
            while todo:
                v = todo.pop()
                if v not in seen:
                    seen.add(v)
                    todo.extend(E[v])
            return seen
        source = [reachable(old, i) for i in range(n)]
        for permutation in permutations(range(n)):
            if any(permutation[j] > permutation[i] for i in range(n) for j in old[i]):
                rejected += 1
                continue
            new_old = [set() for _ in range(n)]
            for i in range(n):
                new_old[permutation[i]].update(permutation[j] for j in old[i])
            assert all(j < i for i in range(n) for j in new_old[i])
            for i in range(n):
                target = reachable(new_old, permutation[i])
                assert target == {permutation[j] for j in source[i]}
                checks += 1
                if permutation != tuple(range(n)):
                    nontrivial += 1
assert checks > 0 and rejected > 0 and nontrivial > 0
print({"closure_image_checks": checks,
       "invalid_back_edge_relabelings_rejected": rejected,
       "non_order_preserving_valid_cases": nontrivial})
