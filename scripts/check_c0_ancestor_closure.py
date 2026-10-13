#!/usr/bin/env python3
"""Finite adversarial regression for the C0 backward-component closure.

Checks all directed dependency diagrams on 1,...,6 components in which
each edge points to a strictly earlier component, as well as multiple
finite vertex multiplicities for diagrams with at most five components.
This is diagnostic only, not a substitute for the Lean proof.
"""
from itertools import product

diagrams = 0
vertices = 0
mutual_pairs = 0
back_edges = 0
for n in range(1, 7):
    pairs = [(i, j) for i in range(n) for j in range(i)]
    for mask in range(1 << len(pairs)):
        old = [set() for _ in range(n)]
        for k, (i, j) in enumerate(pairs):
            if (mask >> k) & 1:
                old[i].add(j)
                back_edges += 1
        ancestor = []
        for i in range(n):
            todo = [i]
            visited = set()
            while todo:
                j = todo.pop()
                if j in visited:
                    continue
                visited.add(j)
                todo.extend(old[j])
            ancestor.append(visited)
            assert i in visited and all(j <= i for j in visited)
        for i in range(n):
            for j in ancestor[i]:
                assert ancestor[j] <= ancestor[i]
        # The vertices of one block can have different labels, but
        # they have the same unary closure and same mutual-reachability class.
        multiplicities = product([1, 2], repeat=n) if n <= 5 else [(1, 2, 1, 2, 1, 2)]
        for sizes in multiplicities:
            component_of = [i for i in range(n) for _ in range(sizes[i])]
            closures = [
                {w for w, j in enumerate(component_of) if j in ancestor[i]}
                for i in component_of
            ]
            for u, i in enumerate(component_of):
                assert u in closures[u]
                for v, j in enumerate(component_of):
                    is_mutual = v in closures[u] and u in closures[v]
                    assert is_mutual == (i == j)
                    if v in closures[u]:
                        assert closures[v] <= closures[u]
                    mutual_pairs += int(is_mutual)
                vertices += 1
        diagrams += 1
assert diagrams == sum(2 ** (n*(n-1)//2) for n in range(1,7))
print({"dependency_diagrams":diagrams,"vertex_samples":vertices,
       "mutual_pairs":mutual_pairs,"back_edges":back_edges})
