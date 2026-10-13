#!/usr/bin/env python3
"""Exhaustively check the no-cross old-neighbour criterion on small graphs."""
from itertools import product

graph_count = 0
admissible_cuts = 0
for n in range(1, 6):
    vertices = tuple(range(n))
    pairs = [(u,v) for u in vertices for v in range(u)]
    for mask in range(1 << len(pairs)):
        edges = {frozenset(p) for i,p in enumerate(pairs) if mask & (1 << i)}
        for roles in product(range(3), repeat=n):
            # 0=old selected, 1=old omitted, 2=new block
            x = {i for i,r in enumerate(roles) if r == 0}
            omitted = {i for i,r in enumerate(roles) if r == 1}
            a = x | omitted
            b = {i for i,r in enumerate(roles) if r == 2}
            if any(frozenset((u,v)) in edges for u in b for v in omitted):
                continue
            # Each edge inside the union is contained in either factor.
            whole = a | x | b
            assert all(
                not e <= whole or e <= a or e <= (x | b)
                for e in edges
            )
            admissible_cuts += 1
        graph_count += 1
print({"labelled_graphs":graph_count,"admissible_splits":admissible_cuts})
