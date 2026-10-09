"""Independent finite model checks of the old-neighbour/back-edge bijection.

The entire labelled simple-graph universe with at most five vertices
is examined.  This diagnostic does not replace a Lean proof.
"""
from itertools import combinations

graphs = 0
configurations = 0

for n in range(6):
    pairs = tuple(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        edges = {
            frozenset((u, v))
            for i, (u, v) in enumerate(pairs)
            if mask & (1 << i)
        }
        graphs += 1
        for old_mask in range(1 << n):
            old = {v for v in range(n) if old_mask & (1 << v)}
            for x in range(n):
                if x in old:
                    continue
                neighbours = {
                    y for y in old if frozenset((x, y)) in edges
                }
                back_edges = {
                    edge for edge in edges
                    if x in edge and edge.issubset(old | {x})
                }
                pairs_from_neighbours = {
                    frozenset((x, y)) for y in neighbours
                }
                assert pairs_from_neighbours == back_edges, (
                    "edge/neighbor mismatch", n, mask, old_mask, x
                )
                assert len(neighbours) == len(back_edges)
                assert len(neighbours) == len(pairs_from_neighbours)
                configurations += 1

assert graphs == 1100, graphs
assert configurations == 84073, configurations
print(
    f"Checked {graphs} labelled simple graphs and {configurations} "
    "old-set/new-vertex configurations."
)
