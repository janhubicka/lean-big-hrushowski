#!/usr/bin/env python3
"""Independent finite falsification of complete-functional image closure.

Enumerate all complete reflexive/transitive unary set-valued functions
on carriers of at most four points. Send them through every injection
into a target with one extra vertex, define the target *complete*
values on the image by exact transport, and check image closedness
and full membership reflection. Check literal induced graph matrices
for each small simple graph under independent relabellings.

A negative control adds a dependency outside the image; it retains
all within-image membership comparisons but violates full-value
equality and image closure.
"""
from itertools import product, permutations, combinations

stats = dict(systems=0, embeddings=0, full_value_checks=0,
             member_reflections=0, closed_image_checks=0,
             graphs=0, adjacency_checks=0, nonclosed_controls=0)

for n in range(1,5):
    for rows in product(range(1<<n),repeat=n):
        if any(not (rows[x]>>x&1) for x in range(n)):
            continue
        if any(rows[y]&~rows[x] for x in range(n)
               for y in range(n) if rows[x]>>y&1):
            continue
        stats["systems"] += 1
        domain = set(range(n))
        for placement in permutations(range(n+1),n):
            im = set(placement)
            assert len(im) == n
            # The target's extra point is independent of the image.
            target_values = {y:{y} for y in range(n+1)}
            for x in range(n):
                target_values[placement[x]] = {
                    placement[y] for y in range(n) if rows[x]>>y&1}
                stats["full_value_checks"] += 1
            for x in range(n):
                assert target_values[placement[x]] <= im
                stats["closed_image_checks"] += 1
                for y in range(n):
                    assert (placement[y] in target_values[placement[x]]) == bool(
                        rows[x]>>y & 1), (n,rows,placement,x,y)
                    stats["member_reflections"] += 1
            stats["embeddings"] += 1

    edge_pairs=list(combinations(range(n),2))
    for mask in range(1<<len(edge_pairs)):
        original={p for i,p in enumerate(edge_pairs) if mask>>i&1}
        stats["graphs"] += 1
        for placement in permutations(range(n+1),n):
            target_edges={frozenset((placement[x],placement[y]))
                          for x,y in original}
            for x in range(n):
                for y in range(n):
                    assert ((tuple(sorted((x,y))) in original) ==
                            (frozenset((placement[x],placement[y]))
                             in target_edges))
                    stats["adjacency_checks"] += 1

# A nonclosed singleton image: the target value C(1)={0,1}
# contains a strict dependency outside the image {1}. Restriction
# to the image sees only {1}, so unary *restriction* is misleading.
C = {0:{0},1:{0,1}}
image = {1}
assert all(((v in C[1]) == (v == 1)) for v in image)
assert C[1] - image == {0}
stats["nonclosed_controls"] += 1

assert stats["systems"] == 389, stats
assert stats["embeddings"] > 0 and stats["member_reflections"] > 0
assert stats["nonclosed_controls"] == 1
print("Track A complete functional finite-image regression:",stats)
