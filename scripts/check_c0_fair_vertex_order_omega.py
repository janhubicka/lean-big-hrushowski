#!/usr/bin/env python3
"""Exhaustive finite adversarial check for lexicographic fair component orders.

Enumerate complete reflexive/transitive unary operations on <=4 vertices,
then all local numeric key assignments which are injective on each
birth-component. Check strict order, initial prefixes and convex blocks.
The no-greatest-vertex statement is only true on the infinite carrier
and is NOT claimed to follow from these finite checks.
"""
from itertools import product

stats = dict(unary_systems=0, permitted_keys=0, order_pairs=0,
             order_triples=0, initial_pairs=0, convex_triples=0,
             class_key_collisions=0)
for n in range(1, 5):
    full = (1 << n) - 1
    for rows in product(range(1 << n), repeat=n):
        if any(not (rows[x] >> x & 1) for x in range(n)):
            continue
        if any(rows[y] & ~rows[x] for x in range(n) for y in range(n)
               if rows[x] >> y & 1):
            continue
        stats["unary_systems"] += 1

        def component(x):
            return sum(1 << y for y in range(n) if rows[y] == rows[x])

        def lower(x):
            return rows[x] & ~component(x)

        birth = [-1] * n
        prefixes = [0]
        q = 0
        while q != full:
            enabled = [x for x in range(n) if not (q >> x & 1)
                       and not (lower(x) & ~q)]
            assert enabled
            x = min(enabled)
            comp = component(x)
            assert comp & q == 0
            for y in range(n):
                if comp >> y & 1:
                    assert birth[y] == -1
                    birth[y] = len(prefixes) - 1
            q |= comp
            prefixes.append(q)

        for key in product(range(n), repeat=n):
            if any(x != y and birth[x] == birth[y] and key[x] == key[y]
                   for x in range(n) for y in range(n)):
                stats["class_key_collisions"] += 1
                continue
            stats["permitted_keys"] += 1

            def before(x, y):
                return (birth[x] < birth[y] or
                        (birth[x] == birth[y] and key[x] < key[y]))

            for x in range(n):
                assert not before(x, x)
                for y in range(n):
                    if x != y:
                        assert before(x, y) != before(y, x)
                        stats["order_pairs"] += 1
                    for z in range(n):
                        if before(x, y) and before(y, z):
                            assert before(x, z)
                        if birth[x] == birth[z] and before(x, y) and before(y, z):
                            assert birth[y] == birth[x]
                            stats["convex_triples"] += 1
                        stats["order_triples"] += 1
            for cut in prefixes:
                for y in range(n):
                    if not (cut >> y & 1):
                        continue
                    for x in range(n):
                        if before(x, y):
                            assert cut >> x & 1
                        stats["initial_pairs"] += 1

            for x in range(n):
                finite_predecessors = {y for y in range(n) if before(y, x)}
                through_birth = prefixes[birth[x] + 1]
                assert all(through_birth >> y & 1 for y in finite_predecessors)

# The assumption that local keys distinguish vertices of a component
# is necessary: two equivalent vertices with a tied key are incomparable.
rows = (0b11, 0b11)
birth = (0, 0)
key = (0, 0)
assert rows[0] == rows[1] and birth[0] == birth[1]
assert not (birth[0] < birth[1] or
            (birth[0] == birth[1] and key[0] < key[1]))
assert not (birth[1] < birth[0] or
            (birth[1] == birth[0] and key[1] < key[0]))
assert stats["unary_systems"] == 389, stats
assert stats["permitted_keys"] > 0
print("fair vertex-order exhaustive adversarial regression:", stats)
