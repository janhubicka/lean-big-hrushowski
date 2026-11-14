#!/usr/bin/env python3
"""Finite falsification of predecessor-count ranks for fair component orders.

For all complete unary systems on at most four vertices, construct
the fair component births. Then test all componentwise-injective
numeric local key assignments. Every finite strict lex order must
have a rank bijection onto the finite ordinal of its size, preserve
and reflect comparisons, and realize the predecessor-rank initial cut.
The infinite no-greatest step is deliberately not tested here.
"""
from itertools import product

stats = dict(unary_systems=0, orders=0, rank_checks=0,
             comparisons=0, predecessor_images=0, key_collisions=0)
for n in range(1, 5):
    whole = (1 << n) - 1
    for rows in product(range(1 << n), repeat=n):
        if any(not (rows[x] >> x & 1) for x in range(n)):
            continue
        if any(rows[y] & ~rows[x] for x in range(n) for y in range(n)
               if rows[x] >> y & 1):
            continue
        stats["unary_systems"] += 1
        def comp(x):
            return sum(1 << y for y in range(n) if rows[x] == rows[y])
        def lower(x):
            return rows[x] & ~comp(x)
        birth = [-1] * n
        q = 0
        level = 0
        while q != whole:
            eligible = [x for x in range(n)
                        if not (q >> x & 1) and not (lower(x) & ~q)]
            assert eligible
            x = min(eligible)
            b = comp(x)
            assert not (q & b)
            for y in range(n):
                if b >> y & 1:
                    birth[y] = level
            q |= b
            level += 1
        assert min(birth) == 0

        for keys in product(range(n), repeat=n):
            if any(x != y and birth[x] == birth[y] and keys[x] == keys[y]
                   for x in range(n) for y in range(n)):
                stats["key_collisions"] += 1
                continue

            def before(x, y):
                return (birth[x], keys[x]) < (birth[y], keys[y])

            pred = [{y for y in range(n) if before(y, x)}
                    for x in range(n)]
            rank = [len(pred[x]) for x in range(n)]
            assert set(rank) == set(range(n)), (n, rows, birth, keys, rank)
            stats["orders"] += 1

            for x in range(n):
                assert {rank[y] for y in pred[x]} == set(range(rank[x]))
                stats["predecessor_images"] += 1
                for y in range(n):
                    assert before(x, y) == (rank[x] < rank[y])
                    stats["comparisons"] += 1
                stats["rank_checks"] += 1

# Without local injectivity, a tied two-vertex component gives two
# incomparable vertices of the same rank.
keys = (0, 0)
birth = (0, 0)
rank = [0, 0]
assert rank[0] == rank[1] and keys[0] == keys[1]
assert stats["unary_systems"] == 389 and stats["orders"] > 0
print("Fair vertex rank/order-isomorphism finite regression:", stats)
