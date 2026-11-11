#!/usr/bin/env python3
"""Adversarial finite test of fair closure-component recursion.

Unlike the enabledness regression, this checks the *whole schedule*:
whole classes, strict growth, C-closure, the least eligible priority,
and eventual exhaustion. Every reflexive/transitive finite-valued unary
operation on carriers of size <= 4 is included. The finite-carrier
procedure stops when Q is the whole carrier.
"""
from itertools import product

stats = dict(preorders=0, components=0, steps=0, closed_prefixes=0,
             visited_vertices=0, lower_checks=0)

for n in range(1, 5):
    full = (1 << n) - 1
    for rows in product(range(1 << n), repeat=n):
        if any(not (rows[x] >> x & 1) for x in range(n)):
            continue
        if any(rows[y] & ~rows[x]
               for x in range(n) for y in range(n)
               if rows[x] >> y & 1):
            continue

        stats["preorders"] += 1
        values = [sum(1 << y for y in range(n) if rows[y] == rows[x])
                  for x in range(n)]
        lowers = [rows[x] & ~values[x] for x in range(n)]
        q = 0
        chosen = []
        components = set(values)
        stats["components"] += len(components)
        while q != full:
            assert all(not (rows[x] & ~q)
                       for x in range(n) if q >> x & 1), (n, rows, q)
            stats["closed_prefixes"] += 1
            enabled = [x for x in range(n)
                       if not (q >> x & 1) and not (lowers[x] & ~q)]
            assert enabled, (n, rows, q)
            x = min(enabled)
            chosen.append(x)
            assert not (q & values[x]), (n, rows, q, x)
            assert (lowers[x] & ~q) == 0
            qnew = q | values[x]
            assert qnew != q
            assert (qnew & ~q) == values[x]
            assert all(not (rows[y] & ~qnew)
                       for y in range(n) if qnew >> y & 1)
            assert all(not (rows[y] & ~q)
                       for y in range(n) if q >> y & 1)
            q = qnew
            stats["steps"] += 1
            stats["lower_checks"] += len(enabled)

        assert q == full and len(chosen) == len(components)
        assert len({values[x] for x in chosen}) == len(components)
        stats["visited_vertices"] += n

# Designed adversarial instance: many unrelated minimal-rank components
# and one higher-rank component whose dependency is a high numeric label.
# Rank-only sorting can delay it arbitrarily; eligible numeric priority
# chooses it once its dependency has appeared.
for n in (5, 9, 17):
    rows = [1 << x for x in range(n)]
    rows[1] |= 1 << (n-1)
    q = 0
    for _ in range(n):
        cls = [sum(1 << y for y in range(n) if rows[y] == rows[x])
               for x in range(n)]
        lowers = [rows[x] & ~cls[x] for x in range(n)]
        enabled = [x for x in range(n) if not (q >> x & 1)
                   and not (lowers[x] & ~q)]
        assert enabled
        q |= cls[min(enabled)]
    assert q == (1 << n) - 1

assert stats["preorders"] == 389, stats
print("track A fair recursion finite adversarial regression:", stats)
