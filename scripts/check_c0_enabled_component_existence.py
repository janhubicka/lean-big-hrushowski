#!/usr/bin/env python3
"""Independent finite falsification test for enabled component existence.

In finite carriers the statement is tested for every proper Q, since the
infinite-carrier assumption in Lean guarantees Q is never the whole carrier.
"""
from itertools import product

stats = {
    "preorders": 0,
    "proper_sets": 0,
    "enabled_candidates": 0,
    "closed_sets": 0,
    "closed_extensions": 0,
}

for n in range(1, 5):
    whole = (1 << n) - 1
    for rows in product(range(1 << n), repeat=n):
        # C is reflexive and transitive, represented by n complete values.
        if any(not (rows[x] >> x & 1) for x in range(n)):
            continue
        if any(
            rows[y] & ~rows[x]
            for x in range(n) for y in range(n)
            if rows[x] >> y & 1
        ):
            continue

        stats["preorders"] += 1

        def component(x):
            return sum(1 << y for y in range(n) if rows[y] == rows[x])

        def lower(x):
            return rows[x] & ~component(x)

        for q in range(1 << n):
            if q == whole:
                continue
            stats["proper_sets"] += 1
            enabled = [
                x for x in range(n)
                if not (q >> x & 1) and not (lower(x) & ~q)
            ]
            assert enabled, (n, rows, q)
            stats["enabled_candidates"] += len(enabled)

            # EVERY rank-minimal unlisted vertex is enabled.
            smallest_rank = min(
                rows[x].bit_count()
                for x in range(n) if not (q >> x & 1)
            )
            for x in range(n):
                if (not (q >> x & 1)
                        and rows[x].bit_count() == smallest_rank):
                    assert x in enabled, (n, rows, q, x)

            if all(
                not (rows[x] & ~q)
                for x in range(n) if q >> x & 1
            ):
                stats["closed_sets"] += 1
                x = min(enabled)  # the fair numerical priority
                new = q | component(x)
                assert not (q >> x & 1)
                assert new != q
                assert all(
                    not (rows[y] & ~new)
                    for y in range(n) if new >> y & 1
                ), (n, rows, q, x)
                stats["closed_extensions"] += 1

assert stats == {
    "preorders": 389,
    "proper_sets": 5541,
    "enabled_candidates": 7899,
    "closed_sets": 2093,
    "closed_extensions": 2093,
}, stats
print(stats)
