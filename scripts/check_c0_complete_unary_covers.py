#!/usr/bin/env python3
"""Adversarial finite regression for complete set-valued unary closures.

Enumerates every function C:[n] -> P([n]) for 0 <= n <= 4.
When x in C(x) and y in C(x) implies C(y) subset C(x), check that
the union of C(x), x in S, is a finite C-closed cover of S.  Also
include a reflexive but nontransitive operation which fails closure.

These finite checks do NOT certify any countable Fraisse theorem.
"""
from itertools import product

operations = complete = subsets_checked = 0
by_size = {}
for n in range(5):
    universe = range(1 << n)
    for values in product(universe, repeat=n):
        operations += 1
        if not all(values[x] & (1 << x) for x in range(n)):
            continue
        if not all((not (values[x] & (1 << y))) or
                   (values[y] & ~values[x] == 0)
                   for x in range(n) for y in range(n)):
            continue
        complete += 1
        by_size[n] = by_size.get(n, 0) + 1
        for source in universe:
            generated = 0
            for x in range(n):
                if source & (1 << x):
                    generated |= values[x]
            assert (source & generated) == source
            for x in range(n):
                if generated & (1 << x):
                    assert (values[x] & ~generated) == 0
            subsets_checked += 1

bad = (0b011, 0b110, 0b100)
assert all(bad[x] & (1 << x) for x in range(3))
assert (bad[0] & (1 << 1)) and (bad[1] & ~bad[0])
assert (bad[0] | 0) == 0b011
assert (bad[1] & ~bad[0]) != 0

print({"all_operations": operations,
       "complete_operations": complete,
       "closed_cover_subsets": subsets_checked,
       "complete_by_size": by_size,
       "nontransitive_counterexample_checked": True})
