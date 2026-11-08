#!/usr/bin/env python3
"""Independent finite regression for complete-unary component descent.

Enumerate all set-valued unary operations on n<=4. For each reflexive
and transitive operation, compare full-value equality classes, their
finite lower sets and strict closure-size descent. This is diagnostic
evidence, not a proof checker.
"""
from itertools import product

results = []
for n in range(5):
    count = valid = components = lowers = 0
    for values in product(range(1 << n), repeat=n):
        count += 1
        if not all(values[x] & (1 << x) for x in range(n)):
            continue
        if not all(
            not (values[x] & (1 << y)) or
            ((values[y] & ~values[x]) == 0)
            for x in range(n) for y in range(n)
        ):
            continue
        valid += 1
        classes = [
            {y for y in range(n) if values[y] == values[x]}
            for x in range(n)
        ]
        for x in range(n):
            components += 1
            assert all(values[x] & (1 << y) for y in classes[x])
            for y in range(n):
                assert classes[x] == classes[y] or classes[x].isdisjoint(classes[y])
                if (values[x] & (1 << y)) and y not in classes[x]:
                    lowers += 1
                    assert values[y] & ~values[x] == 0
                    assert values[y] != values[x]
                    assert values[y].bit_count() < values[x].bit_count()
                    strict_lower = {
                        z for z in range(n)
                        if values[x] & (1 << z) and z not in classes[x]
                    }
                    assert classes[y] <= strict_lower
    results.append((n, count, valid, components, lowers))
expected = [
    (0, 1, 1, 0, 0), (1, 2, 1, 1, 0),
    (2, 16, 4, 8, 2), (3, 512, 29, 87, 48),
    (4, 65536, 355, 1420, 1200),
]
assert results == expected, (results, expected)
print({
    "all_operations": sum(x[1] for x in results),
    "complete_operations": sum(x[2] for x in results),
    "intrinsic_classes_checked": sum(x[3] for x in results),
    "strict_lower_dependencies": sum(x[4] for x in results),
    "failures": 0,
})
