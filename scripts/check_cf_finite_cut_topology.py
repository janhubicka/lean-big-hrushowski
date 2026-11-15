#!/usr/bin/env python3
"""Finite adversarial regression for Track E supported-domain cut lemmas.

These are toy finite-level support systems, NOT the infinite C_F birth tower.
Every vertex supports its own level, and support levels never exceed its birth.
One explicit singleton-level witness at each level is kept for the reverse cut
direction. The second vertex on each level has every possible admissible
support in exhaustive combinations.
"""
from itertools import combinations, product

N = 4
choices = [
    [
        frozenset({n}) | frozenset(k for k in range(n) if mask & (1 << k))
        for mask in range(1 << n)
    ]
    for n in range(N)
]
level_sets = [
    frozenset(k for k in range(N) if mask & (1 << k))
    for mask in range(1 << N)
]


def domain(vertices, levels):
    return frozenset(
        i for i, (_, support) in enumerate(vertices) if support <= levels
    )


def check_all():
    checks = 0
    assignments = 0
    for chosen in product(*choices):
        assignments += 1
        vertices = (
            [(n, frozenset({n})) for n in range(N)]
            + [(n, chosen[n]) for n in range(N)]
        )
        for s, t in product(level_sets, repeat=2):
            ds, dt = domain(vertices, s), domain(vertices, t)
            for m in range(N + 1):
                lhs = all((n in s) == (n in t) for n in range(m))
                rhs = all(
                    (i in ds) == (i in dt)
                    for i, (birth, _) in enumerate(vertices)
                    if birth < m
                )
                assert lhs == rhs, (chosen, s, t, m, lhs, rhs)
                checks += 1
        for h in combinations(range(N), 3):
            full = domain(vertices, frozenset(h))
            for m in range(4):
                prefix = frozenset(h[:m])
                lhs = domain(vertices, prefix)
                rhs = frozenset(
                    i for i, (birth, _) in enumerate(vertices)
                    if i in full and birth in prefix
                )
                assert lhs == rhs, (chosen, h, m, lhs, rhs)
                checks += 1

    # Each omitted hypothesis is genuinely doing work.
    no_singleton_level_one = [(0, frozenset({0})), (1, frozenset({0, 1}))]
    s, t = frozenset(), frozenset({1})
    assert s != t and domain(no_singleton_level_one, s) == domain(
        no_singleton_level_one, t
    )
    future_support = [(0, frozenset({0, 1}))]
    s, t = frozenset({0}), frozenset({0, 1})
    assert s & frozenset({0}) == t & frozenset({0})
    assert domain(future_support, s) != domain(future_support, t)
    descending_h = (2, 0, 3)
    prefix = frozenset(descending_h[:1])
    v = (2, frozenset({0, 2}))
    assert v[1] <= frozenset(descending_h) and v[0] in prefix
    assert not v[1] <= prefix

    assert assignments == 64 and checks == 82944
    print(f"PASS: {checks} finite cut/prefix checks over {assignments} "
          "support assignments; three dropped-hypothesis counterexamples")


if __name__ == "__main__":
    check_all()
