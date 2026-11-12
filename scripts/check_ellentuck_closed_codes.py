#!/usr/bin/env python3
"""Finite-regression audit for the closed support-domain code family.

Exhaustively checks fixed-point characterization, finite obstruction,
and idempotence. Finite data cannot prove the infinite product-topology
claim; the Lean proof establishes that theorem.
"""
from itertools import product


def check(n: int, m: int):
    systems = fixed_tests = excluded = 0
    for support in product(range(1 << m), repeat=n):
        systems += 1

        def domain(levels):
            return sum(
                (1 << i)
                for i, su in enumerate(support)
                if su & ~levels == 0
            )

        image = {domain(S) for S in range(1 << m)}
        for X in range(1 << n):
            levels = 0
            for i, su in enumerate(support):
                if X & (1 << i):
                    levels |= su
            completed = domain(levels)
            assert (completed & X) == X, ("not extensive", n, m, X)
            restored_levels = 0
            for i, su in enumerate(support):
                if completed & (1 << i):
                    restored_levels |= su
            assert domain(restored_levels) == completed, ("not idempotent", n, m, X)
            assert (completed == X) == (X in image), ("fixed points", n, m, X)
            fixed_tests += 1
            if completed != X:
                excluded += 1
                witnesses = [
                    v for v in range(n)
                    if completed & (1 << v) and not X & (1 << v)
                ]
                assert witnesses, ("missing obstruction", n, m, X)
                v = witnesses[0]
                cylinder = X | (1 << v)
                assert all((Y & cylinder) != X for Y in image), (
                    "open cylinder does not exclude domain", n, m, X, v
                )
    return systems, fixed_tests, excluded


def main():
    totals = [0, 0, 0]
    for n, m in [(0, 0), (0, 3), (1, 3), (2, 3),
                 (3, 3), (4, 3), (3, 4)]:
        counts = check(n, m)
        print(f"{n} vertices, {m} levels: {counts}")
        totals = [x + y for x, y in zip(totals, counts)]
    assert totals == [8778, 102674, 62607]
    print(f"PASS: {totals[0]} finite support systems; "
          f"{totals[1]} fixed-point tests; {totals[2]} excluded codes")
    # Negative control: domains need not preserve binary unions.
    support = (1, 2, 3)
    def D(levels):
        return sum(1 << i for i, su in enumerate(support) if su & ~levels == 0)
    assert (D(1), D(2), D(3)) == (1, 2, 7)
    assert D(1) | D(2) != D(3)
    print("PASS: arbitrary union preservation fails, as expected")


if __name__ == "__main__":
    main()
