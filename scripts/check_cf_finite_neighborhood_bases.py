#!/usr/bin/env python3
"""Finite adversarial checks of the directed neighborhood-basis lemmas.

This checks mathematical finite analogues, not a Lean proof or actual C_F host.
For all 4-element increasing sequences from 0..8, check both directions:
* agreement of m initial enumeration entries -> level membership <m;
* agreement below X[n]+1 -> initial n+1 enumeration entries agree.
It also checks that no uniform finite cutoff decides the first enumerated
element, illustrating why the reverse cutoff must depend on the base point.
"""
from itertools import combinations, product


def run():
    points = list(combinations(range(9), 4))
    checks = 0
    for x, y in product(points, repeat=2):
        for m in range(5):
            if x[:m] == y[:m]:
                assert all((q in x) == (q in y) for q in range(m))
            checks += 1
        for n in range(4):
            cutoff = x[n] + 1
            if all((q in x) == (q in y) for q in range(cutoff)):
                assert x[:n + 1] == y[:n + 1]
            checks += 1
    for m in (0, 1, 2, 5, 10):
        x = tuple(range(m, m + 4))
        y = tuple(range(m + 1, m + 5))
        assert x[0] != y[0]
        assert all((q in x) == (q in y) for q in range(m))
    assert len(points) == 126 and checks == 142_884
    print(f"PASS: {checks} directed base checks over {len(points)} "
          "increasing enumerations; 5 no-uniform-cutoff witnesses")


if __name__ == "__main__":
    run()
