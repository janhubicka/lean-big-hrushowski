#!/usr/bin/env python3
"""Independent exhaustive checks for reachable-dependent-history counts.

Reachable history is a tuple stored newest-first. Choice sets can vary
with the precise prior history while their sizes depend only on its
length. Unreachable histories are irrelevant, including invalid labels.
"""
from itertools import product

def reach(choose, n):
    histories = {()}
    for _ in range(n):
        histories = {(a,)+h for h in histories for a in choose(h)}
    return histories

def check():
    tested = 0
    for factors in product(range(4), repeat=4):
        for salt in range(3):
            def choose(h):
                n = len(h)
                if n >= len(factors):
                    return set()
                shift = (salt + sum((i + 1)*a for i,a in enumerate(h))) % 11
                return {shift*20+a for a in range(factors[n])}
            expected = 1
            for n in range(5):
                got = reach(choose, n)
                assert len(got) == expected, (factors, salt, n, len(got))
                assert all(len(h)==n for h in got)
                if n<4:
                    assert all(len(choose(h))==factors[n] for h in got)
                    expected *= factors[n]
                tested += 1

    # Previous lemma required fibre equality for every arbitrary
    # history. Here every reachable stage-1 prior is (0,), while
    # arbitrary, unreachable (1,) has zero options.
    def only_reachable(h):
        if h == (): return {0}
        if h == (0,): return {10, 11}
        return set()
    assert reach(only_reachable, 1) == {(0,)}
    assert len(only_reachable((0,))) == 2
    assert len(only_reachable((1,))) == 0
    assert len(reach(only_reachable, 2)) == 2
    print(f"PASS: {tested} exhaustive stage counts; reachable-only "
          "uniformity and invalid-history negative control")

if __name__ == "__main__": check()
