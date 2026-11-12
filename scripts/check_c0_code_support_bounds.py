#!/usr/bin/env python3
"""Adversarial support-bound regression for literal pointed codes.

Complete graph and unary incidence pairs must live on the declared support.
Point-generatedness alone does not guarantee this.
"""
from random import Random


def well_supported(s, adj, closure):
    square = {(x, y) for x in s for y in s}
    return adj <= square and closure <= square


def restrict(s, adj, closure, t):
    square = {(x, y) for x in t for y in t}
    return (set(t), adj & square, closure & square)


def main():
    rng = Random(20261112)
    checked = 0
    for n in range(1, 8):
        for _ in range(1000):
            s = {k for k in range(n) if rng.getrandbits(1)}
            if not s:
                continue
            pairs = [(x, y) for x in s for y in s]
            adj = {p for p in pairs if rng.getrandbits(1)}
            closure = {p for p in pairs if rng.getrandbits(1)}
            assert well_supported(s, adj, closure)
            for x, y in adj | closure:
                assert x < n and y < n
            t = {x for x in s if rng.getrandbits(1)}
            if t:
                ts, ta, tc = restrict(s, adj, closure, t)
                assert ts == t and well_supported(ts, ta, tc)
            checked += 1
    # Distinct phantom edge pairs on a one-point support all satisfy
    # point generation (C(0)={0}) and point-in-support, yet fail
    # well-supportedness and defeat bounded-fibre finiteness.
    s, point, closure = {0}, 0, {(0, 0)}
    keys = set()
    for k in range(1, 1001):
        adj = {(k, k + 1)}
        assert point in s
        assert all((((point, v) in closure) == (v in s)) for v in range(4))
        assert not well_supported(s, adj, closure)
        keys.add((frozenset(s), point, frozenset(adj), frozenset(closure)))
    assert len(keys) == 1000
    print(f"OK: {checked:,} well-supported finite codes and restrictions; "
          "1,000 distinct bounded-support phantom-code negative controls")


if __name__ == "__main__":
    main()
