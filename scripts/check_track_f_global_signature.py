#!/usr/bin/env python3
"""Independent finite tests: genuine SCC signatures and lower initial segments.

No Lean theorem is inferred from the finite enumeration. Negative controls
check the necessity of both SCC intervals and successor-first orientation.
"""
from itertools import permutations
from check_track_f_canonical_local import orientations, components


def signature(order, comps):
    position = {v: i for i, v in enumerate(order)}
    ranks = tuple(part for part, _ in sorted(
        comps, key=lambda item: min(position[v] for v in item[0])))
    local = frozenset((x, y) for part, _ in comps
                      for x in part for y in part if position[x] < position[y])
    return ranks, local


def is_interval(order, comps):
    p = {v: i for i, v in enumerate(order)}
    return all(max(p[x] for x in part) - min(p[x] for x in part) + 1 == len(part)
               for part, _ in comps)


def successor_first(order, comps):
    p = {v: i for i, v in enumerate(order)}
    return all(p[y] < p[x]
               for part, closure in comps
               for x in part for y in closure - part)


def assert_lower_initial(order, comps):
    p = {v: i for i, v in enumerate(order)}
    for part, closure in comps:
        lower = closure - part
        for y in lower:
            for z in part:
                assert p[y] < p[z], (order, part, lower)
            for z in closure:
                if p[z] < p[y]:
                    assert z in lower, (order, part, lower, z, y)


def negative_controls():
    # Same SCC ranking and internal SCC order, different interleaving:
    # the two global orders need not agree without the interval hypothesis.
    cyc_iso = (frozenset({1}), frozenset({2}),
               frozenset({0}), frozenset())
    comps = components(cyc_iso)
    a = (0, 3, 1, 2)
    b = (0, 1, 3, 2)
    assert a != b and signature(a, comps) == signature(b, comps)
    assert not is_interval(a, comps) and not is_interval(b, comps)

    # A source cannot precede its proper successor in a successor-first order.
    edge = (frozenset({1}), frozenset())
    c = components(edge)
    assert not successor_first((0, 1), c)
    assert successor_first((1, 0), c)


def main():
    negative_controls()
    total_orientations = interval_orders = successor_orders = 0
    for n in range(5):
        for out in orientations(n):
            total_orientations += 1
            comps = components(out)
            seen = {}
            for order in permutations(range(n)):
                if is_interval(order, comps):
                    s = signature(order, comps)
                    assert s not in seen, ("signature collision", out, seen.get(s), order)
                    seen[s] = order
                    interval_orders += 1
                if successor_first(order, comps):
                    assert_lower_initial(order, comps)
                    if is_interval(order, comps):
                        successor_orders += 1
    print(f"PASS: {total_orientations} orientations, {interval_orders} interval "
          f"enumerations with injective SCC signature, {successor_orders} "
          "successor-first interval orders; interleaving and backward-edge "
          "negative controls")


if __name__ == "__main__":
    main()
