#!/usr/bin/env python3
"""Independent finite audit of actual order restriction to C_B.

Checks literal pairwise comparisons on labelled vertices, the old-part
initial segment for successor-first orders, and the global canonical
criterion against a direct complete directed-matrix minimisation.
"""
from itertools import permutations, combinations
from check_track_f_canonical_local import orientations, components, lex_code
from check_track_f_global_canonical_count import legal_components, legal_local_codes


def all_subsets(points):
    points = tuple(points)
    return (frozenset(c) for k in range(len(points)+1)
            for c in combinations(points, k))


def admissible_local(out, local, lower):
    fixed = []
    for candidate in permutations(local):
        if all(candidate[i] == u for i, u in enumerate(local)
               if u in lower):
            fixed.append(candidate)
    assert fixed
    return lex_code(out, local) == min(lex_code(out, f) for f in fixed)


def check(out):
    n = len(out)
    comps = components(out)
    order_count = successor_count = canonical_count = 0
    for order in permutations(range(n)):
        p = {u: i for i, u in enumerate(order)}
        order_count += 1
        for subset in all_subsets(range(n)):
            local = tuple(u for u in order if u in subset)
            assert len(local) == len(subset)
            pl = {u: i for i, u in enumerate(local)}
            assert all((pl[u] < pl[v]) == (p[u] < p[v])
                       for u in subset for v in subset)
            for superset in all_subsets(range(n)):
                if subset <= superset:
                    enlarged = tuple(u for u in order if u in superset)
                    q = {u: i for i, u in enumerate(enlarged)}
                    assert all((pl[u] < pl[v]) == (q[u] < q[v])
                               for u in subset for v in subset)
        is_successor_first = all(
            p[y] < p[x] for part, closure in comps
            for x in part for y in closure-part)
        if is_successor_first:
            successor_count += 1
        good_local = True
        for part, closure in comps:
            lower = closure - part
            local = tuple(u for u in order if u in closure)
            pl = {u: i for i, u in enumerate(local)}
            if is_successor_first:
                assert all(pl[u] < pl[v] for u in lower for v in part)
                assert all(not (pl[z] < pl[v]) or z in lower
                           for v in lower for z in closure)
            good_local &= admissible_local(out, local, lower)
        global_candidate = legal_components(order, comps) and good_local
        independently = legal_components(order, comps) and legal_local_codes(out, order, comps)
        assert global_candidate == independently
        canonical_count += global_candidate
    return order_count, successor_count, canonical_count


def negative_controls():
    # A cycle and an unrelated isolated point: restriction to the
    # cycle is unchanged although its ambient positions are different.
    cycle_iso = (frozenset({1}), frozenset({2}), frozenset({0}), frozenset())
    a, b = (0, 3, 1, 2), (0, 1, 3, 2)
    assert tuple(x for x in a if x in {0, 1, 2}) == tuple(
        x for x in b if x in {0, 1, 2})
    assert a != b
    # The order (0,1) on an arrow 0 -> 1 is not successor-first.
    edge = (frozenset({1}), frozenset())
    assert not all((0,1).index(y) < (0,1).index(x)
                   for part, closure in components(edge)
                   for x in part for y in closure-part)


def main():
    negative_controls()
    total_o = total_orders = total_successor = total_canonical = 0
    for n in range(5):
        for out in orientations(n):
            count, succ, canonical = check(out)
            total_o += 1
            total_orders += count
            total_successor += succ
            total_canonical += canonical
    assert total_o == 653, total_o
    assert total_canonical == 1764, total_canonical
    print(f"PASS: {total_o} finite orientations, {total_orders} labelled orders, "
          f"{total_successor} successor-first orders, {total_canonical} "
          "globally canonical orders; restriction, inheritance, and "
          "negative controls")


if __name__ == "__main__":
    main()
