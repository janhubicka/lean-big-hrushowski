#!/usr/bin/env python3
"""Independent small finite test of the candidate global N0 order count.

Enumerate actual labelled vertex orders, require successor-first SCC
intervals, and test each induced C_B's minimum complete directed code
with its induced ordered lower part. Independently enumerate linear
extensions of the intrinsic SCC dependency order and local stabilizers.
Not a Lean theorem or an infinite Ramsey statement.
"""
from itertools import permutations

from check_track_f_canonical_local import (
    orientations, components, stabilizer_card, lex_code,
)


def legal_components(order, comps):
    place = {i: j for j, i in enumerate(order)}
    for part, _ in comps:
        p = [place[x] for x in part]
        if max(p) - min(p) + 1 != len(p):
            return False
    for top, closure in comps:
        for lower, _ in comps:
            if top != lower and lower <= closure:
                if max(place[y] for y in lower) >= min(place[x] for x in top):
                    return False
    return True


def legal_local_codes(out, order, comps):
    place = {i: j for j, i in enumerate(order)}
    for top, closure in comps:
        lower = closure - top
        restricted = tuple(sorted(closure, key=place.get))
        old_positions = tuple((i, x) for i, x in enumerate(restricted) if x in lower)
        possible = (p for p in permutations(sorted(closure))
                    if all(p[i] == x for i, x in old_positions))
        if lex_code(out, restricted) != min(lex_code(out, p) for p in possible):
            return False
    return True


def extension_count(comps):
    count = 0
    for rank in permutations(range(len(comps))):
        place = {i: j for j, i in enumerate(rank)}
        if all(place[j] < place[i]
               for i, (B, _) in enumerate(comps)
               for j, (C, _) in enumerate(comps)
               if i != j and C <= comps[i][1]):
            count += 1
    return count


def check(out):
    comps = components(out)
    ell = extension_count(comps)
    product_g = 1
    for B, closure in comps:
        product_g *= stabilizer_card(out, closure, closure - B)
    admitted = [order for order in permutations(range(len(out)))
                if legal_components(order, comps)
                and legal_local_codes(out, order, comps)]
    assert len(admitted) == ell * product_g, (out, admitted, ell, product_g)
    return len(admitted), ell, product_g


def main():
    total, admitted = 0, 0
    for n in range(5):
        for out in orientations(n):
            total += 1
            admitted += check(out)[0]
    # A vertex unrelated to the cycle cannot interleave its SCC interval.
    triangle_and_isolate = (
        frozenset({1}), frozenset({2}), frozenset({0}), frozenset()
    )
    comps = components(triangle_and_isolate)
    assert not legal_components((0, 3, 1, 2), comps)
    assert check(triangle_and_isolate) == (6, 2, 3)
    print(f"PASS: {total} orientations; {admitted} globally admissible "
          "canonical orders, matching component linear extensions "
          "times induced pointwise-local stabilizers")


if __name__ == "__main__":
    main()
