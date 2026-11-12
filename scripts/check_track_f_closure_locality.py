#!/usr/bin/env python3
"""Exhaustively verify that SCC orders outside C_B are irrelevant.

The SCC ranking is held fixed; the internal enumeration of components
inside C_B is fixed; orders outside it may vary. Compare the *entire*
induced enumeration and its minimum complete-code eligibility.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components, lex_code


def is_canonical(out, local, lower):
    possible = [
        q for q in permutations(local)
        if all(q[i] == v for i, v in enumerate(local) if v in lower)
    ]
    return lex_code(out, local) == min(lex_code(out, q) for q in possible)


def check(out):
    cc = components(out)
    blocks = [part for part, _ in cc]
    choices = [list(permutations(sorted(block))) for block in blocks]
    checked = differences = 0
    for ranking in permutations(range(len(cc))):
        observations = [dict() for _ in cc]
        for order_tuple in product(*choices):
            ambient = tuple(v for i in ranking for v in order_tuple[i])
            for i, (part, closure) in enumerate(cc):
                inside = tuple(j for j, (other, _) in enumerate(cc)
                               if other <= closure)
                assert set(closure) == set().union(*(blocks[j] for j in inside))
                key = tuple((j, order_tuple[j]) for j in inside)
                induced = tuple(v for v in ambient if v in closure)
                lower = closure - part
                value = (induced, is_canonical(out, induced, lower))
                if key in observations[i]:
                    previous = observations[i][key]
                    assert value == previous, (out, ranking, i, key, value, previous)
                    differences += 1
                else:
                    observations[i][key] = value
                checked += 1
    return checked, differences


def negative_controls():
    # Nontrivial SCC on 0,1,2 with isolated vertex 3:
    # changing only cycle order must not change the closure-order
    # of singleton {3} (even if that cycle is listed earlier).
    O = (frozenset({1}), frozenset({2}), frozenset({0}), frozenset())
    cc = components(O)
    assert len(cc) == 2
    singleton = next(i for i,(block,_) in enumerate(cc) if block == {3})
    cycle = next(i for i,(block,_) in enumerate(cc) if block == {0,1,2})
    assert cc[singleton][1] == {3}
    for t in permutations((0,1,2)):
        assembled = t + (3,)
        assert tuple(v for v in assembled if v in cc[singleton][1]) == (3,)
    # But changing order INSIDE the cycle can affect its induced code/order.
    assert (0,1,2) != (0,2,1)


def main():
    negative_controls()
    structs = checked = repeated = 0
    for n in range(5):
        for out in orientations(n):
            a,b = check(out)
            structs += 1
            checked += a
            repeated += b
    assert structs == 653 and repeated > 0
    print(f"PASS: {structs} orientations, {checked} closure checks, "
          f"{repeated} independent-order coincidences, complete-code controls")


if __name__ == "__main__":
    main()
