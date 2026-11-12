#!/usr/bin/env python3
"""Check that actual canonical local fibres give distinct top SCC orders.

Only bases that put the actual lower successor part first are required.
Tests include an interleaving counterexample when *positions* of the
old part are not fixed (matching only relative orders is insufficient).
"""
from itertools import permutations
from check_track_f_canonical_local import orientations, components, lex_code, stabilizer_card


def test(out):
    classes = comparisons = 0
    for B, closure in components(out):
        P = closure - B
        top = B
        for base in permutations(sorted(closure)):
            # Only lower-initial bases occur for genuine global
            # successor-first ordered component closures.
            if set(base[:len(P)]) != P:
                continue
            fixed = [e for e in permutations(sorted(closure))
                     if all(e[i] == base[i] for i in range(len(P)))]
            assert fixed
            minimum = min(lex_code(out, e) for e in fixed)
            canonical = [e for e in fixed if lex_code(out,e) == minimum]
            top_orders = [tuple(u for u in e if u in top) for e in canonical]
            assert len(top_orders) == len(set(top_orders)), (out,B,base,top_orders)
            factor = stabilizer_card(out,closure,P)
            assert len(canonical) == len(top_orders) == factor
            classes += 1
            comparisons += len(canonical)
    return classes, comparisons


def negative_controls():
    # Relative old order alone does not fix old *positions*:
    # both e and f order the top as 1<2, but their full orders differ.
    P={0}
    e=(0,1,2)
    f=(1,0,2)
    assert tuple(u for u in e if u not in P) == tuple(u for u in f if u not in P)
    assert e != f
    assert {i for i,u in enumerate(e) if u in P} != {
        i for i,u in enumerate(f) if u in P}
    # There is no such collision if old positions are literally fixed:
    all_e=list(permutations(range(3)))
    for base in all_e:
        for a in all_e:
            for b in all_e:
                if (tuple((i,u) for i,u in enumerate(a) if u in P) ==
                    tuple((i,u) for i,u in enumerate(base) if u in P) ==
                    tuple((i,u) for i,u in enumerate(b) if u in P)):
                    if tuple(u for u in a if u not in P) == tuple(
                            u for u in b if u not in P):
                        assert a == b


def main():
    negative_controls()
    ns = bases = choices = 0
    for n in range(5):
        for out in orientations(n):
            a,b = test(out)
            ns += 1
            bases += a
            choices += b
    assert ns == 653 and bases > 0 and choices > 0
    print(f"PASS: {ns} orientations, {bases} lower-initial bases, "
          f"{choices} canonical top choices, exact local stabilizers, "
          "old-position negative controls")


if __name__ == "__main__":
    main()
