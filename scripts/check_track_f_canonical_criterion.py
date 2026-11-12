#!/usr/bin/env python3
"""Independent elementary characterization of canonical local codes.

Checks e is in the minimum class iff e fixes all old positions and
its full directed adjacency code is at most every fixed-old code.
"""
from itertools import permutations
from check_track_f_canonical_local import orientations, components, lex_code


def check(out):
    tested = 0
    negative_old = 0
    negative_code = 0
    for part, closure in components(out):
        P = closure - part
        es = list(permutations(sorted(closure)))
        for base in es:
            old = {i: v for i, v in enumerate(base) if v in P}
            candidates = [e for e in es if all(e[i] == v for i, v in old.items())]
            assert candidates
            m = min(lex_code(out, e) for e in candidates)
            canonical = {e for e in candidates if lex_code(out, e) == m}
            for e in es:
                fixes_old = all(e[i] == v for i, v in old.items())
                criterion = fixes_old and all(
                    lex_code(out, e) <= lex_code(out, f) for f in candidates)
                assert (e in canonical) == criterion
                if not fixes_old:
                    negative_old += 1
                elif lex_code(out, e) > m:
                    negative_code += 1
                tested += 1
    return tested, negative_old, negative_code


def main():
    nstr, nt, no, nc = 0, 0, 0, 0
    for n in range(5):
        for out in orientations(n):
            tested, old, code = check(out)
            nstr += 1
            nt += tested
            no += old
            nc += code
    assert nstr == 653 and nt > 0 and no > 0 and nc > 0
    print(f"PASS: {nstr} orientations, {nt} base/target tests, "
          f"{no} old-position negatives and {nc} strict code negatives")


if __name__ == "__main__":
    main()
