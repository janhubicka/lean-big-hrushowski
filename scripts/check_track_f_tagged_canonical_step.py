#!/usr/bin/env python3
"""Adversarial finite test: later SCC updates preserve earlier canonicality.

Check all oriented digraphs of order <=4, all legal SCC rankings, all
component-order contexts, and all alternative orders of later SCCs.
Canonicality is the full directed adjacency-code minimum on the
actual complete closure of each earlier component.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components, lex_code


def legal(cc, r):
    rank = {i: j for j,i in enumerate(r)}
    return all(rank[j] < rank[i] for i,(B,C) in enumerate(cc)
               for j,(below,_) in enumerate(cc)
               if j != i and below <= C)


def canonical(out, order, B, C):
    P = C - B
    local = tuple(v for v in order if v in C)
    old = tuple((i,v) for i,v in enumerate(local) if v in P)
    minimum = min(lex_code(out, t) for t in permutations(local)
                  if all(t[i] == v for i,v in old))
    return lex_code(out, local) == minimum


def main():
    structures = tests = 0
    for n in range(5):
        for out in orientations(n):
            cc = components(out)
            opts = [tuple(permutations(sorted(B))) for B,C in cc]
            for rank in permutations(range(len(cc))):
                if not legal(cc, rank):
                    continue
                pos = {B:i for i,B in enumerate(rank)}
                for choices in product(*opts):
                    order = tuple(v for i in rank for v in choices[i])
                    for j,(later,_) in enumerate(cc):
                        for t in opts[j]:
                            updated = tuple(t if k==j else choices[k]
                                            for k in range(len(cc)))
                            other = tuple(v for k in rank for v in updated[k])
                            for i,(B,C) in enumerate(cc):
                                if pos[i] < pos[j]:
                                    assert canonical(out,order,B,C) == canonical(
                                        out,other,B,C)
                                    tests += 1
            structures += 1
    assert structures == 653 and tests > 0
    print(f"PASS: {structures} orientations; {tests} later-update "
          "canonicality comparisons on actual earlier SCC closures")


if __name__ == "__main__":
    main()
