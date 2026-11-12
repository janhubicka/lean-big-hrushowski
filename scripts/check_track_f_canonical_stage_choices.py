#!/usr/bin/env python3
"""Independent finite test of concrete one-component extension fibres.

Fix a legal SCC ranking and all component orders except the one at B.
Vary the labelled internal order of B, requiring its complete induced
C_B adjacency code to be the least code with the old positions fixed.
The observed number of permitted next choices must equal g_A(B).
This is finite evidence, not the missing Lean uniformity proof.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components, lex_code, stabilizer_card


def test(out):
    cc=components(out)
    blocks=[b for b,_ in cc]
    options=[tuple(permutations(sorted(b))) for b in blocks]
    stages=extensions=0
    for ranking in permutations(range(len(cc))):
        pos={i:j for j,i in enumerate(ranking)}
        legal=all(pos[lo]<pos[hi]
                  for hi,(top,cl) in enumerate(cc)
                  for lo,(low,_) in enumerate(cc)
                  if hi!=lo and low <= cl)
        if not legal:
            continue
        for base in product(*options):
            for i,(B,C) in enumerate(cc):
                P=C-B
                factor=stabilizer_card(out,C,P)
                possible=set()
                for choice in options[i]:
                    updated=tuple(choice if j==i else base[j]
                                  for j in range(len(cc)))
                    assert all(updated[j]==base[j] for j in range(len(cc)) if j!=i)
                    assembled=tuple(v for j in ranking for v in updated[j])
                    local=tuple(v for v in assembled if v in C)
                    # Compare every full directed adjacency matrix entry.
                    fixed_old=tuple((k,u) for k,u in enumerate(local) if u in P)
                    alternatives=(p for p in permutations(local)
                                  if all(p[k]==u for k,u in fixed_old))
                    minimum=min(lex_code(out,p) for p in alternatives)
                    if lex_code(out,local)==minimum:
                        possible.add(choice)
                assert len(possible)==factor, (out, ranking, B, C, base, possible, factor)
                stages += 1
                extensions += len(possible)
    return stages,extensions


def negative_controls():
    tri=(frozenset({1}),frozenset({2}),frozenset({0}))
    stages,extensions=test(tri)
    assert stages==6 and extensions==18
    # The full internal permutation space has 6 orders, whereas the
    # local canonical fibre has only the three cycle automorphisms.
    assert stabilizer_card(tri, frozenset(range(3)),frozenset())==3


def main():
    negative_controls()
    structures=stages=extensions=0
    for n in range(5):
        for out in orientations(n):
            a,b=test(out)
            structures+=1
            stages+=a
            extensions+=b
    assert structures==653
    print(f"PASS: {structures} orientations, {stages} legal-rank "
          f"fixed-context component stages, {extensions} permitted "
          "updated labelled assignments; exact local stabilizer "
          "fibre sizes and triangle negative control")


if __name__=="__main__":
    main()
