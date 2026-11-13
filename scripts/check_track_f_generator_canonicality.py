#!/usr/bin/env python3
"""Canonical complete closure test is invariant within a genuine SCC.

For every orientation on <=4 vertices and all complete vertex orders,
compare the induced C_x and lower part P_x for vertices in the same
actual strongly connected component. Their exact canonical code
criterion must coincide. An edge distinguishes different SCCs.
"""
from itertools import permutations
from check_track_f_canonical_local import orientations, components, lex_code


def canonical(out, global_order, C, P):
    local=tuple(v for v in global_order if v in C)
    old_positions=tuple((i,v) for i,v in enumerate(local) if v in P)
    alternatives=(p for p in permutations(local)
                  if all(p[i]==v for i,v in old_positions))
    return lex_code(out,local)==min(lex_code(out,p) for p in alternatives)


def check(out):
    cc=components(out)
    membership={v:(B,C) for B,C in cc for v in B}
    tests=0
    for order in permutations(range(len(out))):
        for x in range(len(out)):
            B,C=membership[x]
            P=C-B
            expect=canonical(out,order,C,P)
            for y in B:
                B2,C2=membership[y]
                assert (B2,C2)==(B,C)
                assert canonical(out,order,C2,C2-B2)==expect
                tests+=1
    return tests


def negatives():
    edge=(frozenset({1}),frozenset())
    cc=components(edge)
    found={v:(B,C) for B,C in cc for v in B}
    assert found[0][1] != found[1][1]
    assert found[0][1]=={0,1} and found[1][1]=={1}


def main():
    negatives()
    structures=tests=0
    for n in range(5):
        for out in orientations(n):
            tests+=check(out)
            structures+=1
    assert structures==653 and tests>0
    print(f"PASS: {structures} orientations, {tests} generator checks, "
          "exact SCC closure and lower-part invariance; "
          "different-SCC negative control")


if __name__=="__main__":
    main()
