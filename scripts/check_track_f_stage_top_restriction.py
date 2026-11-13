#!/usr/bin/env python3
"""Independent tests: top SCC order is exactly recovered from C_B.

All SCC rankings and labelled internal component orders are tested
on all finite orientations of order <= 4. Replacing B and restricting
the assembled global enumeration to C_B, then to B, must recover the
chosen *labelled* B order. Distinct choices must remain distinct on C_B.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components


def test(out):
    cc=components(out)
    blocks=[top for top,_ in cc]
    per_block=[list(permutations(sorted(top))) for top in blocks]
    reconstructions=injective=0
    for ranking in permutations(range(len(blocks))):
        for orders in product(*per_block):
            for i,(B,C) in enumerate(cc):
                observed={}
                for choice in per_block[i]:
                    updated=tuple(choice if j==i else orders[j]
                                  for j in range(len(blocks)))
                    full=tuple(v for j in ranking for v in updated[j])
                    local=tuple(v for v in full if v in C)
                    top=tuple(v for v in local if v in B)
                    assert top==choice, (out,ranking,orders,i,choice,top)
                    assert local not in observed, (out,ranking,i,choice,local)
                    observed[local]=choice
                    reconstructions+=1
                injective+=len(observed)
    return reconstructions,injective


def negatives():
    # A cycle plus unrelated isolate can have different ambient
    # positions yet exactly the same restriction to the top SCC.
    O=(frozenset({1}),frozenset({2}),frozenset({0}),frozenset())
    a,b=(0,3,1,2),(0,1,3,2)
    B={0,1,2}
    assert a!=b
    assert tuple(x for x in a if x in B)==tuple(x for x in b if x in B)
    # A cyclic top component has genuinely different internal orders.
    assert (0,1,2)!=(0,2,1)


def main():
    negatives()
    structures=total=recovered=0
    for n in range(5):
        for out in orientations(n):
            a,b=test(out)
            structures+=1
            total+=a
            recovered+=b
    assert structures==653 and total==recovered and total>0
    print(f"PASS: {structures} orientations, {total} labelled top "
          "order reconstructions; every fixed-context top-order map "
          "injective, including illegal component rankings")


if __name__=="__main__":
    main()
