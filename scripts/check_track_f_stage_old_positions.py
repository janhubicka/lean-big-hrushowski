#!/usr/bin/env python3
"""Independent exhaustive finite tests for actual old-position invariance.

Within a fixed legal SCC ranking, replacing one internal SCC order must
not change global comparisons outside that SCC. In its own induced
successor closure, its strict lower part must occupy exactly the same
absolute positions for every chosen internal top-component order.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components


def legal(cc, ranking):
    rank = {i:j for j,i in enumerate(ranking)}
    return all(rank[j] < rank[i]
               for i,(top,closure) in enumerate(cc)
               for j,(below,_) in enumerate(cc)
               if i != j and below <= closure)


def assemble(ranking, choices):
    return tuple(v for i in ranking for v in choices[i])


def check(out):
    cc=components(out)
    blocks=[top for top,_ in cc]
    per_block=[list(permutations(sorted(top))) for top in blocks]
    comparisons=old_position_checks=0
    for ranking in permutations(range(len(blocks))):
        if not legal(cc,ranking):
            continue
        for orders in product(*per_block):
            original=assemble(ranking,orders)
            pos0={x:j for j,x in enumerate(original)}
            for i,(top,closure) in enumerate(cc):
                lower=closure-top
                local0=tuple(x for x in original if x in closure)
                old0=tuple((j,x) for j,x in enumerate(local0) if x in lower)
                for new_order in per_block[i]:
                    updated=tuple(new_order if j==i else orders[j]
                                  for j in range(len(blocks)))
                    new=assemble(ranking,updated)
                    pos1={x:j for j,x in enumerate(new)}
                    assert all((pos0[u]<pos0[v]) == (pos1[u]<pos1[v])
                               for u in range(len(out)) if u not in top
                               for v in range(len(out)) if v not in top)
                    comparisons+=1
                    local1=tuple(x for x in new if x in closure)
                    old1=tuple((j,x) for j,x in enumerate(local1) if x in lower)
                    assert old0==old1, (out,ranking,orders,new_order,top,lower)
                    assert set(local1[:len(lower)])==lower
                    assert set(local0[:len(lower)])==lower
                    old_position_checks+=1
    return comparisons,old_position_checks


def negative_controls():
    # A legal global ranking may put unrelated components *before*
    # the lower set; initiality only holds inside the real closure.
    out=(frozenset({1}),frozenset(),frozenset())
    cc=components(out)
    i0=next(i for i,(B,_) in enumerate(cc) if B == {0})
    i1=next(i for i,(B,_) in enumerate(cc) if B == {1})
    i2=next(i for i,(B,_) in enumerate(cc) if B == {2})
    rank=(i2,i1,i0)
    assert legal(cc,rank)
    order=assemble(rank,[tuple(sorted(B)) for B,_ in cc])
    assert order == (2,1,0)
    lower=cc[i0][1]-cc[i0][0]
    assert lower=={1}
    assert set(order[:len(lower)])!=lower
    assert tuple(x for x in order if x in cc[i0][1])==(1,0)
    # Reversing the proper successor-first order is not legal and
    # can fail the local lower-part initiality assertion.
    assert not legal(cc,(i0,i1,i2))


def main():
    negative_controls()
    structures=comparisons=old_positions=0
    for n in range(5):
        for out in orientations(n):
            c,o=check(out)
            structures+=1
            comparisons+=c
            old_positions+=o
    assert structures==653 and old_positions>0
    print(f"PASS: {structures} orientations, {comparisons} outside-SCC "
          f"comparison controls, {old_positions} literal old-position "
          "checks; unrelated-earlier and illegal-ranking negatives")


if __name__=="__main__":
    main()
