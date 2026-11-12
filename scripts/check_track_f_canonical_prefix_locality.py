#!/usr/bin/env python3
"""Exhaustive canonical prefix locality tests for actual SCC rankings.

For each legal SCC ranking, every component closure is contained in
its rank prefix. The complete inherited order and canonical-code
conditions through k depend only on component orders through k.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components, lex_code


def is_canonical_on_closure(out, order, block, closure):
    lower = closure - block
    inside = tuple(v for v in order if v in closure)
    old_positions = tuple((j,v) for j,v in enumerate(inside) if v in lower)
    fixed = (tuple(p) for p in permutations(inside)
             if all(p[j]==v for j,v in old_positions))
    return lex_code(out,inside)==min(lex_code(out,p) for p in fixed)


def check(out):
    cc=components(out)
    blocks=[b for b,_ in cc]
    per_block=[list(permutations(sorted(b))) for b in blocks]
    checked=0
    for ranking in permutations(range(len(cc))):
        pos={b:j for j,b in enumerate(ranking)}
        islegal=all(pos[lo]<pos[hi]
                    for hi,(top,cl) in enumerate(cc)
                    for lo,(low,_) in enumerate(cc)
                    if hi!=lo and low <= cl)
        if not islegal:
            continue
        for i,(b,cl) in enumerate(cc):
            assert all(pos[j]<=pos[i] for j,(b2,_) in enumerate(cc)
                       if b2 <= cl)
        for k in range(len(cc)):
            observation={}
            for choices in product(*per_block):
                assembled=tuple(v for j in ranking for v in choices[j])
                prefix_key=tuple((j,choices[j]) for j in ranking[:k+1])
                values=tuple(
                    (tuple(v for v in assembled if v in cl),
                     is_canonical_on_closure(out,assembled,b,cl))
                    for i,(b,cl) in enumerate(cc) if pos[i]<=k
                )
                if prefix_key in observation:
                    assert observation[prefix_key] == values
                else:
                    observation[prefix_key]=values
                checked+=1
    return checked


def negative_controls():
    # Legal rank must place successor sink 1 ahead of source 0.
    edge=(frozenset({1}),frozenset())
    cc=components(edge)
    source=next(i for i,(b,_) in enumerate(cc) if 0 in b)
    sink=next(i for i,(b,_) in enumerate(cc) if 1 in b)
    pos={source:0,sink:1}
    assert any(pos[j]>pos[source] for j,(b,_) in enumerate(cc)
               if b <= cc[source][1])
    # Keeping only the *strict* earlier prefix does not fix the
    # top-component canonical condition. The 3-cycle has six
    # internal orders, but only three attain its minimum code.
    tri=(frozenset({1}),frozenset({2}),frozenset({0}))
    top=frozenset({0,1,2})
    assert sum(is_canonical_on_closure(tri,p,top,top)
               for p in permutations(range(3)))==3


def main():
    negative_controls()
    structures=checks=0
    for n in range(5):
        for out in orientations(n):
            checks+=check(out)
            structures+=1
    assert structures==653 and checks>0
    print(f"PASS: {structures} orientations; {checks} checked "
          "canonical rank-prefix observations; illegal-ranking and "
          "strict-prefix negative controls")


if __name__=="__main__":
    main()
