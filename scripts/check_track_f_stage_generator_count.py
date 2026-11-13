#!/usr/bin/env python3
"""Independent exhaustive finite generator-canonical next-choice counts.

Check that the image of all permitted new top-B orders is *exactly*
the minimum full directed-matrix code class on C_B with old positions
fixed, for every legal SCC ranking and every full context. Cardinal
must be the induced pointwise stabilizer order g_A(B).
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components, lex_code, stabilizer_card


def legal(cc,ranking):
    p={i:j for j,i in enumerate(ranking)}
    return all(p[j]<p[i] for i,(B,C) in enumerate(cc)
               for j,(other,_) in enumerate(cc) if j!=i and other<=C)


def check(out):
    cc=components(out)
    blocks=[B for B,_ in cc]
    options=[list(permutations(sorted(B))) for B in blocks]
    contexts=choices_count=0
    for ranking in permutations(range(len(cc))):
        if not legal(cc,ranking): continue
        for chosen in product(*options):
            global_base=tuple(v for i in ranking for v in chosen[i])
            for i,(B,C) in enumerate(cc):
                P=C-B
                base=tuple(v for v in global_base if v in C)
                key=tuple((j,v) for j,v in enumerate(base) if v in P)
                fixed=[f for f in permutations(sorted(C))
                       if all(f[j]==v for j,v in key)]
                least=min(lex_code(out,f) for f in fixed)
                minimum_class={f for f in fixed if lex_code(out,f)==least}
                image={}
                for t in options[i]:
                    updated=tuple(t if j==i else chosen[j]
                                  for j in range(len(cc)))
                    assembled=tuple(v for j in ranking for v in updated[j])
                    e=tuple(v for v in assembled if v in C)
                    assert e in fixed
                    if lex_code(out,e)==least:
                        assert e not in image
                        image[e]=t
                assert set(image)==minimum_class, (out,ranking,chosen,i,image,minimum_class)
                g=stabilizer_card(out,C,P)
                assert len(image)==len(minimum_class)==g
                contexts+=1
                choices_count+=len(image)
    return contexts,choices_count


def negatives():
    # A directed triangle has six possible top orders but only
    # three in the minimum-code class. All six remain distinct.
    tri=(frozenset({1}),frozenset({2}),frozenset({0}))
    ctx,n=check(tri)
    assert ctx==6 and n==18
    assert len(list(permutations(range(3))))==6
    assert stabilizer_card(tri, frozenset(range(3)),frozenset())==3


def main():
    negatives()
    structures=contexts=choices=0
    for n in range(5):
        for o in orientations(n):
            a,b=check(o)
            structures+=1
            contexts+=a
            choices+=b
    assert structures==653 and contexts>0
    print(f"PASS: {structures} orientations, {contexts} legal fixed contexts, "
          f"{choices} canonical generator choices; exact image equality "
          "and stabilizer cardinalities in every context")


if __name__=="__main__":
    main()
