#!/usr/bin/env python3
"""Every complete C_B enumeration with fixed old positions is an SCC update.

For every finite orientation (up to four vertices), every legal actual
SCC ranking and every complete internal SCC assignment, compare:
  1. all permutations of C_B fixing the positions occupied by P_B;
  2. restrictions of global orders obtained by changing only B.
The sets must be literally equal; the map must be injective.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components


def legal(cc, ranking):
    rank={i:j for j,i in enumerate(ranking)}
    return all(rank[j]<rank[i]
               for i,(top,cl) in enumerate(cc)
               for j,(other,_) in enumerate(cc)
               if i!=j and other<=cl)


def check(out):
    cc=components(out)
    parts=[top for top,_ in cc]
    perpart=[list(permutations(sorted(part))) for part in parts]
    contexts=images=0
    for ranking in permutations(range(len(cc))):
        if not legal(cc,ranking):
            continue
        for orders in product(*perpart):
            global_base=tuple(v for j in ranking for v in orders[j])
            for i,(B,C) in enumerate(cc):
                P=C-B
                base=tuple(v for v in global_base if v in C)
                old_key=tuple((j,v) for j,v in enumerate(base) if v in P)
                fixed={tuple(p) for p in permutations(sorted(C))
                       if all(p[j]==v for j,v in old_key)}
                observed={}
                for t in perpart[i]:
                    changed=tuple(t if j==i else orders[j]
                                  for j in range(len(cc)))
                    assembled=tuple(v for j in ranking for v in changed[j])
                    local=tuple(v for v in assembled if v in C)
                    assert tuple(v for v in local if v in B)==t
                    assert tuple((j,v) for j,v in enumerate(local) if v in P)==old_key
                    assert local not in observed, (out,ranking,orders,i,t,local)
                    observed[local]=t
                    images+=1
                assert set(observed)==fixed, (out,ranking,orders,i,observed,fixed)
                for f in fixed:
                    t=tuple(v for v in f if v in B)
                    assert observed[f]==t
                contexts+=1
    return contexts,images


def negative_controls():
    # A 3-cycle plus an unrelated vertex. Even if the unrelated
    # component is listed first, it cannot enter the C_B fibre.
    tri_iso=(frozenset({1}),frozenset({2}),frozenset({0}),frozenset())
    cc=components(tri_iso)
    cyc=next((B,C) for B,C in cc if B=={0,1,2})
    B,C=cyc
    assert C==B
    assert tuple(x for x in (3,0,1,2) if x in C)==(0,1,2)
    # Without fixing old positions, an interleaving can have the
    # same top order but a different full closure enumeration.
    e=(0,1,2)
    f=(1,0,2)
    P={0}
    assert tuple(x for x in e if x not in P)==tuple(
        x for x in f if x not in P)
    assert e!=f and e.index(0)!=f.index(0)


def main():
    negative_controls()
    structures=contexts=images=0
    for n in range(5):
        for out in orientations(n):
            c,i=check(out)
            structures+=1
            contexts+=c
            images+=i
    assert structures==653 and images>0
    print(f"PASS: {structures} orientations, {contexts} legal fixed-old "
          f"contexts, {images} exact local-bijection witnesses; "
          "no omitted or duplicate closure enumerations")


if __name__=="__main__":
    main()
