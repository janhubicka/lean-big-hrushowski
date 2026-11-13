#!/usr/bin/env python3
"""Independent finite check: generator and all-generator next choices agree.

For every small finite orientation, legal component ranking and full
SCC-order context, changing only B to a candidate order must pass
canonicality at the chosen generator iff it passes at every vertex
of that actual SCC. Cardinalities agree with the induced stabilizer.
"""
from itertools import permutations,product
from check_track_f_canonical_local import orientations, components, lex_code, stabilizer_card, reach


def canonical(out,order,x):
    C=reach(out,x)
    B=next(B for B,_ in components(out) if x in B)
    P=C-B
    local=tuple(v for v in order if v in C)
    old=tuple((i,u) for i,u in enumerate(local) if u in P)
    fixed=(p for p in permutations(local)
           if all(p[i]==u for i,u in old))
    return lex_code(out,local)==min(lex_code(out,p) for p in fixed)


def legal(cc,ranking):
    pos={i:j for j,i in enumerate(ranking)}
    return all(pos[j]<pos[i] for i,(B,C) in enumerate(cc)
               for j,(other,_) in enumerate(cc) if j!=i and other<=C)


def check(out):
    cc=components(out)
    opts=[list(permutations(sorted(B))) for B,_ in cc]
    contexts=values=0
    for ranking in permutations(range(len(cc))):
        if not legal(cc,ranking): continue
        for base in product(*opts):
            for i,(B,C) in enumerate(cc):
                generator=min(B)
                accepted=0
                for t in opts[i]:
                    updated=tuple(t if j==i else base[j]
                                  for j in range(len(cc)))
                    global_order=tuple(v for j in ranking for v in updated[j])
                    atgen=canonical(out,global_order,generator)
                    allgen=all(canonical(out,global_order,x) for x in B)
                    assert atgen==allgen
                    accepted+=atgen
                    values+=1
                assert accepted==stabilizer_card(out,C,C-B)
                contexts+=1
    return contexts,values


def main():
    contexts=values=structs=0
    for n in range(5):
        for out in orientations(n):
            a,b=check(out)
            contexts+=a
            values+=b
            structs+=1
    assert structs==653
    print(f"PASS: {structs} orientations, {contexts} legal SCC "
          f"contexts, {values} all-generator equivalence tests; "
          "actual next-fibre counts equal induced stabilizers")


if __name__=="__main__":
    main()
