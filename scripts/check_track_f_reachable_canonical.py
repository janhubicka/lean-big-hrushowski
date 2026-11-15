#!/usr/bin/env python3
"""Independent finite check that every reachable rank prefix is canonical.

The history is reverse chronological and all unchosen SCCs have fixed
default orders. Every prior canonical test must persist after updates
to later SCCs, including for unrelated earlier components.
"""
from itertools import permutations
from check_track_f_canonical_local import orientations, components, lex_code


def legal(cc, rank):
    pos={B:i for i,B in enumerate(rank)}
    return all(pos[j]<pos[i] for i,(top,C) in enumerate(cc)
               for j,(lower,_) in enumerate(cc)
               if i!=j and lower<=C)


def canon(out, assembled, B, C):
    local=tuple(v for v in assembled if v in C)
    P=C-B
    old=tuple((i,v) for i,v in enumerate(local) if v in P)
    return lex_code(out,local)==min(
        lex_code(out,t) for t in permutations(local)
        if all(t[i]==v for i,v in old))


def check(out):
    cc=components(out)
    options=[list(permutations(sorted(B))) for B,_ in cc]
    defaults=tuple(opts[0] for opts in options)
    prefixes=checks=0
    for rank in permutations(range(len(cc))):
        if not legal(cc,rank): continue
        states={defaults}
        for n in range(len(cc)+1):
            for state in states:
                assembled=tuple(v for i in rank for v in state[i])
                for i in rank[:n]:
                    B,C=cc[i]
                    assert canon(out,assembled,B,C)
                    checks+=1
                prefixes+=1
            if n==len(cc): break
            i=rank[n]
            B,C=cc[i]
            next_states=set()
            for state in states:
                for t in options[i]:
                    updated=tuple(t if j==i else state[j]
                                  for j in range(len(cc)))
                    assembled=tuple(v for j in rank for v in updated[j])
                    if canon(out,assembled,B,C):
                        next_states.add(updated)
            states=next_states
    return prefixes,checks


def main():
    structures=prefixes=checks=0
    for n in range(5):
        for out in orientations(n):
            a,b=check(out)
            prefixes+=a;checks+=b;structures+=1
    assert structures==653 and checks>0
    print(f"PASS: {structures} orientations, {prefixes} reachable "
          f"prefix assignments, {checks} persistent canonicality tests")


if __name__=="__main__":
    main()
