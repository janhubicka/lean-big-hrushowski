#!/usr/bin/env python3
"""Finite audit of inverse histories on reachable canonical SCC assignments.

A complete reachable tagged history is uniquely determined by the
orders of SCCs in ranking order. After executing it, reading those
actual labelled SCC orders again must reproduce every original tag.
"""
from itertools import permutations
from check_track_f_canonical_local import orientations, components, lex_code


def legal(cc,r):
    pos={i:j for j,i in enumerate(r)}
    return all(pos[j]<pos[i] for i,(_,C) in enumerate(cc)
               for j,(B,_) in enumerate(cc) if j!=i and B<=C)


def canonical(out,rank,assignment,i,cc):
    B,C=cc[i]; P=C-B
    global_order=tuple(v for j in rank for v in assignment[j])
    loc=tuple(v for v in global_order if v in C)
    old=tuple((k,u) for k,u in enumerate(loc) if u in P)
    return lex_code(out,loc)==min(
        lex_code(out,t) for t in permutations(loc)
        if all(t[k]==u for k,u in old))


def test(out):
    cc=components(out)
    options=[tuple(permutations(sorted(B))) for B,_ in cc]
    defaults=tuple(o[0] for o in options)
    counted=prefixes=0
    for rank in permutations(range(len(cc))):
        if not legal(cc,rank): continue
        reachable={((),defaults)}
        for n,i in enumerate(rank):
            new=set()
            for (rev,old) in reachable:
                for choice in options[i]:
                    updated=tuple(choice if j==i else old[j]
                                  for j in range(len(cc)))
                    if canonical(out,rank,updated,i,cc):
                        hist=((i,choice),)+rev
                        assert tuple(hist)==tuple((j,updated[j])
                                                 for j in reversed(rank[:n+1]))
                        # Components from earlier steps are unchanged.
                        for j in rank[:n]:
                            assert updated[j]==old[j]
                        new.add((hist,updated))
                        prefixes+=1
            reachable=new
            assert len({x[1] for x in reachable})==len(reachable)
        for hist,state in reachable:
            assert tuple((i,state[i]) for i in reversed(rank))==hist
            counted+=1
    return counted,prefixes


def main():
    structures=complete=steps=0
    for n in range(5):
        for out in orientations(n):
            a,b=test(out)
            complete+=a;steps+=b;structures+=1
    assert structures==653 and complete==1764
    print(f"PASS: {structures} orientations; {complete} complete "
          f"invertible tagged histories, {steps} canonical prefix "
          "updates with no assignments collisions")


if __name__=="__main__": main()
