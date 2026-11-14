#!/usr/bin/env python3
"""Independent finite check: every canonical assignment has a reachable history.

For every orientation up to four vertices, each legal SCC ranking and
each complete family of internal SCC orders, select the canonical
assignments. Read their SCC choices in rank order, start with fixed
default orders, and prove every next choice passes the genuine
complete-closure test before the next update is made.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components, lex_code


def legal(cc,r):
    pos={i:j for j,i in enumerate(r)}
    return all(pos[j]<pos[i] for i,(_,cl) in enumerate(cc)
               for j,(other,_) in enumerate(cc)
               if i!=j and other<=cl)


def is_canon(out,state,rank,cc,i):
    B,C=cc[i]; P=C-B
    order=tuple(v for j in rank for v in state[j])
    loc=tuple(v for v in order if v in C)
    old=tuple((k,v) for k,v in enumerate(loc) if v in P)
    return lex_code(out,loc)==min(
        lex_code(out,t) for t in permutations(loc)
        if all(t[k]==v for k,v in old))


def main():
    structs=orders=prefix_checks=0
    for n in range(5):
        for out in orientations(n):
            cc=components(out)
            options=[tuple(permutations(sorted(B))) for B,_ in cc]
            default=[opts[0] for opts in options]
            for rank in permutations(range(len(cc))):
                if not legal(cc,rank): continue
                for full in product(*options):
                    if not all(is_canon(out,full,rank,cc,i)
                               for i in range(len(cc))): continue
                    partial=list(default)
                    for i in rank:
                        partial[i]=full[i]
                        assert is_canon(out,partial,rank,cc,i)
                        prefix_checks+=1
                    assert tuple(partial)==full
                    orders+=1
            structs+=1
    assert structs==653 and orders==1764
    print(f"PASS: {structs} orientations, {orders} canonical "
          f"assignments with reachable rank histories, {prefix_checks} "
          "accepted chronological stage choices")


if __name__=="__main__":
    main()
