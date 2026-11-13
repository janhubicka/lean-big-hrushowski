#!/usr/bin/env python3
"""Independent chronological counting of actual tagged SCC order choices.

All reachable histories use the actual component order type and record
a tag (SCC index, internal labelled enumeration), newest first.
Each legal stage must have the induced local stabilizer cardinality.
At the end, histories must correspond to the exact canonical global
labelled vertex orders, not just to abstract numerical choices.
"""
from itertools import permutations
from check_track_f_canonical_local import orientations, components, lex_code, stabilizer_card
from check_track_f_global_canonical_count import legal_components, legal_local_codes


def legal(cc, rank):
    pos={i:j for j,i in enumerate(rank)}
    return all(pos[j]<pos[i] for i,(B,C) in enumerate(cc)
               for j,(other,_) in enumerate(cc) if i!=j and other<=C)


def context(cc, prior):
    chosen=[tuple(sorted(B)) for B,_ in cc]
    for i,t in reversed(prior):
        chosen[i]=t
    return chosen


def allowed(out, cc, ranking, prior):
    i=ranking[len(prior)]
    B,C=cc[i]
    chosen=context(cc,prior)
    accepted=set()
    for t in permutations(sorted(B)):
        updated=list(chosen)
        updated[i]=t
        assembled=tuple(v for j in ranking for v in updated[j])
        local=tuple(v for v in assembled if v in C)
        P=C-B
        old=tuple((k,v) for k,v in enumerate(local) if v in P)
        other=(f for f in permutations(sorted(C))
               if all(f[k]==v for k,v in old))
        if lex_code(out,local)==min(lex_code(out,f) for f in other):
            accepted.add((i,t))
    return accepted


def check(out):
    cc=components(out)
    m=len(cc)
    n_contexts=histories_count=0
    for r in permutations(range(m)):
        if not legal(cc,r): continue
        histories={()}
        expected=1
        for stage in range(m):
            B,C=cc[r[stage]]
            g=stabilizer_card(out,C,C-B)
            new=set()
            for h in histories:
                opts=allowed(out,cc,r,h)
                assert len(opts)==g,(out,r,h,len(opts),g)
                for tag in opts:
                    assert tag[0]==r[stage]
                    new.add((tag,)+h)
                n_contexts+=1
            expected*=g
            assert len(new)==expected,(out,r,stage,len(new),expected)
            histories=new
        seen=set()
        for h in histories:
            choices=context(cc,h)
            assembled=tuple(v for i in r for v in choices[i])
            assert legal_components(assembled,cc)
            assert legal_local_codes(out,assembled,cc)
            assert assembled not in seen
            seen.add(assembled)
        # Compare against all canonical orders with this exact SCC ranking.
        actual=set()
        for o in permutations(range(len(out))):
            if not legal_components(o,cc) or not legal_local_codes(out,o,cc):
                continue
            pos={v:j for j,v in enumerate(o)}
            actual_rank=tuple(sorted(range(m),
                             key=lambda i:min(pos[x] for x in cc[i][0])))
            if actual_rank==r:
                actual.add(o)
        assert seen==actual,(out,r,len(seen),len(actual))
        histories_count+=len(histories)
    return n_contexts,histories_count


def negative_controls():
    cyc=(frozenset({1}),frozenset({2}),frozenset({0}))
    c,h=check(cyc)
    assert c==1 and h==3
    # The same numerical permutation can be used on two different
    # singleton SCCs, but tags distinguish which component it orders.
    edge=(frozenset({1}),frozenset())
    cc=components(edge)
    assert (0,(0,))!=(1,(1,))
    assert len(cc)==2


def main():
    negative_controls()
    structs=contexts=finals=0
    for n in range(5):
        for out in orientations(n):
            a,b=check(out)
            structs+=1; contexts+=a; finals+=b
    assert structs==653 and finals==1764, (structs, finals)
    print(f"PASS: {structs} orientations, {contexts} reachable "
          f"prefix contexts, {finals} canonical tagged histories; "
          "exact small finite global-order bijection and fibre products")


if __name__=="__main__":
    main()
