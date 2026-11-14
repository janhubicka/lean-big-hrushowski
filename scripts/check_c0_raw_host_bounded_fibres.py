#!/usr/bin/env python3
"""Adversarial finite test of bounded complete raw C0 coordinate fibres.

The bounded host retains complete graph/C matrices, not just pointed
coordinates or unpointed local types. All generated child supports
must remain below the original whole-support bound.
"""
from itertools import product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)
from check_c0_raw_host_graph import make_code, closure


def sample():
    codes=set()
    presentations=0
    for n in range(1,5):
        for edges in graphs(n):
            for levels in range(1,n+1):
                for κ in product(range(levels),repeat=n):
                    if set(κ)!=set(range(levels)):
                        continue
                    cuts=[frozenset(u for u in range(n) if κ[u]<j)
                          for j in range(levels+1)]
                    if not all(finite_minimal_step(cuts[j],cuts[j+1],edges)
                               for j in range(levels)):
                        continue
                    presentations+=1
                    # Re-enumerate by chronological component order;
                    # only increasing coordinate embeddings are allowed.
                    old=sorted(range(n),key=lambda u:(κ[u],u))
                    idx={u:i for i,u in enumerate(old)}
                    E={tuple(sorted((idx[u],idx[v]))) for u,v in edges}
                    Cv=finite_component_values(κ,edges)
                    C=[frozenset(idx[v] for v in Cv[old[i]]) for i in range(n)]
                    for gap,offset in ((2,0),(3,1),(7,2)):
                        e={u:gap*(u+1)+offset for u in range(n)}
                        for a in range(n):
                            codes.add(make_code(E,C,C[a],a,e))
    return codes,presentations


def main():
    codes,presentations=sample()
    assert presentations==1401
    comparisons=0
    for q in codes:
        support,point,E,C=q
        assert point in support
        assert E<={(x,y) for x in support for y in support}
        assert C<={(x,y) for x in support for y in support}
        for r in closure(q):
            assert r[0]<=support
            comparisons+=1
    for N in (0,1,3,5,9,17,31):
        bounded=[q for q in codes if all(x<N for x in q[0])]
        assert all(q[1]<N for q in bounded)
        union=set().union(*(closure(q) for q in bounded[:15]))
        assert all(all(x<N for x in r[0]) for r in union)
    # The pointed coordinate is not a full code key:
    # distinct full source incidence systems may share a root.
    seen={}
    collisions=0
    for q in codes:
        x=q[1]
        if x in seen and seen[x]!=q:
            collisions+=1
        seen[x]=q
    assert collisions>0
    print(f"PASS raw C0 bounded fibres: {presentations} finite "
          f"minimal-strong presentations, {len(codes)} distinct actual "
          f"pointed codes, {comparisons} child-support comparisons, "
          f"{collisions} same-coordinate collisions, 7 coordinate "
          "bounds and finite-family hull checks")


if __name__=="__main__":
    main()
