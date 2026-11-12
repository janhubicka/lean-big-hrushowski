#!/usr/bin/env python3
"""Adversarial graph/C/J equivariance across unrelated raw C0 code vertices.

This does not merely test a single original graph: it checks raw host
pairs assembled from DISTINCT finite presentations, including codes
with equal distinguished coordinates and incompatible full matrices.
An increasing map must preserve/refect the complete raw E/C/J language.
"""
from itertools import product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)


def code(edges, C, support, root, labels):
    return (
        frozenset(labels[u] for u in support),
        labels[root],
        frozenset((labels[u],labels[v]) for u in support for v in support
                  if u != v and tuple(sorted((u,v))) in edges),
        frozenset((labels[u],labels[v]) for u in support for v in C[u]
                  if v in support),
    )


def child(q,x):
    S, _, E, C = q
    assert x in S
    T = frozenset(y for y in S if (x,y) in C)
    assert x in T
    return (T,x,frozenset((u,v) for u,v in E if u in T and v in T),
            frozenset((u,v) for u,v in C if u in T and v in T))


def closed(q):
    return frozenset(child(q,x) for x in q[0])


def back(q):
    return frozenset(r for r in closed(q) if (q[1],r[1]) in q[2])


def adj(q,r):
    return ((r in closed(q) and (q[1],r[1]) in q[2]) or
            (q in closed(r) and (q[1],r[1]) in r[2]))


def relabel(q,h):
    S,p,E,C=q
    return (frozenset(h(x) for x in S),h(p),
            frozenset((h(x),h(y)) for x,y in E),
            frozenset((h(x),h(y)) for x,y in C))


def sample():
    candidates=set()
    presentations=0
    for n in range(1,5):
        for edges in graphs(n):
            for levels in range(1,n+1):
                for kappa in product(range(levels), repeat=n):
                    if set(kappa)!=set(range(levels)):
                        continue
                    stages=[frozenset(v for v in range(n) if kappa[v]<i)
                            for i in range(levels+1)]
                    if not all(finite_minimal_step(stages[i],stages[i+1],edges)
                               for i in range(levels)):
                        continue
                    presentations+=1
                    # The witness is a CHRONOLOGICAL order, not an
                    # arbitrary labelling of its component stages.
                    ordered=sorted(range(n),key=lambda u:(kappa[u],u))
                    rank={v:i for i,v in enumerate(ordered)}
                    E={tuple(sorted((rank[u],rank[v]))) for u,v in edges}
                    C0=finite_component_values(kappa,edges)
                    C=[frozenset(rank[v] for v in C0[ordered[i]])
                       for i in range(n)]
                    for gap in (2,7):
                        labels={u:gap*(u+1) for u in range(n)}
                        for u in range(n):
                            candidates.add(code(E,C,C[u],u,labels))
    return candidates,presentations


def main():
    pool,presentations=sample()
    # Deterministic representative sample from all sizes and graph
    # types; ensure a mix of same-coordinate non-isomorphic codes.
    codes=sorted(pool,key=lambda q:(len(q[0]),q[1],tuple(sorted(q[2])),
                                   tuple(sorted(q[3])),tuple(sorted(q[0]))))
    stride=max(1,len(codes)//260)
    codes=codes[::stride][:300]
    maps=(lambda x:2*x+5,lambda x:3*x+1)
    assert len(codes)>=80
    collisions=0
    for i,q in enumerate(codes):
        for r in codes[i+1:]:
            if q[1]==r[1]:
                assert q!=r
                collisions+=1
    assert collisions>0
    pairs=0
    for h in maps:
        relabelled=[relabel(q,h) for q in codes]
        assert len(set(relabelled))==len(codes)
        for q,qh in zip(codes,relabelled):
            assert closed(qh)==frozenset(relabel(r,h) for r in closed(q))
            assert back(qh)==frozenset(relabel(r,h) for r in back(q))
            assert qh[1]==h(q[1])
            for r,rh in zip(codes,relabelled):
                assert (rh in closed(qh))==(r in closed(q))
                assert (rh in back(qh))==(r in back(q))
                assert adj(qh,rh)==adj(q,r)
                pairs+=1
    comp=lambda x:maps[1](maps[0](x))
    assert all(relabel(relabel(q,maps[0]),maps[1])==relabel(q,comp)
               for q in codes)
    # Noninjective map collapses a genuine 2-vertex edge to a loop
    # in its incidence matrix: such maps cannot act on the host.
    edge=next(q for q in pool if len(q[0])==2 and q[2])
    collapsed=relabel(edge,lambda _x:0)
    assert (0,0) in collapsed[2]
    print(f"PASS raw-host complete E/C/J action: {presentations} "
          f"minimal-strong presentations, {len(pool)} distinct finite "
          f"codes, {len(codes)} sampled host vertices, {pairs} ordered "
          f"cross-presentation pairs, {collisions} same-point collisions; "
          "complete unary values, graph and J, composition, "
          "noninjective negative control")


if __name__=="__main__":
    main()
