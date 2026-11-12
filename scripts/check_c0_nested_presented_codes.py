#!/usr/bin/env python3
"""Independent finite regression: a C(b)-code is restriction of C(a)-code.

Enumerates all finite minimal-strong canonical C0 presentations on <=4
vertices and all nested pairs b in C(a). Checks complete induced E and
C pair matrices, including missing incidences; also includes a
non-C-closed negative control.
"""
from itertools import product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)


def literal(edges, C, support, root, e):
    return (
        frozenset(e[u] for u in support),
        e[root],
        frozenset((e[u],e[v]) for u in support for v in support
                  if u != v and tuple(sorted((u,v))) in edges),
        frozenset((e[u],e[v]) for u in support for v in C[u] if v in support),
    )


def restrict(q, t, x):
    S, _point, adj, closure = q
    assert t <= S and x in t
    return (frozenset(t), x,
            frozenset((u,v) for u,v in adj if u in t and v in t),
            frozenset((u,v) for u,v in closure if u in t and v in t))


def test():
    presentations = nested = full_pairs = 0
    for n in range(1,5):
        for edges in graphs(n):
            for levels in range(1,n+1):
                for κ in product(range(levels),repeat=n):
                    if set(κ) != set(range(levels)):
                        continue
                    cuts = [frozenset(u for u in range(n) if κ[u]<i)
                            for i in range(levels+1)]
                    if not all(finite_minimal_step(cuts[i],cuts[i+1],edges)
                               for i in range(levels)):
                        continue
                    presentations += 1
                    C=finite_component_values(κ,edges)
                    for gap in (2, 7):
                        e={u:gap*(u+1) for u in range(n)}
                        for a in range(n):
                            qa=literal(edges,C,C[a],a,e)
                            for b in C[a]:
                                nested += 1
                                qb=literal(edges,C,C[b],b,e)
                                T=frozenset(e[v] for v in C[b])
                                # Intrinsic row-based support uses only
                                # the complete parent C-incidence matrix.
                                intrinsic=frozenset(y for x,y in qa[3]
                                    if x==e[b] and y in qa[0])
                                assert intrinsic==T and e[b] in intrinsic
                                assert T<=qa[0]
                                assert restrict(qa,T,e[b]) == qb
                                assert all((qb[1],v) in qb[3] for v in qb[0])
                                assert all(v in qb[0] for _u,v in qb[3])
                                for u in T:
                                    for v in T:
                                        assert ((u,v) in restrict(qa,T,e[b])[2]) == (
                                            (u,v) in qb[2])
                                        assert ((u,v) in restrict(qa,T,e[b])[3]) == (
                                            (u,v) in qb[3])
                                        full_pairs += 1
    assert presentations == 1401
    # Restricting to a non-C-closed support is only an induced record,
    # not a complete unary substructure.
    C=[frozenset({0}),frozenset({0,1})]
    parent=literal({(0,1)},C,frozenset({0,1}),1,{0:0,1:1})
    wrong=restrict(parent,frozenset({1}),1)
    assert wrong != literal({(0,1)},C,C[1],1,{0:0,1:1})
    assert (1,0) in parent[3] and (1,0) not in wrong[3]
    # A supported root-generated record without a finite C0 witness
    # can have a nonreflexive C-row for another vertex.
    raw_support=frozenset({0,1})
    raw_closure=frozenset({(0,0),(0,1)})
    assert all((0,y) in raw_closure for y in raw_support)
    assert not any((1,y) in raw_closure for y in raw_support)
    print(f"PASS nested raw C0 codes: {presentations} presentations, "
          f"{nested} nested restrictions across two coordinate maps, "
          f"{full_pairs} exact E/C pair checks; nonclosed negative control")


if __name__ == "__main__":
    test()
