#!/usr/bin/env python3
"""Adversarial raw-host coordinate-reassignment regression.

Tests actual minimal-strong finite C0 codes, full E/C relabelling,
and commutation of the complete finite unary value with two
strictly increasing (non-surjective) natural-number coordinate maps.
"""
from itertools import product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)


def code(edges, C, S, root, e):
    return (
        frozenset(e[u] for u in S),
        e[root],
        frozenset((e[u],e[v]) for u in S for v in S
                  if u != v and tuple(sorted((u,v))) in edges),
        frozenset((e[u],e[v]) for u in S for v in C[u] if v in S),
    )


def relabel(q, h):
    S, a, E, C = q
    return (
        frozenset(h(x) for x in S),
        h(a),
        frozenset((h(x),h(y)) for x,y in E),
        frozenset((h(x),h(y)) for x,y in C),
    )


def child(q, x):
    S, _, E, C = q
    assert x in S
    T = frozenset(y for y in S if (x,y) in C)
    assert x in T
    return (T,x,
        frozenset((u,v) for u,v in E if u in T and v in T),
        frozenset((u,v) for u,v in C if u in T and v in T))


def cval(q):
    return frozenset(child(q,x) for x in q[0])


def main():
    presentations = roots = child_equalities = 0
    maps = (lambda n: 2*n+5, lambda n: 3*n+1)
    for n in range(1,5):
        for edges in graphs(n):
            for levels in range(1,n+1):
                for kappa in product(range(levels),repeat=n):
                    if set(kappa)!=set(range(levels)):
                        continue
                    stages=[frozenset(v for v in range(n) if kappa[v]<i)
                            for i in range(levels+1)]
                    if not all(finite_minimal_step(stages[i],stages[i+1],edges)
                               for i in range(levels)):
                        continue
                    presentations += 1
                    C=finite_component_values(kappa,edges)
                    e={v:3*(v+1) for v in range(n)}
                    for a in range(n):
                        q=code(edges,C,C[a],a,e)
                        roots += 1
                        for h in maps:
                            e1={v:h(e[v]) for v in range(n)}
                            q1=code(edges,C,C[a],a,e1)
                            assert relabel(q,h)==q1
                            assert cval(q1)==frozenset(
                                relabel(r,h) for r in cval(q))
                            child_equalities += len(q[0])
                        comp=lambda x: maps[1](maps[0](x))
                        assert relabel(relabel(q,maps[0]),maps[1]) == relabel(q,comp)
    assert (presentations,roots)==(1401,5545)
    # A noninjective coordinate map can collapse the two vertices of
    # a supported complete graph, producing a diagonal loop.
    q=(frozenset({0,1}),1,frozenset({(0,1),(1,0)}),
       frozenset({(0,0),(1,0),(1,1)}))
    collapsed=relabel(q,lambda _:0)
    assert (0,0) in collapsed[2] and (0,0) not in q[2]
    print(f"PASS raw-host coordinate relabel: {presentations} "
          f"minimal-strong presentations, {roots} generated codes, "
          f"{child_equalities} complete C-value child comparisons; "
          "composition and noninjective negative control")


if __name__=="__main__":
    main()
