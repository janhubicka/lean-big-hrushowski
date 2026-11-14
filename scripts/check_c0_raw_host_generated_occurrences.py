#!/usr/bin/env python3
"""Adversarial exact finite generated-occurrence equivalence.

For each finite minimal-strong C0 presentation and each root a, the
actual source closure C(a) must be in bijection with the raw host
unary value of the COMPLETE pointed code of a. The bijection reflects
all E/C/J pairs, including nonedges and absent C/J memberships.
"""
from itertools import product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)
from check_c0_raw_host_graph import make_code, closure, back, raw_adj


def main():
    presentations = roots = source_pairs = child_points = 0
    for n in range(1,5):
        for edges in graphs(n):
            for levels in range(1,n+1):
                for kappa in product(range(levels),repeat=n):
                    if set(kappa)!=set(range(levels)):
                        continue
                    cuts=[frozenset(u for u in range(n) if kappa[u]<j)
                          for j in range(levels+1)]
                    if not all(finite_minimal_step(cuts[j],cuts[j+1],edges)
                               for j in range(levels)):
                        continue
                    presentations+=1
                    Cv=finite_component_values(kappa,edges)
                    order=sorted(range(n),key=lambda u:(kappa[u],u))
                    idx={v:i for i,v in enumerate(order)}
                    E={tuple(sorted((idx[u],idx[v]))) for u,v in edges}
                    C=[frozenset(idx[v] for v in Cv[order[i]])
                       for i in range(n)]
                    for gap in (2,7):
                        e={u:gap*(u+1) for u in range(n)}
                        q=[make_code(E,C,C[a],a,e) for a in range(n)]
                        for a in range(n):
                            roots+=1
                            image=frozenset(q[b] for b in C[a])
                            assert closure(q[a])==image
                            assert len(image)==len(C[a])
                            child_points+=len(image)
                            for b in C[a]:
                                for c in C[a]:
                                    source_pairs+=1
                                    assert raw_adj(q[b],q[c])==(
                                        b!=c and tuple(sorted((b,c))) in E)
                                    assert (q[c] in closure(q[b]))==(c in C[b])
                                    assert (q[c] in back(q[b]))==(
                                        c in C[b] and b!=c and
                                        tuple(sorted((b,c))) in E)
    assert presentations==1401
    # Two independent singleton components can both occur in the
    # same finite source, but a one-generated closure is NOT the whole
    # source: the equivalence is with C(a), never arbitrary V.
    q0=make_code(set(),[{0},{1}],{0},0,{0:0,1:1})
    q1=make_code(set(),[{0},{1}],{1},1,{0:0,1:1})
    assert q1 not in closure(q0) and q0 not in closure(q1)
    print(f"PASS raw host generated occurrences: {presentations} "
          f"minimal-strong presentations, {roots} pointed source "
          f"closures, {child_points} exact child-code images, "
          f"{source_pairs} full E/C/J pair equivalences; "
          "nongenerated-union negative control")


if __name__=="__main__":
    main()
