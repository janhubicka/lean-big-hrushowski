#!/usr/bin/env python3
"""Finite generated C-closures and no-cross graph edges in the raw C0 host.

Independent check on all <=4-vertex minimal-strong C0 presentations.
Verifies the union-of-one-generated-values closure formula, leastness,
idempotence, intersection/union of closed sets and free cross-edges.
"""
from itertools import combinations, product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)
from check_c0_raw_host_graph import make_code, closure, raw_adj


def subsets(seq):
    return [frozenset(t) for k in range(len(seq)+1)
            for t in combinations(seq,k)]


def close(s):
    return frozenset(r for q in s for r in closure(q))


def closed(s):
    return all(closure(q) <= s for q in s)


def main():
    presentations = finite_sets = closed_pairs = 0
    for n in range(1,5):
        for edges in graphs(n):
            for levels in range(1,n+1):
                for ranks in product(range(levels),repeat=n):
                    if set(ranks)!=set(range(levels)):
                        continue
                    stages=[frozenset(v for v in range(n) if ranks[v]<j)
                            for j in range(levels+1)]
                    if not all(finite_minimal_step(stages[j],stages[j+1],edges)
                               for j in range(levels)):
                        continue
                    presentations+=1
                    C=finite_component_values(ranks,edges)
                    for gap in (2,7):
                        labels={u:gap*(u+1) for u in range(n)}
                        q=[make_code(edges,C,C[a],a,labels) for a in range(n)]
                        assert len(set(q))==n
                        all_sets=subsets(q)
                        all_closed=[s for s in all_sets if closed(s)]
                        for s in all_sets:
                            hull=close(s)
                            finite_sets+=1
                            assert s<=hull
                            assert closed(hull)
                            assert close(hull)==hull
                            for t in all_closed:
                                if s<=t:
                                    assert hull<=t
                        for s in all_closed:
                            for t in all_closed:
                                assert closed(s|t) and closed(s&t)
                                for u in s-t:
                                    for v in t-s:
                                        assert not raw_adj(u,v)
                                        closed_pairs+=1
    assert presentations==1401
    # If named C-values are not nested, the one-step union formula
    # need not produce a closed set.
    from check_c0_raw_host_unary_axioms import child, closed_value
    malformed=(frozenset({0,1,2}),0,frozenset(),
               frozenset({(0,0),(0,1),(0,2),
                          (1,1),(1,2),(2,0),(2,2)}))
    one=frozenset({malformed})
    first=frozenset({r for q in one for r in closed_value(q)})
    assert any(not closed_value(q)<=first for q in first)
    print(f"PASS finite raw C0 closures: {presentations} "
          f"minimal-strong presentations, {finite_sets} generated "
          f"finite subsets, {closed_pairs} exclusive-cross edge checks; "
          "nonnested negative control")


if __name__=="__main__":
    main()
