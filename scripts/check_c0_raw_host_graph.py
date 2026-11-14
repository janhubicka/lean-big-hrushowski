#!/usr/bin/env python3
"""Adversarial regression for graph recovery from raw C0 coordinate codes.

Every minimal-strong C0 presentation on <=4 vertices is checked under
two increasing coordinate assignments. Complete E and C matrices
determine finite child values, J-values, and a simple raw graph.
This script also tests consistency with the original graph edges.
"""
from itertools import product
from check_c0_coordinate_host_finite import (
    graphs, finite_minimal_step, finite_component_values,
)


def make_code(edges, C, S, a, labels):
    return (
        frozenset(labels[u] for u in S),
        labels[a],
        frozenset((labels[u], labels[v]) for u in S for v in S
                  if u != v and tuple(sorted((u, v))) in edges),
        frozenset((labels[u], labels[v]) for u in S for v in C[u] if v in S),
    )


def child(q, x):
    support, _, adj, C = q
    assert x in support
    t = frozenset(y for y in support if (x,y) in C)
    assert x in t
    return (t,x,
        frozenset((u,v) for u,v in adj if u in t and v in t),
        frozenset((u,v) for u,v in C if u in t and v in t))


def closure(q):
    return frozenset(child(q,x) for x in q[0])


def back(q):
    return frozenset(r for r in closure(q) if (q[1],r[1]) in q[2])


def raw_adj(q,r):
    return ((r in closure(q) and (q[1],r[1]) in q[2]) or
            (q in closure(r) and (q[1],r[1]) in r[2]))


def check():
    presentations = roots = pairs = positive = recovered = 0
    for n in range(1,5):
        for edges in graphs(n):
            for levels in range(1,n+1):
                for stages in product(range(levels), repeat=n):
                    if set(stages) != set(range(levels)):
                        continue
                    cuts=[frozenset(u for u in range(n) if stages[u]<j)
                          for j in range(levels+1)]
                    if not all(finite_minimal_step(cuts[j],cuts[j+1],edges)
                               for j in range(levels)):
                        continue
                    presentations += 1
                    C=finite_component_values(stages,edges)
                    for gap in (3,11):
                        labels={u:gap*(u+1) for u in range(n)}
                        q=[make_code(edges,C,C[a],a,labels) for a in range(n)]
                        roots += n
                        # Injectivity of the actual finite occurrence,
                        # exact complete C-value and exact named J-value.
                        assert len(set(q))==n
                        for a in range(n):
                            assert closure(q[a]) == frozenset(q[b] for b in C[a])
                            assert back(q[a]) == frozenset(
                                q[b] for b in C[a]
                                if a!=b and tuple(sorted((a,b))) in edges)
                        for a in range(n):
                            qa=q[a]
                            assert all((v,u) in qa[2] for u,v in qa[2])
                            assert not any((u,u) in qa[2] for u in qa[0])
                            assert back(qa) <= closure(qa)
                            for b in range(n):
                                qb=q[b]
                                h=raw_adj(qa,qb)
                                assert h == raw_adj(qb,qa)
                                assert (not h) if a == b else True
                                assert h == (qb in back(qa) or qa in back(qb))
                                if h:
                                    positive += 1
                                    assert qb in closure(qa) or qa in closure(qb)
                                expected=(a!=b and tuple(sorted((a,b))) in edges)
                                assert h == expected
                                recovered += 1
                                pairs += 1
    assert presentations == 1401
    # Well-supported rooted records need not encode a simple graph.
    bad_support=frozenset({0,1})
    asymmetric=(bad_support,0,frozenset({(0,1)}),
                frozenset({(0,0),(0,1),(1,1)}))
    assert (0,1) in asymmetric[2] and (1,0) not in asymmetric[2]
    loop=(frozenset({0}),0,frozenset({(0,0)}),frozenset({(0,0)}))
    assert loop in closure(loop) and raw_adj(loop,loop)
    print(f"PASS raw host graph: {presentations} minimal-strong presentations, "
          f"{roots} complete vertex codes, {pairs} endpoint pair checks, "
          f"{positive} graph edges, {recovered} exact graph reconstructions; "
          "asymmetric and loop negative controls")


if __name__=="__main__":
    check()
