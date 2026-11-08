#!/usr/bin/env python3
"""Adversarial finite normalizer for one-generated C0 local ordered types.

For every finite canonical minimal-strong component presentation on
1..4 vertices, choose the LEXICOGRAPHICALLY LEAST COMPLETE (E,C)
incidence matrix among all orders of each top block, leaving the
already selected order of its lower closure fixed. This chooses an
ordered ISOMORPHISM TYPE, not a vertex identity or generator.

Test invariance under ALL relabellings of the source vertex names,
strict heredity inside each presentation and a counterexample to
choosing the raw numeric order of the top vertices. Not a Lean proof.
"""
from itertools import combinations, permutations, product


def graphs(n):
    all_edges = list(combinations(range(n), 2))
    for mask in range(1 << len(all_edges)):
        yield frozenset(e for i,e in enumerate(all_edges) if mask & (1 << i))


def adj(edges, u, v):
    return u != v and tuple(sorted((u,v))) in edges


def subsets(s):
    s=sorted(s)
    for k in range(len(s)+1):
        for q in combinations(s,k):
            yield frozenset(q)


def predim(s,edges):
    return 2*len(s) - sum(u in s and v in s for u,v in edges)


def strong(a,b,edges):
    return a <= b and all(
        predim(a,edges) <= predim(z,edges)
        for z in subsets(b) if a <= z
    )


def minimal(a,b,edges):
    return a<b and strong(a,b,edges) and all(
        not strong(z,b,edges) for z in subsets(b) if a<z<b
    )


def values(kappa,edges):
    n=len(kappa);m=max(kappa)+1
    blocks=[frozenset(v for v in range(n) if kappa[v]==i)
            for i in range(m)]
    dep=[{j for j in range(i)
          if any(kappa[u]==i and kappa[v]==j and adj(edges,u,v)
                 for u in range(n) for v in range(n))}
         for i in range(m)]
    ans=[]
    for u in range(n):
        seen={kappa[u]}; todo=[kappa[u]]
        while todo:
            for j in dep[todo.pop()]:
                if j not in seen:
                    seen.add(j);todo.append(j)
        ans.append(frozenset(v for i in seen for v in blocks[i]))
    return ans


def code(order,lower,C,edges):
    return (
        len(lower),
        tuple(int(adj(edges,u,v)) for u in order for v in order),
        tuple(int(v in C[u]) for u in order for v in order),
    )


def canonical_order(lower_order,top,C,edges):
    assert top and set(lower_order).isdisjoint(top)
    candidates=[(code(lower_order+p,lower_order,C,edges),
                 lower_order+p)
                for p in permutations(sorted(top))]
    # Equal matrices may have several minimizing vertex orders.
    # Such ambiguity is an automorphism of the complete diagram.
    return min(candidates)


def choose_all(kappa,C,edges):
    n=len(kappa);m=max(kappa)+1
    order=[];codes={};orders={}
    for i in range(m):
        top={u for u in range(n) if kappa[u]==i}
        a=min(top)
        D=C[a]
        assert all(C[v]==D for v in top)
        lower=D-top
        assert lower <= set(order)
        old=tuple(u for u in order if u in lower)
        matrix,selected=canonical_order(old,top,C,edges)
        order.extend(selected[len(old):])
        for u in top:
            codes[u]=matrix; orders[u]=selected
    for a in range(n):
        local=tuple(u for u in order if u in C[a])
        assert local == orders[a]
        lower=C[a]-{u for u in range(n) if kappa[u]==kappa[a]}
        assert code(local,lower,C,edges)==codes[a]
        for b in C[a]:
            assert tuple(u for u in local if u in C[b])==orders[b]
    return codes


def main():
    presentations=locals_seen=compared=multivertex=0
    for n in range(1,5):
        for edges in graphs(n):
            for m in range(1,n+1):
                for kappa in product(range(m),repeat=n):
                    if set(kappa)!=set(range(m)):
                        continue
                    cuts=[frozenset(u for u in range(n) if kappa[u]<i)
                          for i in range(m+1)]
                    if not all(minimal(cuts[i],cuts[i+1],edges)
                               for i in range(m)):
                        continue
                    presentations+=1
                    if m<n:
                        multivertex+=1
                    C=values(kappa,edges)
                    base=choose_all(kappa,C,edges)
                    locals_seen+=n
                    for perm in permutations(range(n)):
                        h=dict(enumerate(perm))
                        k2=[None]*n;C2=[None]*n
                        for u in range(n):
                            k2[h[u]]=kappa[u]
                            C2[h[u]]=frozenset(h[v] for v in C[u])
                        edges2=frozenset(tuple(sorted((h[u],h[v])))
                                         for u,v in edges)
                        transformed=choose_all(k2,C2,edges2)
                        assert all(base[u]==transformed[h[u]]
                                   for u in range(n))
                        compared+=n
    assert (presentations,locals_seen,compared,multivertex)==(
        1401,5545,130289,4)

    # Sorting top vertices by their numerical labels instead of by
    # the minimal complete matrix is NOT presentation-invariant.
    C=(frozenset({0}),frozenset({0,1,2}),frozenset({0,1,2}))
    edges=frozenset({(0,1)})
    h={0:0,1:2,2:1}
    C2=[None]*3
    for u in range(3):
        C2[h[u]]=frozenset(h[v] for v in C[u])
    edges2=frozenset(tuple(sorted((h[u],h[v]))) for u,v in edges)
    first,_=canonical_order((0,),{1,2},C,edges)
    second,_=canonical_order((0,),{1,2},C2,edges2)
    assert first==second
    assert code((0,1,2),{0},C,edges)!=code(
        (0,1,2),{0},C2,edges2)

    print(f"PASS {presentations} minimal-strong presentations, "
          f"{locals_seen} canonical local codes, {compared} full "
          f"relabelled-type comparisons, {multivertex} non-singleton "
          "increment presentations and raw-label-order counterexample")


if __name__=="__main__":
    main()
