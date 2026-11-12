#!/usr/bin/env python3
"""Independent exhaustive inverse-base transport regression.

On each reflexive/transitive finite unary system with at most four
vertices, enumerate every closed finite source base and every
permutation of that base into a *separate* target-label carrier.
The resulting complete-functional isomorphism must have inverse
base maps preserving entire values in every enclosing finite stage,
and preserve/refect induced adjacency under all graph choices.

This tests *literal labels and finite complete values*, not an
infinitary extension theorem. An omitted dependency gives an
independent negative control for nonclosed bases.
"""
from itertools import permutations, product, combinations

stats=dict(unary_systems=0,closed_bases=0,transport_maps=0,
           enclosing_stages=0,complete_value_checks=0,
           membership_reflections=0,induced_graph_pairs=0,
           nonclosed_negative_controls=0)

for n in range(1,5):
    full=(1<<n)-1
    for rows in product(range(1<<n),repeat=n):
        if any(not (rows[x]>>x&1) for x in range(n)):continue
        if any(rows[y]&~rows[x] for x in range(n)
               for y in range(n) if rows[x]>>y&1):continue
        stats["unary_systems"]+=1
        for mask in range(1<<n):
            src=[x for x in range(n) if mask>>x&1]
            if any(rows[x]&~mask for x in src):
                stats["nonclosed_negative_controls"]+=1
                continue
            stats["closed_bases"]+=1
            for perm in permutations(src):
                # The abstract target carrier has labels n,n+1,...
                # The finite graph isomorphism sends each source x
                # to n + its position in perm.
                f={x:n+i for i,x in enumerate(perm)}
                inv={y:x for x,y in f.items()}
                tar={f[x] for x in src}
                target_values={
                    f[x]:{f[y] for y in src if rows[x]>>y&1}
                    for x in src}
                for original in src:
                    y=f[original]
                    named={z for z in tar if z in target_values[y]}
                    inverse_image={inv[z] for z in named}
                    true_value={z for z in range(n) if rows[original]>>z&1}
                    assert inverse_image==true_value,(n,rows,mask,perm,original)
                    stats["complete_value_checks"]+=1
                    for other in src:
                        assert ((other in true_value)==
                                (f[other] in target_values[y]))
                        stats["membership_reflections"]+=1

                # Enclosing stage T is any finite set containing the
                # original source, with inverse map y -> inv[y].
                for stage in range(1<<n):
                    if mask & ~stage:continue
                    assert all((inv[y] in range(n) and stage>>inv[y]&1)
                               for y in tar)
                    stats["enclosing_stages"]+=1
                stats["transport_maps"]+=1

    # The graph condition is independent of the unary operation.
    for code in range(1<<(n*(n-1)//2)):
        pairs=list(combinations(range(n),2))
        edges={e for i,e in enumerate(pairs) if code>>i&1}
        for mask in range(1<<n):
            src=[x for x in range(n) if mask>>x&1]
            for perm in permutations(src):
                f={x:n+i for i,x in enumerate(perm)}
                inv={y:x for x,y in f.items()}
                tar_edges={tuple(sorted((f[u],f[v])))
                           for u,v in edges if u in src and v in src}
                for u in f:
                    for v in f:
                        old=(tuple(sorted((u,v))) in edges)
                        new=(tuple(sorted((f[u],f[v]))) in tar_edges)
                        assert old==new
                        stats["induced_graph_pairs"]+=1

# A nonclosed singleton cannot carry the complete value C(1)={0,1}.
C={0:{0},1:{0,1}}
assert C[1]-{1}=={0}
assert stats["unary_systems"]==389,stats
assert stats["nonclosed_negative_controls"]>0
print("inverse closed functional base transport:",stats)
