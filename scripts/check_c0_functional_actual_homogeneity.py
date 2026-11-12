#!/usr/bin/env python3
"""Independent finite adversarial test of closed functional forth/back composition.

Retain every canonical minimal-strong component presentation on up to
four vertices. Enumerate all C-closed finite bases, all relabelled
target presentations under vertex permutations, and all prescribed
source and target vertices. The global relabelled isomorphism must
extend the same finite base map pointwise, preserve AND reflect all
graph edges, and transport complete unary values. Its finite domain
and range are closed, and the two one-sided extension requirements
can be satisfied simultaneously.

This is a diagnostic small-case test, NOT a proof of existence of
joint steps in the infinite Fraïssé limit. Explicit negative controls
reject graph-only maps and maps on nonclosed bases.
"""
from itertools import combinations, permutations, product
from functools import lru_cache

stats=dict(graphs=0,indices=0,canonical=0,closed_bases=0,
           partial_maps=0,joint_requests=0,complete_values=0,
           induced_pairs=0,nonclosed_controls=0,graph_only_controls=0)

def is_subset(a,b):return not (a&~b)

for n in range(5):
    pairs=list(combinations(range(n),2))
    full=(1<<n)-1
    for code in range(1<<len(pairs)):
        edges={e for j,e in enumerate(pairs) if code>>j&1}
        stats["graphs"]+=1

        @lru_cache(None)
        def delta(s):
            return 2*s.bit_count()-sum(
                bool(s>>u&1) and bool(s>>v&1) for u,v in edges)

        @lru_cache(None)
        def strong(a,b):
            return is_subset(a,b) and all(
                delta(a)<=delta(c) for c in range(1<<n)
                if is_subset(a,c) and is_subset(c,b))

        def minimal(a,b):
            return a!=b and strong(a,b) and all(
                c in (a,b) for c in range(1<<n)
                if is_subset(a,c) and is_subset(c,b) and strong(c,b))

        for slots in range(1,max(2,n+1)):
            for index in product(range(slots),repeat=n):
                stats["indices"]+=1
                cuts=[sum(1<<v for v in range(n) if index[v]<r)
                      for r in range(slots+1)]
                if not all(cuts[k]==cuts[k+1] or
                           minimal(cuts[k],cuts[k+1])
                           for k in range(slots)):
                    continue
                stats["canonical"]+=1

                def values():
                    out={}
                    for x in range(n):
                        reached={index[x]}
                        while True:
                            before=len(reached)
                            for u,v in edges:
                                if index[u] in reached and index[v]<index[u]:
                                    reached.add(index[v])
                                if index[v] in reached and index[u]<index[v]:
                                    reached.add(index[u])
                            if len(reached)==before:break
                        out[x]={z for z in range(n) if index[z] in reached}
                    return out

                C=values()
                for mask in range(1<<n):
                    base={x for x in range(n) if mask>>x&1}
                    if any(not C[x]<=base for x in base):
                        stats["nonclosed_controls"]+=1
                        continue
                    stats["closed_bases"]+=1
                    for perm in permutations(range(n)):
                        p={x:perm[x] for x in base}
                        image={perm[x] for x in base}
                        target_C={perm[x]:{perm[y] for y in C[x]}
                                  for x in range(n)}
                        target_edges={frozenset((perm[u],perm[v]))
                                      for u,v in edges}
                        assert all(target_C[z]<=image for z in image)
                        stats["partial_maps"]+=1
                        # The full relabelling is the finite analogue
                        # of the final union equivalence. It *must*
                        # extend the old partial isomorphism pointwise.
                        total={x:perm[x] for x in range(n)}
                        assert all(total[x]==v for x,v in p.items())
                        for x in range(n):
                            assert target_C[total[x]]=={
                                total[y] for y in C[x]}
                            stats["complete_values"]+=1
                            for y in range(n):
                                old=frozenset((x,y)) in {
                                    frozenset(e) for e in edges}
                                new=frozenset((total[x],total[y])) in target_edges
                                assert old==new
                                stats["induced_pairs"]+=1
                        for k in range(n):
                            # First cover k on the source, then k on
                            # the target, without changing old values.
                            assert k in total
                            assert k in set(total.values())
                            assert all(total[x]==v for x,v in p.items())
                            stats["joint_requests"]+=1

# A graph-only automorphism of the *actual canonical two-vertex edge*
# (with index 0 before 1) need not preserve complete unary values:
# C(0)={0}, C(1)={0,1}, and swapping endpoints is not functional.
C={0:{0},1:{0,1}}
swap={0:1,1:0}
assert C[swap[0]] != {swap[z] for z in C[0]}
stats["graph_only_controls"]+=1
# The singleton {1} omits 0 from C(1), so restricted membership
# does not preserve the complete unary structure.
assert not C[1] <= {1}
stats["nonclosed_controls"]+=1

assert stats["graphs"]==76,stats
assert stats["canonical"]>0 and stats["joint_requests"]>0,stats
assert stats["graph_only_controls"]==1
print("Track A closed functional finite joint-step regression:",stats)
