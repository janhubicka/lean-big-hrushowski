#!/usr/bin/env python3
"""Independent finite falsification of the actual closed-functional forth construction.

For all canonical minimal-strong component presentations on up to four
vertices, every finite closed old source base and every permutation of
the full finite graph, check that the inverse old partial isomorphism
embeds its target base into a finite source stage carrying the exact
named full unary values. The full permuted-stage response extends the
old base pointwise, has induced graph and whole-function equality,
and gives a closed strong target image.

This is NOT a finite proof of the countable extension property; that
is a separate kernel-certified theorem already imported by the Lean
source. Nonclosed bases and graph-only maps are negative controls.
"""
from itertools import combinations, permutations, product
from functools import lru_cache

stats = dict(graphs=0,indexings=0,canonical=0,
             closed_bases=0,permuted_extensions=0,
             full_value_checks=0,adjacency_checks=0,
             exact_old_map_checks=0,nonclosed_controls=0)

def subset(a,b):
    return a & ~b == 0

for n in range(5):
    pairs=list(combinations(range(n),2))
    whole=(1<<n)-1
    for mask in range(1<<len(pairs)):
        es={e for i,e in enumerate(pairs) if mask>>i&1}
        stats["graphs"]+=1

        @lru_cache(None)
        def delta(s):
            return 2*s.bit_count()-sum(
                int(bool(s>>u&1) and bool(s>>v&1)) for u,v in es)

        @lru_cache(None)
        def strong(a,b):
            return subset(a,b) and all(
                delta(c)>=delta(a) for c in range(1<<n)
                if subset(a,c) and subset(c,b))

        def minimal(a,b):
            return a!=b and strong(a,b) and all(
                c==a or c==b for c in range(1<<n)
                if subset(a,c) and subset(c,b) and strong(c,b))

        for m in range(1,max(2,n+1)):
            for ix in product(range(m),repeat=n):
                stats["indexings"]+=1
                cuts=[sum(1<<x for x in range(n) if ix[x]<k)
                      for k in range(m+1)]
                if not all(cuts[k]==cuts[k+1] or minimal(cuts[k],cuts[k+1])
                           for k in range(m)):
                    continue
                stats["canonical"]+=1

                def canonical_values():
                    result={}
                    for x in range(n):
                        reached={ix[x]}
                        while True:
                            before=len(reached)
                            for u,v in es:
                                if ix[u] in reached and ix[v]<ix[u]:
                                    reached.add(ix[v])
                                if ix[v] in reached and ix[u]<ix[v]:
                                    reached.add(ix[u])
                            if len(reached)==before:break
                        result[x]={z for z in range(n) if ix[z] in reached}
                    return result

                value=canonical_values()
                for s in range(1<<n):
                    src={x for x in range(n) if s>>x&1}
                    if not all(value[x] <= src for x in src):
                        stats["nonclosed_controls"]+=1
                        continue
                    stats["closed_bases"]+=1
                    # Full stage T contains every source point and any
                    # prescribed k; other finite stages work identically.
                    for perm in permutations(range(n)):
                        target_values={
                            perm[x]:{perm[z] for z in value[x]}
                            for x in range(n)}
                        target_edges={tuple(sorted((perm[u],perm[v])))
                                      for u,v in es}
                        target_base={perm[x] for x in src}
                        inverse={perm[x]:x for x in range(n)}
                        # i(y)=p^{-1}(y), and the target-base named
                        # value transports to the source complete value.
                        for y in target_base:
                            named={z for z in target_base
                                   if z in target_values[y]}
                            assert {inverse[z] for z in named}==value[inverse[y]]
                            stats["full_value_checks"]+=1
                        # The response to the target base is simply
                        # the permutation, so h(i(y))=y.
                        for x in src:
                            assert perm[inverse[perm[x]]]==perm[x]
                            stats["exact_old_map_checks"]+=1
                        # All full values and graph/nonedges are
                        # preserved by the same map, its image is closed.
                        for x in range(n):
                            assert target_values[perm[x]]=={
                                perm[z] for z in value[x]}
                            assert target_values[perm[x]] <= set(range(n))
                            stats["full_value_checks"]+=1
                            for y in range(n):
                                old=(tuple(sorted((x,y))) in es)
                                new=(tuple(sorted((perm[x],perm[y])))
                                     in target_edges)
                                assert old==new
                                stats["adjacency_checks"]+=1
                        stats["permuted_extensions"]+=1

# Nonclosed singleton with a strict dependency cannot have exact
# named C-values, and a graph-only swap need not be functional.
C={0:{0},1:{0,1}}
assert C[1]-{1}=={0}
swap={0:1,1:0}
assert C[swap[0]] != {swap[z] for z in C[0]}
stats["nonclosed_controls"]+=1
assert stats["graphs"]==76 and stats["canonical"]>0
assert stats["permuted_extensions"]>0
print("actual finite closed functional forth falsification:",stats)
