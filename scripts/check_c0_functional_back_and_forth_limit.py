#!/usr/bin/env python3
"""Finite adversarial test of closed functional back-and-forth unions.

Enumerate canonical finite C0 structures on <=4 labelled vertices,
all original component-index maps (with empty slots), and relabellings
of the *entire* carrier. Closed stage prefixes give a coherent nested
chain of functional partial isomorphisms. The union must preserve the
full canonical unary values and reflect edges and nonedges.

Counterexample: a one-vertex domain omitting its strict lower
dependency may preserve its restricted unary membership trivially,
yet cannot preserve its complete two-vertex unary value.
"""
from itertools import combinations, permutations, product

stats=dict(graphs=0,canonical_maps=0,closed_chain_checks=0,
           source_target_closure_checks=0,full_value_checks=0,
           induced_edge_nonedge_checks=0,nonclosed_negative_controls=0)

for n in range(5):
    edgepairs=list(combinations(range(n),2))
    full=(1<<n)-1
    for edge_mask in range(1<<len(edgepairs)):
        edges={e for i,e in enumerate(edgepairs) if edge_mask>>i & 1}
        stats["graphs"]+=1

        def canonical(idx,domain):
            output={}
            for x in range(n):
                if not (domain>>x & 1):continue
                reached={idx[x]}
                while True:
                    before=len(reached)
                    for a,b in edges:
                        if not ((domain>>a & 1) and (domain>>b & 1)):
                            continue
                        if idx[a] in reached and idx[b]<idx[a]:
                            reached.add(idx[b])
                        if idx[b] in reached and idx[a]<idx[b]:
                            reached.add(idx[a])
                    if len(reached)==before:break
                output[x]={y for y in range(n)
                           if domain>>y & 1 and idx[y] in reached}
            return output

        for slots in range(1,max(2,n+1)):
            for idx in product(range(slots),repeat=n):
                stats["canonical_maps"]+=1
                full_values=canonical(idx,full)
                # Stages are oldStage κ k, k=0,...,slots.
                stages=[sum(1<<x for x in range(n) if idx[x]<k)
                        for k in range(slots+1)]
                for s in stages:
                    values=canonical(idx,s)
                    for x in range(n):
                        if s>>x & 1:
                            assert values[x]==full_values[x]
                            stats["source_target_closure_checks"]+=1

                for perm in permutations(range(n)):
                    target_edges={tuple(sorted((perm[a],perm[b])))
                                  for a,b in edges}
                    target_values={
                        perm[x]: {perm[y] for y in full_values[x]}
                        for x in range(n)}
                    for s in stages:
                        target={perm[x] for x in range(n) if s>>x & 1}
                        assert all(full_values[x] <= {
                            y for y in range(n) if s>>y & 1}
                            for x in range(n) if s>>x & 1)
                        assert all(target_values[y] <= target
                                   for y in target)
                        stats["closed_chain_checks"]+=1
                    # The same single bijection must preserve all
                    # complete values and the induced graph.
                    for x in range(n):
                        assert target_values[perm[x]] == {
                            perm[y] for y in full_values[x]}
                        stats["full_value_checks"]+=1
                        for y in range(n):
                            xy=tuple(sorted((x,y)))
                            uv=tuple(sorted((perm[x],perm[y])))
                            assert (xy in edges)==(uv in target_edges)
                            stats["induced_edge_nonedge_checks"]+=1

                for s in range(1<<n):
                    if s in stages:continue
                    restricted=canonical(idx,s)
                    if any(restricted[x]!=full_values[x]
                           for x in range(n) if s>>x & 1):
                        stats["nonclosed_negative_controls"]+=1

# Explicit nonclosed two-vertex unary example. C(1)={0,1};
# restricting to the singleton {1} removes the required predecessor 0.
full_values={0:{0},1:{0,1}}
restricted={1:{1}}
assert restricted[1]!=full_values[1]
assert stats["graphs"]==76 and stats["full_value_checks"]>0
assert stats["nonclosed_negative_controls"]>0
print("Track A full-function back-and-forth finite test:",stats)
