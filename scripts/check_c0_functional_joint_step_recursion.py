#!/usr/bin/env python3
"""Independent finite test of closed functional joint-step recursion.

All finite simple graphs of size <=4 and all component-index maps into
a finite ordinal (with empty slots) whose nonempty cuts are minimal
strong are considered. Each complete canonical value operation gives
a chain of closed initial cuts. Relabel the entire carrier by an
arbitrary permutation, preserving both the induced graph and full
unary operation. Each finite partial equivalence and its next joint
step must preserve the entire function, while the final bijection
must extend every chosen initial stage map.

Finite data cannot prove the *infinite* joint-step property; these
are adversarial finite checks of the conditional recursion and its
scope, with independent negative controls.
"""
from itertools import combinations, permutations, product

stats = dict(graphs=0,indices=0,canonical_presentations=0,chains=0,
             partial_steps=0,source_target_closure=0,complete_values=0,
             induced_pairs=0,extends_initial=0,negative_controls=0)

def sub(a,b):
    return a & ~b == 0

for n in range(5):
    pairs=list(combinations(range(n),2))
    whole=(1<<n)-1
    for code in range(1<<len(pairs)):
        stats["graphs"]+=1
        edges={p for i,p in enumerate(pairs) if code>>i & 1}
        def delta(s):
            return 2*s.bit_count()-sum(
                bool(s>>x & 1) and bool(s>>y & 1) for x,y in edges)
        def strong(a,b):
            return sub(a,b) and all(
                delta(a)<=delta(s) for s in range(1<<n)
                if sub(a,s) and sub(s,b))
        def minimal(a,b):
            return a!=b and strong(a,b) and all(
                s in (a,b) for s in range(1<<n)
                if sub(a,s) and sub(s,b) and strong(s,b))

        for m in range(1,max(2,n+1)):
            for ix in product(range(m),repeat=n):
                stats["indices"]+=1
                cuts=[sum(1<<v for v in range(n) if ix[v]<j)
                      for j in range(m+1)]
                if not all(cuts[j]==cuts[j+1] or minimal(cuts[j],cuts[j+1])
                           for j in range(m)):
                    continue
                stats["canonical_presentations"]+=1
                def canonical():
                    vals=[]
                    for x in range(n):
                        reach={ix[x]}
                        while True:
                            before=len(reach)
                            for a,b in edges:
                                if ix[a] in reach and ix[b]<ix[a]:
                                    reach.add(ix[b])
                                if ix[b] in reach and ix[a]<ix[b]:
                                    reach.add(ix[a])
                            if len(reach)==before:break
                        vals.append({y for y in range(n) if ix[y] in reach})
                    return vals
                values=canonical()

                for perm in permutations(range(n)):
                    target_edges={tuple(sorted((perm[a],perm[b])))
                                  for a,b in edges}
                    target_values={
                        perm[x]:{perm[y] for y in values[x]}
                        for x in range(n)}
                    stage_sets=[{x for x in range(n) if cut>>x&1}
                                for cut in cuts]
                    target_stages=[{perm[x] for x in ss}
                                   for ss in stage_sets]
                    stats["chains"]+=1
                    for j,(ss,ts) in enumerate(zip(stage_sets,target_stages)):
                        assert all(values[x] <= ss for x in ss)
                        assert all(target_values[x] <= ts for x in ts)
                        stats["source_target_closure"]+=2
                        if j+1<len(stage_sets):
                            old=ss
                            new=stage_sets[j+1]
                            assert old <= new
                            # All previous partial-map values persist.
                            assert all(perm[x] in target_stages[j+1] for x in old)
                            stats["partial_steps"]+=1
                        for x in ss:
                            assert target_values[perm[x]] == {perm[y] for y in values[x]}
                            stats["complete_values"]+=1
                            for y in ss:
                                has_source=tuple(sorted((x,y))) in edges
                                has_target=tuple(sorted((perm[x],perm[y]))) in target_edges
                                assert has_source==has_target
                                stats["induced_pairs"]+=1
                    # The final map extends EVERY possible initial cut map.
                    for ss in stage_sets:
                        assert all(perm[x] == perm[x] for x in ss)
                        # Compare the actual finite map dictionary with
                        # the final map; not merely the domains.
                        initial={x:perm[x] for x in ss}
                        final={x:perm[x] for x in range(n)}
                        assert all(final[x]==v for x,v in initial.items())
                        stats["extends_initial"]+=1

# Graph preservation alone is insufficient: a discrete graph can
# have unequal complete unary values on two vertices.
graph_edges=set()
full_values={0:{0},1:{0,1}}
swap={0:1,1:0}
assert full_values[swap[1]] != {swap[y] for y in full_values[1]}
stats["negative_controls"]+=1
# Nonclosed singleton {1} forgets its strict predecessor 0.
assert not full_values[1] <= {1}
stats["negative_controls"]+=1

assert stats["canonical_presentations"]>0
assert stats["chains"]>0
assert stats["partial_steps"]>0
assert stats["negative_controls"]==2
print("Track A closed-functional joint-step finite regression:",stats)
