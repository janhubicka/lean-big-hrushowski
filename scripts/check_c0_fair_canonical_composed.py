#!/usr/bin/env python3
"""Combined regression: fair closed-prefix chronologies reconstruct complete canonical C0 values."""
from itertools import combinations,product
stats=dict(graphs=0,old_indices=0,fair_components=0,prefix_vertex_value_checks=0,
           same_class_comparisons=0,strict_lower_checks=0)
for n in range(1,5):
    all_edges=list(combinations(range(n),2))
    for mask in range(1<<len(all_edges)):
        edges=[e for k,e in enumerate(all_edges) if mask>>k & 1]
        stats["graphs"]+=1
        for old_ix in product(range(n),repeat=n):
            stats["old_indices"]+=1
            def canonical(ix,s):
                s=set(s)
                es=[(a,b) for a,b in edges if a in s and b in s]
                out={}
                for x in s:
                    reached={ix[x]}
                    while True:
                        prev=len(reached)
                        for a,b in es:
                            if ix[a] in reached and ix[b]<ix[a]: reached.add(ix[b])
                            if ix[b] in reached and ix[a]<ix[b]: reached.add(ix[a])
                        if len(reached)==prev:break
                    out[x]=frozenset(y for y in s if ix[y] in reached)
                return out
            old=canonical(old_ix,range(n))
            new_ix=[-1]*n
            q=set()
            k=0
            while len(q)<n:
                enabled=[]
                for x in range(n):
                    if x in q:continue
                    cx=old[x]
                    p={y for y in cx if old[y]==cx}
                    if (cx-p)<=q:enabled.append(x)
                assert enabled,(n,edges,old_ix,q)
                x=min(enabled)
                p={y for y in range(n) if old[y]==old[x]}
                assert not p&q
                for y in p:new_ix[y]=k
                k+=1
                q|=p
                assert all(old[y]<=q for y in q)
                actual=canonical(new_ix,q)
                for y in q:
                    assert actual[y]==old[y],(n,edges,old_ix,new_ix,q,y,actual[y],old[y])
                    stats["prefix_vertex_value_checks"]+=1
                stats["fair_components"]+=1
            for x in range(n):
                for y in range(n):
                    assert (new_ix[x]==new_ix[y])==(old[x]==old[y])
                    stats["same_class_comparisons"]+=1
                    if y in old[x] and old[y]!=old[x]:
                        assert new_ix[y]<new_ix[x]
                        stats["strict_lower_checks"]+=1
assert stats==dict(graphs=75,old_indices=16609,fair_components=45269,
                  prefix_vertex_value_checks=124099,same_class_comparisons=264121,
                  strict_lower_checks=56624),stats
print("combined fair canonical C0 value regression:",stats)
