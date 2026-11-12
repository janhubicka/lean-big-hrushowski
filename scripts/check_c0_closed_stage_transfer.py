#!/usr/bin/env python3
"""All closed induced subgraphs preserve complete canonical C0 values."""
from itertools import combinations,product
stats=dict(graphs=0,indices=0,closed_subsets=0,vertex_checks=0,negative_nonclosed=0)
for n in range(1,5):
    all_pairs=list(combinations(range(n),2))
    for mask in range(1<<len(all_pairs)):
        edges=[e for i,e in enumerate(all_pairs) if mask>>i & 1]
        stats['graphs']+=1
        for ix in product(range(n),repeat=n):
            stats['indices']+=1
            def vals(domain):
                domain=set(domain)
                adj=[(a,b) for a,b in edges if a in domain and b in domain]
                result={}
                for x in domain:
                    reached={ix[x]}
                    while True:
                        prev=len(reached)
                        for a,b in adj:
                            if ix[a] in reached and ix[b]<ix[a]:reached.add(ix[b])
                            if ix[b] in reached and ix[a]<ix[b]:reached.add(ix[a])
                        if len(reached)==prev:break
                    result[x]={y for y in domain if ix[y] in reached}
                return result
            full=vals(range(n))
            for sm in range(1<<n):
                s={x for x in range(n) if sm>>x & 1}
                induced=vals(s)
                closed=all(full[x] <= s for x in s)
                if closed:
                    stats['closed_subsets']+=1
                    for x in s:
                        assert induced[x]==full[x],(n,edges,ix,s,x)
                        stats['vertex_checks']+=1
                elif any(induced[x]!=full[x] for x in s):
                    stats['negative_nonclosed']+=1
assert stats==dict(graphs=75,indices=16609,closed_subsets=75092,
                   vertex_checks=149769,negative_nonclosed=188814),stats
print('C0 closed canonical restriction exhaustive regression:',stats)
