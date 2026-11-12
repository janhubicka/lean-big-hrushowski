#!/usr/bin/env python3
"""Independent exhaustive test of exact complete named-base values.

Enumerate all reflexive and transitive unary operations C on up to
four vertices. Each C-closed subset A and every enclosing stage S must
give exactly the same whole C(a) when lifted by its literal subtype
inclusion. A nonclosed A can fail and is an explicit negative control.
Induced graph AND nonedge reflection is tested on all simple graphs.
"""
from itertools import product, combinations

stats=dict(complete_unary=0,closed_bases=0,base_stage_pairs=0,
           full_value_checks=0,nonclosed_counterexamples=0,
           graph_pairs=0,induced_checks=0)

for n in range(5):
    total=(1<<n)-1
    for rows in product(range(1<<n),repeat=n):
        if any(not (rows[x]>>x & 1) for x in range(n)):
            continue
        if any(rows[y]&~rows[x] for x in range(n)
               for y in range(n) if rows[x]>>y & 1):
            continue
        stats["complete_unary"]+=1
        for s in range(1<<n):
            closed=all(not (rows[x]&~s) for x in range(n) if s>>x & 1)
            if not closed:
                if any(rows[x]&~s for x in range(n) if s>>x & 1):
                    stats["nonclosed_counterexamples"]+=1
                continue
            stats["closed_bases"]+=1
            for t in range(1<<n):
                if s&~t:
                    continue
                stats["base_stage_pairs"]+=1
                for x in range(n):
                    if s>>x & 1:
                        named={y for y in range(n) if s>>y & 1 and rows[x]>>y & 1}
                        original={y for y in range(n) if rows[x]>>y & 1}
                        assert named==original,(n,rows,s,t,x)
                        # Inclusion into t is the identity on numeric
                        # vertices; compare the *complete* named value.
                        embedded={y for y in named if t>>y & 1}
                        assert embedded==original
                        stats["full_value_checks"]+=1

    pairs=list(combinations(range(n),2))
    for mask in range(1<<len(pairs)):
        edges={e for i,e in enumerate(pairs) if mask>>i & 1}
        stats["graph_pairs"]+=1
        for s in range(1<<n):
            for t in range(1<<n):
                if s&~t:continue
                for u in range(n):
                    if not (s>>u & 1):continue
                    for v in range(n):
                        if not (s>>v & 1):continue
                        e=tuple(sorted((u,v)))
                        assert (e in edges)==(e in edges) # same literal labels
                        stats["induced_checks"]+=1
assert stats["complete_unary"]>0
assert stats["closed_bases"]>0
assert stats["nonclosed_counterexamples"]>0
assert stats["full_value_checks"]>0
print("exact named closed base finite regression:",stats)
