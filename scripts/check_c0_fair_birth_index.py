#!/usr/bin/env python3
"""Independent complete finite falsification of fair birth indices."""
from itertools import product
stats = {"systems":0,"births":0,"components":0,"same_value":0,"strict_lower":0,"prefix_tests":0}
for n in range(1,5):
    full=(1<<n)-1
    for rows in product(range(1<<n), repeat=n):
        if any(not (rows[x] >> x & 1) for x in range(n)): continue
        if any(rows[y]&~rows[x] for x in range(n) for y in range(n)
               if rows[x]>>y & 1): continue
        stats["systems"]+=1
        def component(x):
            return sum(1<<y for y in range(n) if rows[y]==rows[x])
        def lower(x): return rows[x]&~component(x)
        q=0; birth=[-1]*n; prefixes=[0]
        while q!=full:
            eligible=[x for x in range(n) if not (q>>x & 1)
                      and not (lower(x)&~q)]
            assert eligible,(n,rows,q)
            x=min(eligible); p=component(x)
            assert p and not (p&q)
            for y in range(n):
                if p>>y & 1:
                    assert birth[y]==-1
                    birth[y]=len(prefixes)-1
                    stats["births"]+=1
            q|=p;prefixes.append(q);stats["components"]+=1
        for x in range(n):
            for k,p in enumerate(prefixes):
                assert (birth[x]<k)==bool(p>>x & 1)
                stats["prefix_tests"]+=1
            for y in range(n):
                assert (birth[x]==birth[y])==(rows[x]==rows[y])
                stats["same_value"]+=1
                if lower(x)>>y & 1:
                    assert birth[y]<birth[x]
                    stats["strict_lower"]+=1
assert stats=={"systems":389,"births":1516,"components":1345,
               "same_value":5958,"strict_lower":1250,"prefix_tests":6803},stats
print(stats)
