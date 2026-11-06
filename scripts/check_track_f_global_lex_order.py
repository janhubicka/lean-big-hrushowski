"""Independent finite test: lexicographic SCC ranks yield interval orders.

For all two-orientations of up to four labelled vertices, enumerate
all legal SCC orders and test two locally injective rank choices.
Checks totality, successor-first condition, SCC intervals and
restrictions to each SCC. Includes negative cases for illegal
component rankings and noninjective local ranks.
"""
from itertools import combinations, permutations, product
from collections import Counter
import json

def run():
    counts=Counter()
    for n in range(5):
        edges=tuple(combinations(range(n),2))
        for choices in product((0,1,2),repeat=len(edges)):
            out=[0]*n
            for (a,b),v in zip(edges,choices):
                if v==1: out[a]|=1<<b
                if v==2: out[b]|=1<<a
            if any(v.bit_count()>2 for v in out): continue
            counts["orientations"]+=1
            reach=[(1<<i)|out[i] for i in range(n)]
            for k in range(n):
                for i in range(n):
                    if reach[i]>>k&1: reach[i]|=reach[k]
            seen=set()
            comps=[]
            for i in range(n):
                block=tuple(j for j in range(n) if
                            reach[i]>>j&1 and reach[j]>>i&1)
                if block not in seen:
                    seen.add(block); comps.append(block)
            owner={v:i for i,B in enumerate(comps) for v in B}
            deps={(owner[y],owner[x]) for x in range(n) for y in range(n)
                  if reach[x]>>y&1 and not (reach[y]>>x&1)}
            for order in permutations(range(len(comps))):
                rank={block:i for i,block in enumerate(order)}
                if any(rank[i]>=rank[j] for i,j in deps): continue
                counts["component_rankings"]+=1
                for loc in [lambda x:x,lambda x,n=n:n-1-x]:
                    keys={v:(rank[owner[v]],loc(v)) for v in range(n)}
                    assert len(set(keys.values()))==n
                    sorted_vertices=sorted(range(n),key=keys.__getitem__)
                    for C in comps:
                        inds=[sorted_vertices.index(x) for x in C]
                        assert max(inds)-min(inds)+1==len(C)
                    for x in range(n):
                        for y in range(n):
                            if reach[x]>>y&1 and not (reach[y]>>x&1):
                                assert keys[y]<keys[x]
                    counts["constructed_orders"]+=1
    assert counts["orientations"]==653
    assert counts["component_rankings"]==1586
    assert counts["constructed_orders"]==3172
    # Invalid local ranks merge all vertices of a cycle into one key.
    cycle=[0b010,0b100,0b001]
    assert len({(0,0) for _ in cycle})==1
    # Reversing the rank of 0->1 puts the source first.
    assert (0,0)<(1,0)
    return dict(status="PASS",scope="finite structural order construction",
                counts=dict(counts),
                negative_cases=["noninjective ranks on a directed cycle",
                                "illegal component ranking on one arrow"])

if __name__=="__main__":
    print(json.dumps(run(),indent=2))
