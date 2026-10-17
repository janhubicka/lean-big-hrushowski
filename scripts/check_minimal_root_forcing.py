#!/usr/bin/env python3
"""Exhaustive check for finite-cut closedness and minimal-root forcing.

All labelled simple graphs of order <=5, with
  delta(S) = 2*|S| - |E(S)|.
The program checks weak strength and strict d-closure
against *every* intermediate vertex subset.  No external
graph or model theory libraries are needed.
"""
def verify(n, graph):
    subsets = range(1 << n)
    edges = [(a,b) for a in range(n) for b in range(a+1,n)]
    delta = [0] * (1 << n)
    for s in range(1,1 << n):
        delta[s] = 2*s.bit_count() - sum(
            1 for j,(a,b) in enumerate(edges)
            if graph >> j & 1 and s >> a & 1 and s >> b & 1)
    strong = {(a,b):True for b in subsets for a in subsets if a & ~b == 0}
    strict = dict(strong)
    for (a,b) in strong:
        rem = b & ~a
        part = rem
        while part:
            value = delta[a | part]
            if value < delta[a]:
                strong[a,b] = False
            if value <= delta[a]:
                strict[a,b] = False
            part = (part - 1) & rem
    cuts = rooted = 0
    for c in subsets:
        for x in subsets:
            if x & ~c: continue
            for b in subsets:
                if b & ~c: continue
                meet = x & b
                for rel in (strong, strict):
                    if rel[x,c]:
                        cuts += 1
                        assert rel[meet,b], ('cut', n,graph,c,x,b,rel is strict)
                    else:
                        continue
                    for a in subsets:
                        if a & ~b or a & ~x or not rel[a,b]:
                            continue
                        fresh = b & ~a
                        if not fresh or not (fresh & x):
                            continue
                        minimal = True
                        part = fresh
                        while True:
                            z = a | part
                            if z not in (a,b) and rel[z,b]:
                                minimal = False
                                break
                            if not part:
                                break
                            part = (part - 1) & fresh
                        if minimal:
                            rooted += 1
                            assert b & ~x == 0, (
                                'root', n,graph,c,a,b,x,rel is strict)
    return cuts,rooted

if __name__ == '__main__':
    cuts = rooted = graphs = 0
    for n in range(6):
        count = 1 << (n*(n-1)//2)
        for graph in range(count):
            a,b = verify(n,graph)
            cuts += a
            rooted += b
        graphs += count
        print(f'n={n}: {count} graphs; cuts={cuts}; roots={rooted}',flush=True)
    assert (graphs,cuts,rooted) == (1100,5216272,2044354)
    print('PASS: 1100 graphs, 5216272 finite-cut cases, '
          '2044354 minimal-root cases')
