#!/usr/bin/env python3
"""Adversarial finite audit of the *constructed* simultaneous CF graph.

The old graph is labelled on U={0,...,m-1}, m<=3. For every actual
strictly d-closed support P and every complete ordered local graph
code with 1<=|B|<=2, collect all 2-sparse minimal d-closed codes
with exact support. Use the complete finite request catalogue:
  stage vertices = old names U + tagged fresh pairs (request_id,index)
  stage edges = old graph edges + all individually copied local edges.

Check the old induced graph is unchanged, every single request code
is an induced subgraph, every actual old neighbour belongs to that
request's named support, and no edge runs between distinct tags.
The class predicate 2-sparsity is a test filter, not the actual C_F.

This diagnostic does not prove that the *combined* graph belongs
to C_F or that the entire old stage is d-closed in the simultaneous
amalgam. Both require further mathematical arguments.
"""
from itertools import combinations
from functools import lru_cache

stages = request_count = fresh_count = total_edges = 0
local_pair_checks = no_cross_checks = base_checks = 0
multi_block_requests = nontrivial_supports = 0

def predim(size, edges):
    return tuple(2*s.bit_count() -
                 sum(bool(s&(1<<a)) and bool(s&(1<<b)) for a,b in edges)
                 for s in range(1<<size))

def closed(data,a,b):
    if a & ~b: return False
    tail = b & ~a
    sub=tail
    while sub:
        if data[a]>=data[a|sub]: return False
        sub=(sub-1)&tail
    return True

def hull(data,s,b):
    h=b
    z=b
    while True:
        if not s&~z and closed(data,z,b):
            h&=z
        if not z:break
        z=(z-1)&b
    assert closed(data,h,b)
    return h

def minimal(data,a,b):
    if a==b or not closed(data,a,b):return False
    z=b
    while True:
        if z not in (a,b) and not a&~z and closed(data,z,b):
            return False
        if not z:break
        z=(z-1)&b
    return True

def generate_requests(m,oldE):
    oldDelta=predim(m,oldE)
    requests=[]
    oldmask=(1<<m)-1
    for P in range(1<<m):
        if not closed(oldDelta,P,oldmask):
            continue
        pnames=tuple(i for i in range(m) if P&(1<<i))
        p=len(pnames)
        for n in (1,2):
            size=p+n
            pairs=tuple(combinations(range(size),2))
            required={(i,j) for i,j in combinations(range(p),2)
                      if tuple(sorted((pnames[i],pnames[j]))) in oldE}
            for mask in range(1<<len(pairs)):
                E={edge for j,edge in enumerate(pairs) if mask&(1<<j)}
                if {e for e in E if e[1]<p} != required:
                    continue
                data=predim(size,E)
                if min(data)<0:continue
                base=(1<<p)-1
                if not minimal(data,base,(1<<size)-1):continue
                neighbors=sum(1<<a for a in range(p)
                              if any(tuple(sorted((a,b))) in E
                                     for b in range(p,size)))
                if hull(data,neighbors,base)!=base:continue
                requests.append((P,pnames,n,E,mask))
    return requests

for m in range(4):
    pairs=tuple(combinations(range(m),2))
    for mask in range(1<<len(pairs)):
        oldE={edge for j,edge in enumerate(pairs) if mask&(1<<j)}
        stages+=1
        req=generate_requests(m,oldE)
        request_count+=len(req)
        stageE={tuple(sorted((("old",a),("old",b)))) for a,b in oldE}
        tags=set()
        for tag,(P,pnames,n,E,code) in enumerate(req):
            if P:nontrivial_supports+=1
            if n>1:multi_block_requests+=1
            vertices={("new",tag,j) for j in range(n)}
            assert not(tags & vertices)
            tags |= vertices
            def local_image(k):
                return ("old",pnames[k]) if k<len(pnames) else \
                       ("new",tag,k-len(pnames))
            assert len({local_image(i) for i in range(len(pnames)+n)}) == len(pnames)+n
            for a,b in E:
                stageE.add(tuple(sorted((local_image(a),local_image(b)))))
        fresh_count+=len(tags)
        total_edges+=len(stageE)
        assert {tuple(sorted((a[1],b[1]))) for a,b in stageE
                if a[0]=="old" and b[0]=="old"} == oldE
        base_checks+=len(pairs)
        for tag,(P,pnames,n,E,code) in enumerate(req):
            def local_image(k):
                return ("old",pnames[k]) if k<len(pnames) else \
                       ("new",tag,k-len(pnames))
            sz=len(pnames)+n
            for a,b in combinations(range(sz),2):
                assert (tuple(sorted((local_image(a),local_image(b))))
                        in stageE) == ((a,b) in E)
                local_pair_checks+=1
            for j in range(n):
                u=("new",tag,j)
                for v in range(m):
                    if not P&(1<<v):
                        assert tuple(sorted((u,("old",v)))) not in stageE
                        no_cross_checks+=1
        for a,b in stageE:
            if a[0]=="new" and b[0]=="new":
                assert a[1]==b[1],(m,mask,a,b,"cross between request tags")
                no_cross_checks+=1

assert request_count>0 and multi_block_requests>0
# A deliberately invalid added cross-edge is detectable:
fake_edge=tuple(sorted((("new",0,0),("new",1,0))))
assert fake_edge[0][1]!=fake_edge[1][1]

print({
    "old_graph_stages":stages,
    "tagged_local_requests":request_count,
    "fresh_vertices":fresh_count,
    "total_constructed_edges":total_edges,
    "complete_local_adjacency_checks":local_pair_checks,
    "absence_of_crossing_checks":no_cross_checks,
    "old_base_edge_checks":base_checks,
    "multi_vertex_blocks":multi_block_requests,
    "nonempty_support_requests":nontrivial_supports,
    "old_or_local_or_crossing_mismatches":0
})
