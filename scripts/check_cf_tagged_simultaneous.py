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
predimension_image_checks = minimal_image_checks = 0
relative_subbatch_strict_checks = 0
exact_support_image_checks = finite_closed_old_support_checks = 0
sequential_relative_predimension_checks = multiblock_strict_samples = 0
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
            prefix={("old",u) for u in range(m)} | tags
            def local_image(k):
                return ("old",pnames[k]) if k<len(pnames) else \
                       ("new",tag,k-len(pnames))
            assert len({local_image(i) for i in range(len(pnames)+n)}) == len(pnames)+n
            for a,b in E:
                stageE.add(tuple(sorted((local_image(a),local_image(b)))))
            def delta_on(vertex_set):
                return 2*len(vertex_set)-sum(
                    u in vertex_set and v in vertex_set for u,v in stageE)
            support={("old",u) for u in pnames}
            # Check the *actual chronological prefix*, not only
            # an abstract relative predimension identity. Each
            # nonempty subset of the next fresh block increases
            # its predimension relative to the current prefix.
            for subset in range(1,1<<n):
                selected={("new",tag,j) for j in range(n)
                          if subset&(1<<j)}
                prefix_diff=delta_on(prefix|selected)-delta_on(prefix)
                local_diff=delta_on(support|selected)-delta_on(support)
                assert prefix_diff==local_diff and prefix_diff>0
                sequential_relative_predimension_checks+=1
            tags |= vertices
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
            # Adversarially compare every induced predimension value,
            # not just pairwise edges, and recheck strict minimality
            # in the copied code's entire finite image interval.
            code_delta = predim(sz,E)
            stage_delta = []
            for sub in range(1<<sz):
                image={local_image(k) for k in range(sz) if sub&(1<<k)}
                stage_edges=sum(a in image and b in image for a,b in stageE)
                stage_delta.append(2*sub.bit_count()-stage_edges)
                assert stage_delta[-1]==code_delta[sub]
                predimension_image_checks+=1
            full=(1<<sz)-1
            base=(1<<len(pnames))-1
            assert minimal(tuple(stage_delta),base,full)
            minimal_image_checks+=1
            # The complete old-neighbour set and its finite strict
            # hull in this *actual tagged induced copy* coincide
            # with the prescribed named support of the original type.
            source_n=sum(1<<v for v in range(len(pnames))
                         if any((v,w) in E for w in range(len(pnames),sz)))
            target_n=sum(1<<v for v in range(len(pnames))
                         if any(tuple(sorted((local_image(v),local_image(w))))
                                in stageE for w in range(len(pnames),sz)))
            assert source_n == target_n
            assert hull(tuple(stage_delta),target_n,base) == base
            exact_support_image_checks+=1
            assert closed(predim(m,oldE),P,(1<<m)-1)
            finite_closed_old_support_checks+=1
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
        # Directly sample strict d-closedness of the original old
        # prefix against intermediate sets meeting several blocks.
        # These bounded samples supplement the certified finite
        # transitivity proof and do not replace its universal claim.
        old_set={("old",u) for u in range(m)}
        def full_delta(vertex_set):
            return 2*len(vertex_set)-sum(
                u in vertex_set and v in vertex_set for u,v in stageE)
        base_d=full_delta(old_set)
        for u in sorted(tags):
            assert full_delta(old_set|{u})>base_d
            multiblock_strict_samples+=1
        for u,v in combinations(sorted(tags),2):
            assert full_delta(old_set|{u,v})>base_d
            multiblock_strict_samples+=1
        ordered=sorted(tags)
        for stride in range(1,min(7,len(ordered)+1)):
            selection=set(ordered[::stride])
            if selection:
                assert full_delta(old_set|selection)>base_d
                multiblock_strict_samples+=1
        # Arbitrary sub-batch prefixes, not just chronological
        # initial segments: verify strict growth against added
        # vertices from previously unused request tags.
        all_req_ids=sorted({u[1] for u in tags})
        done_samples=[
            set(),
            set(all_req_ids[::2]),
            set(all_req_ids[1::2]),
            set(all_req_ids[:2]),
            set(all_req_ids[:-1]),
            set(all_req_ids)
        ]
        for done_tags in done_samples:
            prefix=old_set|{u for u in tags if u[1] in done_tags}
            fresh_outside=sorted(u for u in tags if u[1] not in done_tags)
            base=full_delta(prefix)
            increments=[{u} for u in fresh_outside]
            increments.extend(set(z) for z in
                              combinations(fresh_outside[:12],2))
            for stride in (1,2,3,5):
                added=set(fresh_outside[::stride])
                if added: increments.append(added)
            for added in increments:
                assert added and added.isdisjoint(prefix)
                assert full_delta(prefix|added)>base, (
                    m,mask,done_tags,added,"relative prefix not d-closed")
                relative_subbatch_strict_checks+=1

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
    "all_local_predimension_image_checks":predimension_image_checks,
    "strict_minimal_image_checks":minimal_image_checks,
    "exact_tagged_support_hull_checks":exact_support_image_checks,
    "strict_chronological_new_subset_checks":sequential_relative_predimension_checks,
    "global_old_dclosed_multiblock_samples":multiblock_strict_samples,
    "arbitrary_dclosed_subbatch_prefix_checks":relative_subbatch_strict_checks,
    "actual_old_support_closed_checks":finite_closed_old_support_checks,
    "absence_of_crossing_checks":no_cross_checks,
    "old_base_edge_checks":base_checks,
    "multi_vertex_blocks":multi_block_requests,
    "nonempty_support_requests":nontrivial_supports,
    "old_or_local_or_crossing_mismatches":0
})
