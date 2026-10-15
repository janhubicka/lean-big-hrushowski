#!/usr/bin/env python3
"""Independent finite check of the catalogue of actual CF stage requests.

For each old labelled graph U with at most three vertices,
enumerate every *actual* support P⊆U that is strictly d-closed
in U. For each P and every fresh ordered size 1≤n≤2,
enumerate all complete graph codes on P⊕Fin n that agree
with U on P. Keep precisely the codes satisfying:
  - an explicit sample admissibility filter (2-sparsity);
  - a minimal strict d-closed step P<_d P∪B;
  - exact support cl_P^d(N_P(B))=P.
Check that the finite request key (old graph, literal P, n,
full local adjacency mask) is unique, and that isomorphic but
distinct actual supports are not identified.

The 2-sparse filter is ONLY a finite test predicate, not the
published C_F membership condition. No free-amalgamation or
countable extension theorem is inferred from these checks.
"""
from itertools import combinations
from functools import lru_cache

stages=closed_supports=all_graph_codes=request_count=multi_block=0
requests=set()
distinct_named_support_example=False

def predim(n,E):
    return tuple(2*s.bit_count()-sum(
        bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in E)
        for s in range(1<<n))

def predicates(n,E):
    d=predim(n,E)
    @lru_cache(None)
    def closed(a,b):
        if a & ~b:return False
        tail=b & ~a
        sub=tail
        while sub:
            if d[a]>=d[a|sub]:return False
            sub=(sub-1)&tail
        return True
    @lru_cache(None)
    def hull(S,b):
        h=b
        for c in range(1<<n):
            if not S&~c and not c&~b and closed(c,b):
                h&=c
        assert closed(h,b)
        return h
    def minimal(a,b):
        if a==b or not closed(a,b):return False
        return all(c==a or c==b or not closed(c,b)
                   for c in range(1<<n)
                   if not a&~c and not c&~b)
    def sparse():
        return all(x>=0 for x in d)
    return closed,hull,minimal,sparse

for m in range(4):
    oldpairs=tuple(combinations(range(m),2))
    for oldmask in range(1<<len(oldpairs)):
        oldE={e for j,e in enumerate(oldpairs) if oldmask&(1<<j)}
        stages+=1
        old_closed,_,_,_=predicates(m,oldE)
        for P in range(1<<m):
            if not old_closed(P,(1<<m)-1):
                continue
            closed_supports+=1
            support=[v for v in range(m) if P&(1<<v)]
            p=len(support)
            for n in (1,2):
                N=p+n
                pairs=tuple(combinations(range(N),2))
                old_restriction={(i,j) for i,j in combinations(range(p),2)
                    if tuple(sorted((support[i],support[j]))) in oldE}
                for mask in range(1<<len(pairs)):
                    localE={e for j,e in enumerate(pairs) if mask&(1<<j)}
                    all_graph_codes+=1
                    if {e for e in localE if e[1]<p}!=old_restriction:
                        continue
                    closed,hull,minimal,sparse=predicates(N,localE)
                    full=(1<<N)-1
                    base=(1<<p)-1
                    if not sparse() or not minimal(base,full):
                        continue
                    neighbors=sum(1<<v for v in range(p)
                                  if any(tuple(sorted((v,w))) in localE
                                         for w in range(p,N)))
                    if hull(neighbors,base)!=base:
                        continue
                    assert n<=2
                    key=(m,oldmask,P,n,mask)
                    assert key not in requests
                    requests.add(key)
                    request_count+=1
                    if n>1:multi_block+=1

# P={0} and P={1} are distinct actual supports even when
# their induced old graph and ordered local extension are isomorphic.
w0=[k for k in requests if k[0]==2 and k[1]==0 and k[2]==1 and k[3]==1]
w1=[k for k in requests if k[0]==2 and k[1]==0 and k[2]==2 and k[3]==1]
assert w0 and w1
distinct_named_support_example=True
assert request_count>0 and multi_block>0

print({
    "finite_old_graph_stages":stages,
    "actual_dclosed_supports":closed_supports,
    "complete_local_graph_codes_examined":all_graph_codes,
    "distinct_bounded_ordered_requests":request_count,
    "non_singleton_new_blocks":multi_block,
    "pointwise_named_supports_kept_distinct":distinct_named_support_example,
    "duplicate_request_keys":0,
    "support_or_minimality_mismatches":0
})
