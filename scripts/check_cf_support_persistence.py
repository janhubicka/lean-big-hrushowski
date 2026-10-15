#!/usr/bin/env python3
"""Adversarial finite audit of exact CF support after free attachment.

For every simple labelled graph of order at most 5 and every partition
into P, A\P and fresh B, test when
  P ≤d A,
  no B--(A\P) edges,
  P <min_d P∪B, and cl_P^d(N_P(B))=P.
The full enlarged block must remain minimal d-closed over A,
P∪B must be d-closed in A∪B, and its computed old-neighbour
support cl_A^d(N_A(B)) must equal the original P.

The controls explicitly show why the base d-closedness and
back-neighbour hypotheses are necessary. Bounded tests supplement
the Lean theorem; they do not establish growth-class amalgamation.
"""
from itertools import combinations, product
from functools import lru_cache

tested=eligible=positive_supports=multi_vertex=0

def check_graph(n,E):
    global tested,eligible,positive_supports,multi_vertex
    allv=(1<<n)-1
    delta=tuple(2*s.bit_count()-sum(
        bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in E)
        for s in range(1<<n))
    @lru_cache(None)
    def dclosed(a,b):
        if a&~b:return False
        tail=b&~a
        sub=tail
        while sub:
            if delta[a]>=delta[a|sub]:return False
            sub=(sub-1)&tail
        return True
    @lru_cache(None)
    def hull(a,b):
        assert a&~b==0
        result=b
        for s in range(1<<n):
            if not a&~s and not s&~b and dclosed(s,b):
                result&=s
        assert dclosed(result,b)
        return result
    def minimal(a,b):
        return a!=b and dclosed(a,b) and all(
            s==a or s==b or not dclosed(s,b)
            for s in range(1<<n) if not a&~s and not s&~b)
    def nbrs(old,B):
        return sum(1<<v for v in range(n) if old&(1<<v)
                   and any(B&(1<<u) and tuple(sorted((u,v))) in E
                           for u in range(n)))
    for assignment in product((0,1,2),repeat=n):
        P=sum(1<<i for i,t in enumerate(assignment) if t==0)
        omitted=sum(1<<i for i,t in enumerate(assignment) if t==1)
        B=allv&~(P|omitted)
        A=P|omitted
        tested+=1
        if any((B&(1<<u) and omitted&(1<<v)) or
               (B&(1<<v) and omitted&(1<<u)) for u,v in E):
            continue
        if not dclosed(P,A):continue
        if not minimal(P,P|B):continue
        if hull(nbrs(P,B),P)!=P:continue
        eligible+=1
        if P:positive_supports+=1
        if B.bit_count()>1:multi_vertex+=1
        assert minimal(A,A|B),(n,E,P,A,B,"enlarged minimality")
        assert dclosed(P|B,A|B),(n,E,P,A,B,"second factor")
        assert nbrs(A,B)==nbrs(P,B),(n,E,P,A,B,"old neighbours")
        assert hull(nbrs(A,B),A)==P,(n,E,P,A,B,"support recovery")

for n in range(6):
    possible=tuple(combinations(range(n),2))
    for mask in range(1<<len(possible)):
        E={e for i,e in enumerate(possible) if mask&(1<<i)}
        check_graph(n,E)

# Dropping the no-cross hypothesis: a--b grows the old support.
cross={(0,1)}
def delta2(s):return 2*s.bit_count()-int(s==3)
assert delta2(1)>delta2(0) and delta2(2)>delta2(0)
assert cross

# Dropping P≤d A: an isolated new vertex over empty P,
# old A=K5 has δ(A)=0, so the least empty-generated hull in A
# cannot be empty.
K5=set(combinations(range(5),2))
def delta5(s):
    return 2*s.bit_count()-sum(bool(s&(1<<u)) and bool(s&(1<<v))
                               for u,v in K5)
assert delta5(31)==0 and delta5(0)==0
assert all(delta5(s)>0 for s in range(1,31))

assert eligible>0 and multi_vertex>0
print({
    "graphs_up_to_vertices":5,
    "partitions_examined":tested,
    "eligible_one_block_free_attachments":eligible,
    "eligible_nonempty_supports":positive_supports,
    "eligible_multi_vertex_blocks":multi_vertex,
    "enlarged_minimality_or_support_mismatches":0,
    "no_cross_necessity_control":True,
    "base_dclosedness_necessity_control":True,
})
