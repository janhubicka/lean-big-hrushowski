#!/usr/bin/env python3
"""Adversarial test of finite chronological runs of d-closed blocks.

For every labelled simple graph of order at most 5 and every partition
into old A, first block B1 and second block B2, choose canonical
d-closed supports P1=cl_A(N_A(B1)) and
P2=cl_(A∪B1)(N_(A∪B1)(B2)).
If both local increments are minimal strict d-closed extensions,
test all intermediate subsets in
    A <=d A∪B1 <=d A∪B1∪B2.
The finite chain and the strict closure of the entire original
old stage are independently verified.

The run theorem assumes these sequential certificates and does
not assert that every arbitrary batch graph satisfies them or
belongs to the growth-function class C_F.
"""
from itertools import combinations, product
from functools import lru_cache

graphs = partitions = eligible_runs = multi_vertex_runs = 0
nonempty_support_runs = empty_old_runs = strict_checks = 0

def check(n,edges):
    global partitions,eligible_runs,multi_vertex_runs
    global nonempty_support_runs,empty_old_runs,strict_checks
    delta=tuple(2*s.bit_count()-sum(
        bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in edges)
        for s in range(1<<n))

    @lru_cache(None)
    def dclosed(a,b):
        if a&~b:return False
        t=b&~a
        rest=t
        while rest:
            if delta[a]>=delta[a|rest]:
                return False
            rest=(rest-1)&t
        return True

    @lru_cache(None)
    def hull(a,b):
        assert not a&~b
        h=b
        subset=b
        while True:
            if not a&~subset and dclosed(subset,b):
                h&=subset
            if not subset:break
            subset=(subset-1)&b
        assert dclosed(h,b)
        return h

    @lru_cache(None)
    def minimal(a,b):
        if a==b or not dclosed(a,b):
            return False
        z=b
        while True:
            if z not in (a,b) and not a&~z and dclosed(z,b):
                return False
            if not z:break
            z=(z-1)&b
        return True

    def neighbors(old,block):
        return sum(1<<v for v in range(n) if old&(1<<v)
                   and any(block&(1<<u)
                           and tuple(sorted((u,v))) in edges
                           for u in range(n)))

    for cats in product((0,1,2),repeat=n):
        A=sum(1<<i for i,t in enumerate(cats) if t==0)
        B=sum(1<<i for i,t in enumerate(cats) if t==1)
        C=sum(1<<i for i,t in enumerate(cats) if t==2)
        if not B or not C:continue
        partitions+=1
        P=hull(neighbors(A,B),A)
        if not minimal(P,P|B):continue
        current=A|B
        Q=hull(neighbors(current,C),current)
        if not minimal(Q,Q|C):continue
        eligible_runs+=1
        if B.bit_count()>1 or C.bit_count()>1:multi_vertex_runs+=1
        if P or Q:nonempty_support_runs+=1
        if not A:empty_old_runs+=1
        assert minimal(A,current)
        assert minimal(current,current|C)
        assert dclosed(A,current|C)
        assert A&~(current|C)==0
        strict_checks+=3

for n in range(6):
    pairs=tuple(combinations(range(n),2))
    for mask in range(1<<len(pairs)):
        graph={e for i,e in enumerate(pairs) if mask&(1<<i)}
        graphs+=1
        check(n,graph)

assert eligible_runs>0 and multi_vertex_runs>0
assert empty_old_runs>0 and nonempty_support_runs>0
print({
    "labelled_graphs":graphs,
    "nonempty_two_block_partitions":partitions,
    "certified_two_step_runs":eligible_runs,
    "runs_with_multivertex_increment":multi_vertex_runs,
    "runs_with_nonempty_support":nonempty_support_runs,
    "runs_starting_from_empty_old_graph":empty_old_runs,
    "strict_dclosed_and_chain_checks":strict_checks,
    "batch_dclosed_mismatches":0
})
