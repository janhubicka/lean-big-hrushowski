#!/usr/bin/env python3
"""Independent bounded adversarial checks of strict d-closed chains.

For every labelled simple graph with <=5 vertices, every partition
into three chronological ranks defines S0 ⊆ S1 ⊆ V.
If S0<=d S1 and S1<=d V, check S0<=d V, the global
finite-ambient analogue of the countable d-closed-chain theorem.

Additional tests:
- strict d-closedness restricts to every intermediate ambient;
- omission of the covering hypothesis fails (constant empty stages
  in K5 are internally d-closed but not globally d-closed);
- weak strongness does not substitute for strict d-closedness
  (singletons in K4 can be strong but not d-closed).

The quantification over all finite sets of an infinite union is
handled by Lean, not by this bounded regression.
"""
from itertools import combinations, product

graphs=chain_patterns=eligible=restrict_checks=0
nontrivial_transitivity=weak_strong_counterexample=False

def delta(n,E):
    return tuple(2*s.bit_count()-sum(
        bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in E)
        for s in range(1<<n))

def dclosed(d,a,b):
    if a&~b:return False
    tail=b&~a
    s=tail
    while s:
        if d[a]>=d[a|s]:return False
        s=(s-1)&tail
    return True

def strong(d,a,b):
    if a&~b:return False
    tail=b&~a
    s=tail
    while True:
        if d[a]>d[a|s]:return False
        if not s:break
        s=(s-1)&tail
    return True

for n in range(6):
    possible=tuple(combinations(range(n),2))
    for mask in range(1<<len(possible)):
        E={e for k,e in enumerate(possible) if mask&(1<<k)}
        d=delta(n,E)
        full=(1<<n)-1
        graphs+=1
        for rank in product((0,1,2),repeat=n):
            s0=sum(1<<v for v,t in enumerate(rank) if t==0)
            s1=sum(1<<v for v,t in enumerate(rank) if t!=2)
            chain_patterns+=1
            if not dclosed(d,s0,s1) or not dclosed(d,s1,full):
                continue
            eligible+=1
            assert dclosed(d,s0,full),(n,E,s0,s1,"strict transitivity")
            if s0!=s1 and s1!=full:
                nontrivial_transitivity+=1
            # Global strict closure in this finite ambient restricts
            # to every intermediate stage containing the base.
            for subset in range(1<<n):
                if s0&~subset or subset&~full:continue
                assert dclosed(d,s0,subset)
                restrict_checks+=1

K5=set(combinations(range(5),2))
d5=delta(5,K5)
assert dclosed(d5,0,0)
assert not dclosed(d5,0,31)

K4=set(combinations(range(4),2))
d4=delta(4,K4)
assert strong(d4,1,15)
assert not dclosed(d4,1,15)
weak_strong_counterexample=True

assert eligible>0 and nontrivial_transitivity>0
print({
    "labelled_graphs":graphs,
    "nested_stage_patterns":chain_patterns,
    "applicable_strict_stage_chains":eligible,
    "nontrivial_two_strict_steps":nontrivial_transitivity,
    "global_to_intermediate_restrictions":restrict_checks,
    "missing_cover_K5_counterexample":True,
    "strong_not_strict_K4_counterexample":weak_strong_counterexample,
    "strict_chain_mismatches":0
})
