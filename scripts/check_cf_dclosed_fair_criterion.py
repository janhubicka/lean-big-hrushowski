#!/usr/bin/env python3
"""Bounded audit of fair recurrence and d-closed response promotion.

The Lean criterion combines two ingredients:
 (i) any encoded finite request occurs again beyond every stage, and
 (ii) if the response is d-closed in a finite stage that is itself
      d-closed in the entire graph, the response is globally d-closed.

The finite checker tests the monotone pairing interface using a
standard bijective pairing implementation, and exhaustively tests
the strict local-to-global transitivity on all labelled simple
graphs of order <=4. The actual Lean theorem uses Mathlib's
Nat.pair/unpair; these checks supplement, not replace, its proof.
"""
from itertools import combinations

pairs=stage_lower_bounds=finite_stage_chains=responses_checked=0

def pair(a,b):
    t=a+b
    return t*(t+1)//2+b

def unpair(code):
    lo,hi=0,1
    while hi*(hi+1)//2<=code:
        hi*=2
    while lo+1<hi:
        md=(lo+hi)//2
        if md*(md+1)//2<=code:lo=md
        else:hi=md
    t=lo
    b=code-t*(t+1)//2
    return (t-b,b)

for request in range(80):
    for threshold in range(80):
        stage=pair(request,threshold)
        assert stage>=threshold
        assert unpair(stage)==(request,threshold)
        stage_lower_bounds+=1
        pairs+=1

def delta(n,E):
    return tuple(2*s.bit_count()-sum(
        bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in E)
        for s in range(1<<n))

def closed(d,a,b):
    if a&~b:return False
    rest=b&~a
    s=rest
    while s:
        if d[a]>=d[a|s]:return False
        s=(s-1)&rest
    return True

for n in range(5):
    possible=tuple(combinations(range(n),2))
    for edges_mask in range(1<<len(possible)):
        E={e for j,e in enumerate(possible) if edges_mask&(1<<j)}
        d=delta(n,E)
        full=(1<<n)-1
        for stage in range(1<<n):
            if not closed(d,stage,full):
                continue
            finite_stage_chains+=1
            for target in range(1<<n):
                if target&~stage or not closed(d,target,stage):
                    continue
                assert closed(d,target,full)
                responses_checked+=1

assert responses_checked>0 and stage_lower_bounds==6400
print({
    "pairing_recurrence_checks":pairs,
    "later_stage_bounds_checked":stage_lower_bounds,
    "finite_closed_stages_examined":finite_stage_chains,
    "local_responses_promoted_to_full_closedness":responses_checked,
    "fair_or_strict_response_mismatches":0
})
