#!/usr/bin/env python3
"""Independent finite audit: shared C0 components and two-sided amalgams.

Enumerate finite canonical minimal-strong presentations on two graphs
sharing a common closed functional base P. The graph free amalgam
identifies P and adds no left-tail/right-tail edges.

For every pair of presentations whose complete named unary values on
P agree, verify:
* both presentations determine the same component equivalence on P;
* P contains every backward-reachable component of each P vertex;
* a finite canonical presentation of the free graph amalgam exists
  that preserves *both* original complete unary functions.

The last assertion is a bounded counterexample search, not a Lean
proof of two-sided free functional amalgamation. It includes
non-singleton minimal components in graphs of total order up to five.
"""
from itertools import product, combinations
from functools import lru_cache

@lru_cache(None)
def ordered(n):
    if not n:
        return [((),0)]
    return [(idx, max(idx)+1) for idx in product(range(n),repeat=n)
            if set(idx)==set(range(max(idx)+1))]

def edges(n,mask):
    return tuple(e for i,e in enumerate(combinations(range(n),2))
                 if mask>>i & 1)

def delta(E,S):
    return 2*S.bit_count()-sum(bool(S&(1<<u)) and bool(S&(1<<v))
                               for u,v in E)

def strong(E,a,b):
    if a&~b:
        return False
    t=tail=b&~a
    while True:
        if delta(E,a)>delta(E,a|t):
            return False
        if not t:
            return True
        t=(t-1)&tail

def minimal(E,a,b):
    if a==b or not strong(E,a,b):
        return False
    t=tail=b&~a
    while True:
        c=a|t
        if c not in (a,b) and strong(E,c,b):
            return False
        if not t:
            return True
        t=(t-1)&tail

def values(E,idx,m):
    n=len(idx)
    blocks=[sum(1<<v for v,k in enumerate(idx) if k==j)
            for j in range(m)]
    deps=[set() for _ in range(m)]
    for u,v in E:
        i,j=idx[u],idx[v]
        if i>j:deps[i].add(j)
        elif j>i:deps[j].add(i)
    out=[]
    for i in range(m):
        reached,queue={i},[i]
        for t in queue:
            for j in deps[t]:
                if j not in reached:
                    reached.add(j)
                    queue.append(j)
        out.append(sum(blocks[j] for j in reached))
    return tuple(out[idx[v]] for v in range(n))

@lru_cache(None)
def presentations(n,mask):
    E=edges(n,mask)
    out=[]
    for idx,m in ordered(n):
        stages=[sum(1<<v for v,k in enumerate(idx) if k<i)
                for i in range(m+1)]
        if all(minimal(E,a,b) for a,b in zip(stages,stages[1:])):
            out.append((idx,values(E,idx,m)))
    return out

def remap(bitset,f):
    return sum(1<<f[i] for i in range(len(f)) if bitset>>i & 1)

def audit_span(p,l,r):
    nL,nR,nD=p+l,p+r,p+l+r
    base=(1<<p)-1
    mapR=tuple(range(p))+tuple(p+l+j for j in range(r))
    graph_spans=diagrams=0
    for gm in range(1<<(nL*(nL-1)//2)):
        gl=presentations(nL,gm)
        if not gl:
            continue
        el=edges(nL,gm)
        for hm in range(1<<(nR*(nR-1)//2)):
            gr=presentations(nR,hm)
            if not gr:
                continue
            er=edges(nR,hm)
            if frozenset(e for e in el if e[1]<p)!= \
               frozenset(e for e in er if e[1]<p):
                continue
            left=[(idx,vv) for idx,vv in gl if all(
                vv[u]&~base==0 for u in range(p))]
            right=[(idx,vv) for idx,vv in gr if all(
                vv[u]&~base==0 for u in range(p))]
            if not left or not right:
                continue
            graph_spans+=1
            joined=set(el)|{tuple(sorted((mapR[u],mapR[v])))
                             for u,v in er}
            maskD=sum(1<<k for k,e in enumerate(
                combinations(range(nD),2)) if e in joined)
            # Keep the ENTIRE left witnessing order unchanged and
            # append only the fresh right-tail components. Even when
            # closed P is interleaved with left-tail components, no
            # common base ordering or reindexing of left is needed.
            possible={vv for _,vv in presentations(nD,maskD)}
            for idxL,vL in left:
                for idxR,vR in right:
                    if vL[:p]!=vR[:p]:
                        continue
                    diagrams+=1
                    for u in range(p):
                        for v in range(p):
                            assert (idxL[u]==idxL[v])==(
                                idxR[u]==idxR[v]), (
                                    "common component mismatch",p,l,r)
                            if u<v and (u,v) in el and idxL[u]!=idxL[v]:
                                assert (idxL[u]<idxL[v])==(
                                    idxR[u]<idxR[v]), (
                                    "common edge orientation mismatch",p,l,r)
                        assert vL[u]&~base==0
                    required=vL+tuple(remap(vR[u],mapR)
                                      for u in range(p,nR))
                    right_parts=sorted({idxR[u] for u in range(p,nR)})
                    mLeft=max(idxL,default=-1)+1
                    rpos={k:mLeft+i for i,k in enumerate(right_parts)}
                    chosen=idxL+tuple(rpos[idxR[u]] for u in range(p,nR))
                    mChosen=mLeft+len(right_parts)
                    assert set(chosen)==set(range(mChosen))
                    stages=[sum(1<<v for v,j in enumerate(chosen) if j<k)
                            for k in range(mChosen+1)]
                    assert all(minimal(tuple(joined),a,b)
                               for a,b in zip(stages,stages[1:])), (
                        "left-fixed appended-tail order breaks minimality",
                        (p,l,r),el,er,idxL,idxR,chosen,stages)
                    actual=values(tuple(joined),chosen,mChosen)
                    assert actual==required, (
                        "left-fixed appended-tail order changes named unary values",
                        (p,l,r),el,er,idxL,idxR,vL,vR,chosen,actual,required)
                    assert required in possible, (
                        "two-sided functional amalgam counterexample",
                        (p,l,r),el,er,idxL,idxR,vL,vR)
    return graph_spans,diagrams


def audit_interleaved_triangle():
    """Seven-vertex stress test: closed P is NOT initial in left.
    
    Left: P={0,1,2}, l=3, blocks {0},{3},{1},{2},
    with edge 0--3. Right: reverse base order {2},{1},{0},
    then one genuinely nonsingleton triangle {3,4,5}
    meeting the three base vertices in distinct edges.
    """
    p,l,r=3,1,3
    el=((0,3),)
    er=((0,3),(1,4),(2,5),(3,4),(3,5),(4,5))
    idxL=(0,2,3,1)
    idxR=(2,1,0,3,3,3)
    mapR=(0,1,2,4,5,6)
    joined=tuple(sorted(set(el)|{tuple(sorted((mapR[u],mapR[v])))
                                    for u,v in er}))
    chosen=idxL+(4,4,4)
    def stages(idx,m):
        return [sum(1<<v for v,k in enumerate(idx) if k<i)
                for i in range(m+1)]
    assert all(minimal(el,a,b) for a,b in zip(stages(idxL,4),
                                             stages(idxL,4)[1:]))
    assert all(minimal(er,a,b) for a,b in zip(stages(idxR,4),
                                             stages(idxR,4)[1:]))
    assert all(minimal(joined,a,b) for a,b in zip(stages(chosen,5),
                                                 stages(chosen,5)[1:]))
    vl=values(el,idxL,4)
    vr=values(er,idxR,4)
    assert all(vl[i]==vr[i] and vl[i]<(1<<p) for i in range(p))
    expected=vl+tuple(remap(vr[u],mapR) for u in range(p,p+r))
    assert values(joined,chosen,5)==expected
    assert chosen[:p+l]==idxL
    return True

configs=[(0,1,1),(1,1,1),(2,1,1),(1,2,1),
         (1,1,2),(1,2,2),(1,3,1),(2,2,1)]
results=[audit_span(*c) for c in configs]
assert all(a>0 and b>0 for a,b in results)
print({"configurations":len(configs),
       "finite_graph_span_types":sum(a for a,_ in results),
       "compatible_closed_functional_diagrams":sum(b for _,b in results),
       "intrinsic_common_partitions_verified":True,
       "two_sided_functional_amalgam_counterexamples":0,
       "left_witness_unchanged_construction_verified":True,
       "seven_vertex_interleaved_triangle_verified":audit_interleaved_triangle()})
