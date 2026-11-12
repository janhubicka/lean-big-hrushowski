#!/usr/bin/env python3
"""Independent finite falsification of two-sided C0 functional amalgamation.

Exhaust all graph/index presentations with at most three total tagged
vertices, allowing unused component levels. Keep only pairs with
empty-or-minimal-strong canonical steps and identical complete named
base values. Check the actual free graph, induced embeddings, strong
images, whole component chronology and *both full unary functions*.

Also include a four-vertex K4 minimal-strong increment test with a
nontrivial top component. Relabelling tests check original carrier
permutations rather than relying on raw numeric labels as invariants.
"""
from itertools import combinations, permutations, product

stats = dict(pairs=0, valid_pairs=0, minimal_steps=0,
             full_value_checks=0, strong_images=0, relabel_checks=0)

def graph_edges(n, code):
    pp = list(combinations(range(n), 2))
    return {p for i, p in enumerate(pp) if code >> i & 1}

def predim(n, es, subset):
    return 2 * subset.bit_count() - sum(
        (subset >> u & 1) and (subset >> v & 1) for u, v in es)

def issub(a, b):
    return (a & ~b) == 0

def strong(n, es, a, b):
    return issub(a, b) and all(
        predim(n, es, a) <= predim(n, es, s)
        for s in range(1 << n) if issub(a, s) and issub(s, b))

def minimal(n, es, a, b):
    return strong(n, es, a, b) and a != b and all(
        s == a or s == b for s in range(1 << n)
        if issub(a, s) and issub(s, b) and strong(n, es, s, b))

def steps(n, es, idx, slots):
    old = [sum(1 << v for v in range(n) if idx[v] < k)
           for k in range(slots + 1)]
    return all(old[k] == old[k+1] or minimal(n, es, old[k], old[k+1])
               for k in range(slots))

def canonical(n, es, idx):
    output = []
    for x in range(n):
        reached = {idx[x]}
        while True:
            before = len(reached)
            for u,v in es:
                if idx[u] in reached and idx[v] < idx[u]:
                    reached.add(idx[v])
                if idx[v] in reached and idx[u] < idx[v]:
                    reached.add(idx[u])
            if len(reached) == before:
                break
        output.append(sum(1 << y for y in range(n) if idx[y] in reached))
    return output

def check(p, l, r, eL, idxL, mL, eR, idxR, mR):
    a=p+l; b=p+r
    if not steps(a,eL,idxL,mL) or not steps(b,eR,idxR,mR):
        return
    vl=canonical(a,eL,idxL)
    vr=canonical(b,eR,idxR)
    base=(1<<p)-1
    if not all((vl[x] & ~base)==0 and (vr[x] & ~base)==0
               and vl[x] == vr[x] for x in range(p)):
        return
    stats["valid_pairs"] += 1

    size=p+l+r
    E=set(eL)
    def right(x):
        return x if x<p else p+l+x-p
    E|={tuple(sorted((right(u),right(v)))) for u,v in eR}
    ix=tuple(list(idxL) + [mL+mR+idxR[p+k] for k in range(r)])
    assert steps(size,E,ix,mL+2*mR), (
        p,l,r,eL,eR,idxL,idxR,ix)
    assert all(predim(size,E,s)>=0 for s in range(1<<size))
    leftMask=(1<<a)-1
    rightMask=base | sum(1 << (p+l+k) for k in range(r))
    assert strong(size,E,leftMask,(1<<size)-1)
    assert strong(size,E,rightMask,(1<<size)-1)
    stats["strong_images"]+=2

    cv=canonical(size,E,ix)
    for x in range(a):
        assert cv[x] == vl[x], (p,l,r,eL,idxL,eR,idxR,ix,x)
        stats["full_value_checks"]+=1
    for x in range(b):
        transported=sum(1<<right(y) for y in range(b) if vr[x]>>y & 1)
        assert cv[right(x)] == transported, (
            p,l,r,eL,idxL,eR,idxR,ix,x)
        stats["full_value_checks"]+=1

    for u in range(a):
        for v in range(a):
            assert (tuple(sorted((u,v))) in E) == (
                tuple(sorted((u,v))) in eL)
    for u in range(b):
        for v in range(b):
            assert (tuple(sorted((right(u),right(v)))) in E) == (
                tuple(sorted((u,v))) in eR)
    assert all((u,p+l+k) not in E for u in range(p,p+l) for k in range(r))
    for k in range(mL+2*mR):
        old=sum(1<<v for v in range(size) if ix[v]<k)
        new=sum(1<<v for v in range(size) if ix[v]<k+1)
        if old!=new:
            assert minimal(size,E,old,new)
            stats["minimal_steps"]+=1

    # A few explicit relabellings of the *original* two carriers:
    # full values must transport by the inverse vertex permutation.
    if a<=3 and b<=3:
        for pl in list(permutations(range(a)))[:3]:
            for pr in list(permutations(range(b)))[:3]:
                oldL={tuple(sorted((pl[u],pl[v]))) for u,v in eL}
                oldR={tuple(sorted((pr[u],pr[v]))) for u,v in eR}
                idxOldL=[0]*a;idxOldR=[0]*b
                for u in range(a):idxOldL[pl[u]]=idxL[u]
                for u in range(b):idxOldR[pr[u]]=idxR[u]
                valOldL=canonical(a,oldL,idxOldL)
                valOldR=canonical(b,oldR,idxOldR)
                for u in range(a):
                    assert valOldL[pl[u]] == sum(
                        1<<pl[v] for v in range(a) if vl[u]>>v & 1)
                for u in range(b):
                    assert valOldR[pr[u]] == sum(
                        1<<pr[v] for v in range(b) if vr[u]>>v & 1)
                stats["relabel_checks"]+=1

for p in range(3):
    for l in range(4-p):
        for r in range(4-p-l):
            a=p+l; b=p+r
            ml=max(1,a+1); mr=max(1,b+1)
            for cL in range(1<< (a*(a-1)//2)):
                eL=graph_edges(a,cL)
                for cR in range(1<< (b*(b-1)//2)):
                    eR=graph_edges(b,cR)
                    if {e for e in eL if e[0]<p and e[1]<p} != {
                        e for e in eR if e[0]<p and e[1]<p}:
                        continue
                    for idxL in product(range(ml),repeat=a):
                        if not steps(a,eL,idxL,ml):continue
                        for idxR in product(range(mr),repeat=b):
                            stats["pairs"]+=1
                            check(p,l,r,eL,idxL,ml,eR,idxR,mr)

# Non-singleton minimal strong top component: K4 over one named
# base vertex. A new block of three vertices is minimal strong.
K4=graph_edges(4, (1<<6)-1)
assert minimal(4,K4,1,15)
check(1,3,0,K4,(0,1,1,1),5,set(),(0,),2)

assert stats["valid_pairs"]>0 and stats["full_value_checks"]>0
print("C0 arbitrary-base full functional amalgam check:",stats)
