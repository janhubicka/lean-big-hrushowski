#!/usr/bin/env python3
"""Full finite C0 functional lifting across arbitrary induced embeddings.

Enumerate small target graphs, every injective map from a finite old
vertex set (in an independently labelled order) into its target, and
every old canonical presentation by minimal strong components.
Whenever the old image is strong, free fresh-block factorisation
produces an indexed target presentation. Check minimality and exact
image equality of complete old unary closures.

Also test relabel invariance under arbitrary permutations, including
old graphs with several vertices in a component.
"""
from itertools import combinations, permutations, product

def edges_of(n,bits):
    es=list(combinations(range(n),2))
    return [e for j,e in enumerate(es) if bits & (1<<j)]

def delta(edges,s):
    return 2*s.bit_count()-sum(bool(s&(1<<u)) and bool(s&(1<<v))
                             for u,v in edges)

def strong(edges,a,b):
    if a & ~b:return False
    z=rest=b&~a
    while True:
        if delta(edges,a)>delta(edges,a|z):return False
        if z==0:return True
        z=(z-1)&rest

def minimal(edges,a,b):
    if a==b or not strong(edges,a,b):return False
    z=rest=b&~a
    while True:
        c=a|z
        if c not in (a,b) and strong(edges,c,b):return False
        if z==0:return True
        z=(z-1)&rest

def values(edges,labels,nslots,size,selected):
    comp=[sum(1<<u for u in range(size) if
              selected&(1<<u) and labels[u]==k) for k in range(nslots)]
    deps=[set() for _ in range(nslots)]
    for u,v in edges:
        if not(selected&(1<<u) and selected&(1<<v)):continue
        i,j=labels[u],labels[v]
        if i>j:deps[i].add(j)
        elif j>i:deps[j].add(i)
    ans=[]
    for i in range(nslots):
        reached,queue={i},[i]
        for j in queue:
            for k in deps[j]:
                if k not in reached:reached.add(k);queue.append(k)
        ans.append(sum(comp[k] for k in reached))
    return ans

def chain(edges,a,b):
    blocks=[]
    while a!=b:
        opts=[c for c in range(b+1)
              if c&~b==0 and c&a==a and c!=a and strong(edges,c,b)]
        assert opts
        c=min(opts,key=lambda z:(z.bit_count(),z))
        assert minimal(edges,a,c)
        blocks.append(c&~a)
        a=c
    return blocks

graphs=injections=strong_embeddings=canonical_old_presentations=old_value_equalities=steps=nontrivial=0
for nw in range(5):
    full=(1<<nw)-1
    for bits in range(1 << (nw*(nw-1)//2)):
        target_edges=edges_of(nw,bits);graphs+=1
        for nu in range(nw+1):
            for inj in permutations(range(nw),nu):
                injections+=1
                image=sum(1<<x for x in inj)
                if not strong(target_edges,image,full):continue
                strong_embeddings+=1
                source_edges=[(u,v) for u in range(nu) for v in range(u+1,nu)
                              if tuple(sorted((inj[u],inj[v]))) in target_edges]
                blocks=chain(target_edges,image,full)
                nontrivial+=len(blocks)>1
                for nslots in range(4):
                    if nslots==0 and nu:continue
                    for old_labels in product(range(nslots),repeat=nu):
                        stages=[sum(1<<u for u,k in enumerate(old_labels)
                                    if k<j) for j in range(nslots+1)]
                        if any(a!=b and not minimal(source_edges,a,b)
                               for a,b in zip(stages,stages[1:])):continue
                        canonical_old_presentations+=1
                        labels=[nslots]*nw
                        for u,ku in enumerate(old_labels):
                            labels[inj[u]]=ku
                        for j,B in enumerate(blocks):
                            for v in range(nw):
                                if B&(1<<v):labels[v]=nslots+j
                        all_stages=[sum(1<<v for v,k in enumerate(labels) if k<j)
                                    for j in range(nslots+len(blocks)+1)]
                        assert all_stages[-1]==full
                        assert all_stages[nslots]==image
                        assert all(a==b or minimal(target_edges,a,b)
                                   for a,b in zip(all_stages,all_stages[1:]))
                        steps+=nslots+len(blocks)
                        val_old=values(source_edges,old_labels,nslots,nu,(1<<nu)-1)
                        val_target=values(target_edges,labels,nslots+len(blocks),nw,full)
                        for u in range(nu):
                            expected=sum(1<<inj[v] for v in range(nu)
                                         if val_old[old_labels[u]]&(1<<v))
                            assert val_target[labels[inj[u]]]==expected, (
                                "embedded f_cl changed",target_edges,inj,old_labels,blocks,u)
                            old_value_equalities+=1
assert all(c>0 for c in [injections,strong_embeddings,canonical_old_presentations,
                         old_value_equalities,nontrivial])
print({"target_graphs":graphs, "injective_maps":injections,
       "strong_induced_embeddings":strong_embeddings,
       "canonical_old_presentations":canonical_old_presentations,
       "multiblock_spans":nontrivial, "indexed_steps":steps,
       "old_unary_image_equalities":old_value_equalities})
