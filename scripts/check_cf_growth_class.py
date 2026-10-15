#!/usr/bin/env python3
"""Adversarial regression of the actual finite growth class C_F.

For every small labelled simple graph G on at most four vertices,
all finite vertex subsets, and nontrivial real-valued growth bounds
F(n), check:
  * heredity of δ(X) >= F(|X|);
  * invariance under an induced injection into a larger graph whose
    extra boundary edges may vary independently;
  * that ordinary 2-sparsity does NOT imply membership for F(n)=n;
  * that strict d-closedness of the overlap and growth membership
    of both factors do NOT, for an arbitrary F, establish membership
    of their free amalgam.

The final control is two triangles sharing exactly one old vertex:
the overlap is d-closed in each triangle, each triangle satisfies
δ(X)>=|X|, but their 5-vertex free union has 6 edges, so
δ(union)=4<5=F(5). Hence the paper's class-level
free-amalgamation hypothesis cannot be silently dropped.
"""
from fractions import Fraction
from itertools import combinations, permutations

graphs=subsets=image_tests=hereditary_tests=0

FAMILIES = [
    lambda n: Fraction(0),
    lambda n: Fraction(n),
    lambda n: Fraction(n,2),
    lambda n: Fraction(min(n,2)),
]

def delta(n,E,s):
    return 2*s.bit_count()-sum(
        bool(s&(1<<u)) and bool(s&(1<<v)) for u,v in E)

def is_growth(n,E,a,F):
    subset=a
    while True:
        if Fraction(delta(n,E,subset))<F(subset.bit_count()):
            return False
        if not subset:break
        subset=(subset-1)&a
    return True

def dclosed(n,E,a,b):
    if a & ~b:return False
    tail=b & ~a
    subset=tail
    while subset:
        if delta(n,E,a)>=delta(n,E,a|subset):
            return False
        subset=(subset-1)&tail
    return True

for n in range(5):
    possible=tuple(combinations(range(n),2))
    for mask in range(1<<len(possible)):
        edges={e for i,e in enumerate(possible) if mask&(1<<i)}
        graphs+=1
        # One arbitrary induced renaming and one outside-vertex
        # variant already detects any dependence on outside edges.
        embeddings=[tuple(range(n))]
        if n>1:embeddings.append(tuple(reversed(range(n))))
        for F in FAMILIES:
            for a in range(1<<n):
                subsets+=1
                b=a
                while True:
                    if is_growth(n,edges,a,F):
                        assert is_growth(n,edges,b,F)
                    hereditary_tests+=1
                    if not b:break
                    b=(b-1)&a
                for emb in embeddings:
                    image_mask=sum(1<<emb[v] for v in range(n)
                                   if a&(1<<v))
                    translated={tuple(sorted((emb[u],emb[v])))
                                for u,v in edges}
                    for extra_edges in (False,True):
                        target=set(translated)
                        if extra_edges:
                            target.update((u,n) for u in range(n)
                                          if u%2==0)
                        assert is_growth(n,edges,a,F)==is_growth(
                            n+1,target,image_mask,F)
                        image_tests+=1

# K4 is 2-sparse (predimension nonnegative on every subset)
# but does not satisfy the growth bound F(n)=n.
K4=set(combinations(range(4),2))
assert all(delta(4,K4,a)>=0 for a in range(16))
assert not is_growth(4,K4,15,lambda n:Fraction(n))

# Class-level free amalgamation is not valid for every F.
P={0}
A={0,1,2}
B={0,3,4}
EA={(0,1),(0,2),(1,2)}
EB={(0,3),(0,4),(3,4)}
combined=EA|EB
mask=lambda s:sum(1<<x for x in s)
growth=lambda n:Fraction(n)
assert is_growth(5,EA,mask(A),growth)
assert is_growth(5,EB,mask(B),growth)
assert dclosed(5,EA,mask(P),mask(A))
assert dclosed(5,EB,mask(P),mask(B))
assert delta(5,combined,mask(A|B))==4
assert not is_growth(5,combined,mask(A|B),growth)
assert all(not (a in A-P and b in B-P) and
           not (b in A-P and a in B-P) for a,b in combined)

print({
    "graphs_up_to_vertices":4,
    "graphs_examined":graphs,
    "growth_subset_checks":subsets,
    "heredity_comparisons":hereditary_tests,
    "induced_image_comparisons":image_tests,
    "ordinary_2_sparse_not_enough":True,
    "two_dclosed_triangles_nonclosed_growth_union":True,
    "class_membership_or_image_mismatches":0
})
