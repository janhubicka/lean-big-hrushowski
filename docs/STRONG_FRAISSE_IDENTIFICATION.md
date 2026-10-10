# Identifying the constructed graph with the strong Fraïssé limit

**Status:** mathematical proof programme and adversarial audit;
not yet a Lean theorem. The existence of a concrete countable generic
graph is developed in PR #48 and must pass the full axiom audit before
its theorem names are used below.

## Strong-age uniqueness theorem

Let (M) and (N) be graphs on countably infinite sets satisfying:

1. every finite vertex set has nonnegative predimension
   (delta(X)=2|X|-|E(X)|);
2. every finite set is contained in a finite globally self-sufficient set;
3. every finite strong embedding (A\leq B) of two finite two-sparse
   graphs can be realized over any induced globally strong embedding
   of (A) into the graph.

Then (M) and (N) are isomorphic. Indeed, every isomorphism between
finite globally strong induced subgraphs of one of the graphs extends
to an automorphism of that graph.

Here “globally strong” means (A\leq C) for every finite induced
subgraph (C) containing (A). Finite strong covers are essential:
an arbitrary finite induced subgraph need not be self-sufficient.

## One finite forth extension

Suppose (p:A\to A') is an induced graph isomorphism between finite
globally strong subgraphs (A\subseteq M) and (A'\subseteq N).
Given a vertex (v\in M), choose a finite globally strong
(C\subseteq M) containing (A\cup\{v\}). Since (A) is globally
strong, (A\leq C). Apply the strong extension property of (N)
to the induced strong embedding (A\hookrightarrow C) and the
globally strong copy (p:A\to N). We obtain an induced embedding
(q:C\to N) extending (p), with globally strong image (q[C]).
Consequently the restriction of (q) is a new finite strong partial
isomorphism whose domain contains (v).

Interchanging (M,N) and taking the inverse partial map gives the
corresponding back extension.

## Back-and-forth

Fix enumerations (m_0,m_1,\ldots) and (n_0,n_1,\ldots) of
(M) and (N). Begin with any finite strong partial isomorphism,
in particular the empty map. The empty set is globally strong
because both graphs are two-sparse.

At even stage (2k), perform a forth extension including (m_k).
At odd stage (2k+1), perform a back extension including (n_k).
The finite maps form an increasing chain of induced partial
isomorphisms. Their union is a bijection, and every pair of
vertices occurs together in one finite domain. Both edges and
nonedges are preserved. Thus the union is an isomorphism.
Starting with an arbitrary finite strong partial isomorphism proves
the asserted strong homogeneity.

No finite bound on strong closures is used.

## Lean implementation interface

The existing theorem
`FiniteCatalogue.arbitrary_finite_strong_extension` supplies
the required forth step for arbitrary finite vertex types.

The existing `StrongChain.contains_finite` and
`StrongChain.stage_global` supply a finite globally strong
container in a coherent strong union. Alternatively, use
`StrongExhaustion.closure_global` to take the least such container.

A maintainable development should introduce:

- `FiniteStrongPartialIso M N` with finite source and target
  subsets, an equivalence of their induced vertex types, induced
  adjacency preservation, and global strongness of both domains;
- a `forth` lemma enlarging the source to contain a prescribed
  vertex, using the arbitrary finite extension theorem;
- a `back` lemma by applying `forth` to the inverse partial map;
- a coherent recursion alternating the two operations;
- totality, surjectivity, and induced-graph equivalence of the union.

Reuse `GraphOn.pullback` for graph structures on finite subtype
carriers, and `GraphOn.strong_image_iff` for the transfer of
self-sufficiency. The image of each finite subtype equivalence
must be shown equal to the corresponding underlying finite set,
rather than silently treated as definitionally equal.

The standard relational Fraïssé formalization in Mathlib,
`Mathlib/ModelTheory/Fraisse.lean`, is useful background but does
not directly supply the strong-embedding theorem for this graph
class. An independent back-and-forth proof avoids prematurely
replacing strong embeddings by ordinary relational embeddings.

## Adversarial verification questions

**Referee A — relative versus global strongness.** Ensure that the
chosen (C) is globally strong, not only strong in one finite stage,
so that the new range of the partial map has the invariant needed
by later back steps.

**Referee B — induced embeddings.** Verify reflection of nonedges
in the extension property. An edge-preserving homomorphism is
insufficient for the back-and-forth union to be an isomorphism.

**Referee C — finite containers.** Do not assume (A\cup\{v\})
is strong. It must first be enclosed in a finite globally strong
subgraph; no uniform closure-size bound is available for
`C0`.

**Referee D — coverage.** Alternate forth and back requirements.
Only extending domains does not ensure surjectivity, even when all
partial maps remain strong and induced.

**Referee E — no circularity.** The construction of a countable
generic graph must be completed independently before its strong
extension property is used as an input here. The uniqueness theorem
should take existence of the two graph structures as assumptions.

These are five logically distinct mathematical adversarial checks
performed in one review, not independently spawned referee agents.
