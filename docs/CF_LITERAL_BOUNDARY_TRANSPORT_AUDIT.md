# Adversarial audit: literal C_F old-fresh boundary transport

29 October 2026

## Core statement

Let a selected old source S contain a canonical support P, and let
f be injective on S. A prescribed equivalence e:P≃Q has value
e(p)=f(p) and Q is the actual target support. Under the named-base
pullback of the complete local graph, the old-fresh adjacency
criterion is equivalent on both sides for every old u in S and
every fresh ordinal i.

The lemma preserves and reflects nonedges, including the case
u not in P, and does not require f to be defined as an order
embedding on the whole source stage. The fresh-fresh graph
is also unchanged by named-base relabelling.

## Independent hostile mathematical roles

1. **Boundary referee.** The forward direction follows by
   taking q=e(p). In the reverse direction q has the unique
   preimage p=e^{-1}(q); because p is in P⊆S and u∈S,
   injectivity of f on S proves p=u. Without injectivity on
   S, the target could gain an apparent old-fresh edge to a
   different source vertex with the same f-image.

2. **Graph referee.** The proof uses the full induced
   named-base pullback graph, not a homomorphism preserving
   only positive edges. The biconditional includes the
   absence of edges to old vertices outside P and every
   fresh-fresh nonedge.

3. **Finite-catalogue referee.** This is a statement for an
   existing local graph, its support equivalence, and a
   chosen fresh ordinal. It does not manufacture the
   target StageRequest or prove support d-closedness; those
   are already verified by separate modules.

4. **Same-level referee.** The result is sufficient to
   discharge the old-fresh boundary hypothesis in the
   generic simultaneous-batch inducedness theorem once
   the actual target request graph is identified with the
   named-base pullback. It does not introduce an ordering
   or a succession of individual blocks.

5. **Lean review.** Two exact axiom endpoints are registered.
   The statements require a successful complete Lean build,
   standard axiom audit, placeholder scan and finite
   regression suite before certification.

## Remaining scope

The final step is to substitute the actual transported target
request for the generic named-base pullback, with the canonical
fresh Fin cast, and invoke the generic simultaneous-map
inducedness criterion. Verification of the stage order and
block-support function values remains separate.

These are role-separated internal adversarial proof checks,
not reports by external human referees.
