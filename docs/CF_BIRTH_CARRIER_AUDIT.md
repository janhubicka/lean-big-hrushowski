# Adversarial audit: birth-labelled countable C_F carrier

16 October 2026

## Construction

Starting from the actual dependent finite tower of PR #155, define
FreshAt(n) to be exactly the request-tagged new vertices of level n.
The countable carrier is the sigma-type

    V = Sigma n : Nat, FreshAt(n).

A stage-n vertex is mapped to the same birth vertex at later
stages. The old inclusion is literally Sum.inl; the new inclusion
Sum.inr fresh has birth index n. The embedded stage U_n contains
precisely vertices born before level n, once surjectivity onto
that initial segment is established in the next lemma.

## Five mathematical referee checks

1. **Old/new collision.** A vertex in stage n has birth index
   strictly less than n, whereas each vertex introduced in the
   successor stage has index exactly n. Hence old and new images
   are disjoint. This supplies a semantic reason for injectivity,
   not just reliance on an abstract equivalence.

2. **Duplicate tags.** A fresh vertex is the dependent pair
   (request, ordinal within that block). Sigma equality retains
   *both* data. Distinct named supports, local types or fresh
   indices can never be identified accidentally.

3. **Stage coherence.** Mapping an old vertex to its birth
   label commutes with every single-step Sum.inl injection by
   definitional equality. This is stronger than choosing a new
   arbitrary numbering of each finite stage, where embeddings
   would require extra coherent bijection choices.

4. **Coverage.** Every birth vertex (n,r) has a canonical
   representative Sum.inr r in stage n+1. This is a proof of
   coverage of the *carrier*, not of any graph property.
   Countability follows from the countable sigma of finite
   fresh layers without a quotient construction.

5. **No hidden genericity.** There is not yet a GraphOn structure
   on this carrier. One must show that the finite induced graph
   adjacencies agree under all stage inclusions and use that
   agreement to define a coherent limit adjacency. Only after
   this can finite d-closed stage inclusions be transported to
   global strict closure and the response property applied.

## Follow-on reusable interface

Define iterated old embeddings into any later stage; prove they
are induced and injective, and compatible with the birth maps.
Then define adjacency of two birth vertices by choosing a
finite stage containing both. Independence of the witness stage
is the key proof obligation. It must not be assumed from
carrier coverage alone.

The result is a conditional formalization milestone; exact
certification requires the Lean build, standard-axiom check,
and placeholder scan. The five referee roles are internal
adversarial analyses, not external human certification.
