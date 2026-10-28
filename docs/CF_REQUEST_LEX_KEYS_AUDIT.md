# Finite C_F request keys — adversarial mathematical audit

28 October 2026

## Exact construction

For a finite old stage U carrying its inherited linear order, every
literal StageRequest r contains a named d-closed support P and an
ordered local graph on P ⊕ Fin n. We extract its key in two parts:

* the increasing tuple of the actual support P, with ordinary
  lexicographic list comparison and the proper-prefix convention;
* the pair (n, adjacency-code), where n is the size of the fresh
  block and the adjacency code is the entire Boolean matrix of
  its local graph read in old-support order followed by fresh
  Fin-ordinal order.

The resulting RequestLexLt implements the manuscript's stated
two-stage comparison *at one finite stage with a chosen old order*.
Its proof interface does not fabricate an arbitrary request rank.
This is not yet a coherent order of the entire infinite birth
carrier, since the old-stage orders must be defined recursively.

## Twelve hostile checks

1. The support tuple is sorted using the inherited old order,
   not an independently chosen Fintype.equivFin order.
2. The standard List Nat/old-vertex linear order is lexicographic,
   including the stated rule for proper initial segments.
3. The local coordinate list first contains **all** old support
   vertices in increasing order, and then **all** fresh Fin n
   vertices in their chosen order.
4. The adjacency code includes internal old-old, old-new,
   new-old and new-new entries; it is not a support-neighbour
   mask alone.
5. The local graph represents a simple undirected graph, so
   repeated symmetric entries do not change information.
6. The fresh size is recorded separately. If the support and
   graph code agree but n differs, the two requests remain
   distinct and have a definite order.
7. Propositional fields `allowed`, `minimal`,
   `exact_support` and `supportClosed` do not contribute
   independent order data; they certify validity of each code.
8. Two requests with the same tuple and size are compared by
   the full adjacency code, precisely as the manuscript says.
9. The proof establishes irreflexivity and the two exact
   comparison-reduction lemmas, but **not yet injectivity** of
   the encoded adjacency matrix or strict totality of the
   request relation. Those are explicit remaining obligations.
10. The construction assumes a finite old stage with
    `[LinearOrder U]`; no compatible recursive order on all
    `stage F K n` has been constructed yet.
11. The later unique-level-lifting argument needs request
    lex comparison to commute with increasing support maps;
    this invariance is not claimed in this PR.
12. Each GREEN marker must refer to an exact compiled
    declaration after full CI, axiom and placeholder scans.
    The manuscript's full global order marker must remain
    PARTIAL until all dependencies have been assembled.

These are internal role-separated adversarial checks, not
independently commissioned human referees.
