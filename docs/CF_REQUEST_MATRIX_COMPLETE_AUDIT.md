# Adversarial audit: complete local C_F ordered adjacency matrix
28 October 2026

## Statement

For an actual StageRequest r with literal support P, local new
block size n, and full local graph on P⊕Fin n, the list of
coordinates consists of all old vertices of P in their
inherited increasing order followed by all new Fin indices
in their chosen order. Every coordinate appears.

The complete row-major zero/one matrix on this list uniquely
determines the local graph, *once P and n are fixed*. The
matrix includes all edges and nonedges, not only the old-fresh
boundary.

## Hostile mathematical checks

1. The old coordinate subtype is the actual named P; no
   arbitrary isomorphic copy or quotient of its vertices is
   introduced.
2. The old coordinate sort uses the inherited stage order,
   exactly as the manuscript prescribes.
3. The fresh coordinate sort uses the natural order on Fin n,
   hence records the chosen ordered fresh block.
4. The list contains every old and fresh vertex. The generic
   matrix injectivity lemma has precisely this completeness
   hypothesis, not a hidden global enumeration assumption.
5. The empty old support is permitted. The fresh part remains
   nonempty for minimal extensions, but completeness itself
   works even for n=0.
6. Edges inside the fresh block are included, so graph codes
   with identical boundary masks are not conflated.
7. Old-old edges are included even though the support graph
   fixes them; this harmless redundancy is the full matrix
   convention now specified in the manuscript.
8. The code includes zero bits for absent edges; preserving
   only the positive edge count would not yield injectivity.
9. Same-carrier injectivity does not yet prove equality of
   two dependent StageRequest records. One must first
   recover the named support and fresh size, then transport
   both graph codes to the same local carrier.
10. The comparison of code lists is the standard lexicographic
    comparison. The graph injection theorem is purely an
    equality assertion and does not rely on numeric ranking.
11. The result introduces no growth, d-closure, Fraisse or
    Ramsey hypotheses beyond those already in the request
    record; it is a finite coding fact.
12. The full manuscript-order marker remains PARTIAL until
    dependent request-key injectivity, strict totality and
    stage-order coherence are assembled. Each individual
    new endpoint requires exact Lean CI and axiom checks.

These are internal role-separated adversarial reviews.
