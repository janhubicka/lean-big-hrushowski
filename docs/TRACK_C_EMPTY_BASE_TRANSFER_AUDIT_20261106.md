# Track C — the empty-base condition is not independent on the countable limit

The manuscript assumes the empty substructure is strictly
d-closed inside **each finite C_F member**. Under full
growth-class membership of all finite induced subgraphs
of a countable comparison graph N, the corresponding
**globally** strictly d-closed empty-base condition is automatic.

## Exact proof

For an arbitrary finite b⊆ℕ, take the *literal* induced
subtype `{v : ℕ // v∈b}` with its exact graph. The global
finite growth inequality on N implies that this complete
finite subtype is in C_F (the already validated
`CFDClosedFiniteSubtype.growthSparse_iff`).
Apply the independent finite-class empty-base hypothesis to
get ∅≤_d b in the subtype. Transport the resulting strict
finite predimension inequalities back to b using the
verified `CFDClosedFiniteSubtype.dClosed_iff`.
Take the full b as the proper extension in the resulting
strict inclusion. Since b was arbitrary, ∅ is globally
strictly d-closed in N.

No finite covers, free amalgamation, infinitude, continuity,
or countable Fraisse property enter this lemma.

## Internal adversarial panel

- **Local/global referee:** a statement about ∅≤_d only one
  selected stage is insufficient. This proof explicitly
  quantifies over every finite b and transports the
  finite-subtype relation back to the ambient graph.
- **Strictness referee:** `IsDClosed` is strict on every
  proper intermediate extension; `IsStrong` alone cannot
  establish the conclusion.
- **Class referee:** the hypothesis covers all finite
  growth-class graphs; it is *not* inferred from F(0)=0.
  The comparison graph must have the full growth inequality
  on every finite subset.
- **Finite-bound referee:** no new size bound, cardinal
  inverse or class-amalgamation premise is introduced.
- **Nonedge referee:** the induced subtype uses the complete
  graph, so the proof does not replace the source with an
  edge-preserving homomorphic image.
- **Generic referee:** the derived property removes one
  separate target hypothesis from the already proved
  birth-graph recognition theorem. It does not establish
  the birth-carrier infinitude or the identity of the
  published M_F on its own.
- **Certification referee:** the two new endpoints are
  reviewed on their exact isolated Lean build and axiom
  registry; the umbrella build alone is not sufficient.

At creation CI is pending, and the full manuscript lemma
remains unpromoted. This is internal role-separated
adversarial checking, not external human refereeing.
