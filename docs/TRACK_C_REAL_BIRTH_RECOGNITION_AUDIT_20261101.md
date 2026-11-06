# Track C — induced recognition of actual birth vertices

This is a source-level composition of independently verified,
merged results: #300 (nonempty requests give an infinite,
countable birth carrier), #302 (exact Nat strict genericity)
and #291 (global strict d-closed relabelling).

The final theorem is a genuine induced equivalence between the
*actual* birth-labelled graph and an arbitrary countable graph
on ℕ satisfying the exact strict C_F finite recognition data.
No larger ambient graph, quotient of birth vertices, totalization
of a partial source embedding or abstract unnamed isomorphism
is assumed.

## Internal adversarial referee panel

- **Carrier referee:** `natEquivBirth_of_requests` requires
  at least one actual StageRequest per finite level; this is
  stronger than the countability theorem and follows from no
  numerical assumption by itself.
- **Class referee:** restricted free-amalgamation closure is
  explicit in hFree; monotonicity and unboundedness of F are
  not used to infer it.
- **Embeddings referee:** the equivalence is constructed by
  composing two genuine bijections, and its adjacency statement
  is an iff, so nonedges are reflected.
- **Generic referee:** the comparison graph N has the complete
  finite growth inequality, strict closed covers, prescribed
  finite extension responses and globally d-closed empty base;
  these are not omitted or silently equated with 2-sparsity.
- **Certification referee:** the new endpoint requires an
  independent Lean build and exact `#print axioms`; a passing
  dependency build alone does not certify the composite statement.

## Remaining manuscript-facing assumptions

1. Prove from the **published** one-vertex class-membership and
   empty-base d-closedness hypotheses that each finite level has
   a literal permitted StageRequest. Do not add a stronger
   assumption to the paper merely to make the formalization work.
2. Give the countable graph denoted M_F the exact finite
   recognition property in Lean, or explicitly use the paper's
   strong Fraisse characterization to instantiate the target N.
3. Specialize the present real-domain F to the published
   nonnegative-domain F via the exact adapter (#277);
   PR #311 handles the Nat-pullback specialization separately.

Status: submitted for isolated CI. The full manuscript lemma is
not yet marked verified. This review is internal and role-separated,
not an external human referee panel.
