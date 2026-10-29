# Adversarial audit: actual named C_F request construction

29 October 2026

## New assertion

A source StageRequest r over a finite old graph G has a literal
support P and a bounded complete ordered local graph on P + Fin n.
Suppose P is contained in a selected old source S and a map f is
strictly increasing on S. Let Q=f[P]. If the old graph on P is
induced by f in the target old graph H, and Q is strictly d-closed
in H, there is an actual target StageRequest with support Q,
the same fresh size n and the transported full local graph.

No embedding of all of G's old vertices is assumed. No extra
numerical size bound is needed: the canonical order isomorphism
P ≃o Q proves |P|=|Q|, so the source's bound n ≤ K(|P|)
is exactly the target bound n ≤ K(|Q|).

## Role-separated hostile checks

1. **Predimension referee.** The target support must be
   d-closed in the entire target old stage, not just in
   the image of S. This remains an explicit hypothesis,
   discharged later by the selected-source d-closedness
   and induced support transport. Strict monotonicity
   alone does not establish d-closedness.

2. **Graph-code referee.** The local graph is relabelled by
   the *literal* support equivalence, and the fresh Fin
   ordinals are fixed. The previous named-base transport
   lemmas prove growth membership, minimal strict d-closedness
   and the exact canonical support in both directions.
   The complete adjacency matrix still needs an explicit
   theorem connecting the constructed target request to
   the source code.

3. **Size-bound referee.** The source request's dependent
   index is a Fin (K(|P|)+1), hence n ≤ K(|P|).
   Because the support equivalence is bijective,
   |Q|=|P| even when f is not globally injective.
   No monotonicity of K is used or required.

4. **Order referee.** The support order isomorphism uses
   strict monotonicity only on the selected old source.
   No global order embedding U_t → U_s is introduced.
   Empty supports are permitted and require no
   distinguished old vertex.

5. **Lean referee.** The exact theorem endpoints in
   CheckAxioms.lean and the full build, axiom audit,
   placeholder scan and finite regressions must all pass
   on the same commit before certification.

## Remaining obligations

Prove that the actual target request's complete adjacency
matrix equals the source request's matrix (using the
complete coordinate theorem), then derive its precise
request-key transport and noncollision with other requests.
After that, assemble all selected same-level blocks into
one induced, d-closed and ordered map. The finite unique
level-lifting theorem and embedding-monoid identification
remain unverified.

These are separate adversarial mathematical perspectives
within the project, not reports by independent human referees.
