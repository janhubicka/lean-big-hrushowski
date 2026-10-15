# Adversarial audit: finite coverage and exact C_F growth in the countable tower

16 October 2026

## Mathematical assertions

The canonical image of U_n in the countable birth carrier is a
finite set StageImage(n). For n <= m, StageImage(n) is contained
in StageImage(m), because the exact old embedding U_n -> U_m
preserves birth labels. Every vertex belongs to a finite stage
image immediately after its birth. Consequently every *finite*
set is covered by one common stage image.

Assuming exact inducedness of every finite stage (PR #159),
the predimension of a finite set is unchanged when computed
inside its covering stage. Therefore, if all finite stages
satisfy delta(X) >= F(|X|), so does every finite vertex set
in the countable graph.

## Five adversarial mathematical checks

1. **Finite versus pointwise coverage.** The assertion
   that every vertex is in some finite stage is insufficient
   on its own to ensure finite-set coverage. The crucial
   extra fact is monotonicity of the stage images. The proof
   explicitly takes the maximum of two stage indices during
   induction on a finite vertex set.

2. **Nonedge reflection.** Transferring predimension needs
   induced graph embeddings, because extra edges decrease
   delta. A forward graph homomorphism is not enough. The
   proof uses the exact stage-induced equivalence of PR #159,
   not just the positive edge-witness lemma of PR #158.

3. **Cardinality.** The canonical stage map is injective,
   so the image has the same finite cardinality and the
   same number of induced unordered edges. The already
   certified growthSparse_image_iff transports the *entire*
   growth predicate, not merely 2-sparsity.

4. **Actual restricted class.** The finite stage membership
   hypothesis is expressed with the actual real-valued
   growth F and explicit restricted d-closed free-amalgamation
   assumption. Monotonicity of F alone does not suffice.
   The second theorem retains an explicit growth-valid
   empty stage and a family of free-join hypotheses.

5. **Not yet the Fraisse generic.** The argument proves
   only the growth inequality for every finite subset.
   It does not prove global strict d-closedness of stage
   images, the minimal-extension property, the singleton
   request (nonstagnation), or the functional block-root
   recovery. Those must be isolated and verified separately.

Any manuscript GREEN marker must be restricted to the
literal finite-cover or growth-transfer statement and
pinned to a passing integrated Lean run (including
standard-axiom and placeholder audits). These are
separated internal adversarial reviews, not independent
external referee-agent reports.
