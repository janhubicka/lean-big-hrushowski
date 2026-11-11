# Track B — prescribed-level preorder and complete finite block images (11 November 2026)

## Statement and scope

The already merged finite `C_F` existence theorem constructs one map on
the original finite birth-block-closed source. Its images have exactly the
assigned birth levels, and the assignment is strictly increasing on the
**represented source birth levels**, not necessarily on all natural numbers.

This patch records a further invariant of that same map:

1. The entire **weak birth-level preorder** is preserved and reflected.
2. The original existential theorem can include this preorder without
   changing the witness or making a second choice of finite map.
3. Combining that preorder with the complete birth-`b` image and the
   *partial* rigidity theorem yields equality of images of each **entire
   literal old support** and **entire literal birth block**.

These are finite structural facts on the actual birth-labelled graph. They
do not yet prove order preservation, exact `R,H` transport, uniqueness
among arbitrary functional embeddings, or the infinite embedding-monoid
identification.

## Role-separated adversarial referee panel

**Referee A — represented levels.** The converse implication
`level(a) ≤ level(b) ⇒ a ≤ b` uses strict increase at both represented
levels. If `b<a`, strict increase yields `level(b)<level(a)`, a
contradiction. Unused levels are never compared. An extension of the level
assignment to a strictly increasing function on all of ℕ would be an
unjustified extra assumption and is not introduced.

**Referee B — same witness.** The stronger existence conclusion applies
to the same `finiteSourcePrescribedLift`, whose exact labels, graph
inducedness and complete `b` values were independently proved. It does
not combine separately chosen witnesses.

**Referee C — genuine partial-domain support images.** The block/support
conclusion applies `finitePartial_birthSupport_block_of_preorder` to the
literal subtype `{v // v∈s}`. Complete `b` images refer to the full
actual values because `s` is birth-block-closed. It does **not** extend
the finite map to all vertices and does **not** assume surjectivity onto
target blocks: this is a conclusion of the rigidity theorem.

**Referee D — negative controls.** Strict monotonicity merely on some
smaller collection of source levels would not reflect the preorder on
the missing represented levels. Merely preserving (rather than exactly
transporting) complete `b` values also fails to force target block
surjectivity. A source cut not closed under the whole fresh block
invalidates the complete-value premise.

**Referee E — Lean gate.** The requested certification is exact-head
`lake build BigHrushovski.CFPrescribedLevelPreorder`, followed by
`lake env lean CheckAxiomsCFTrackBLevelPreorder.lean`,
`scripts/check_axioms.py`, and the repository-wide placeholder scan.
The umbrella workflow discovers the new check module automatically.
Do not call this kernel-certified until its exact-head workflow succeeds.

**Referee F — manuscript discipline.** No paper validation marker is
promoted. The finite uniqueness statement still needs reconstruction
of every target request tag, identification of internal ordinals, and
induction that compares an *arbitrary* admissible embedding with the
canonical one, including source and target gaps. The order bridge is
also needed before importing the (R,H)-equivalence theorem.

## Immediate next lemma

At each represented source level, let two finite admissible maps agree
on the earlier selected source cut and have the same prescribed target
birth labels. The already proved complete support/block images, full
induced graph, and literal support-order/adjacency code transport must
identify their target request tags, using
`transportGrowthStageRequest_partial_unique`. The
`birthOrdinal_image_on_closedSet_of_canonicalOrder` rigidity supplies
the fresh ordinal once the closed-source order interface is in place.
Induct over represented source levels, not all intervening levels.

The exact equivalence between the chosen canonical birth order and the
finite-stage order remains an obligation; it cannot be replaced by
ordinal monotonicity inside one block alone.
