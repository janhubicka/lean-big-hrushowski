import BigHrushovski.CFBatchLocalInduced
import BigHrushovski.CFDClosedDecomposition

/-!
# Finite iteration of exact minimal d-closed block attachments

One new block B attaches over an old d-closed support P in A
and has no neighbour outside P. We already know it produces
a minimal d-closed step A <_d A∪B with the same exact support.

This module packages the finite *induction* over a list of
such certified successive one-block attachments. It proves
that the original old stage is d-closed in the final carrier
and yields an explicit minimal d-closed chain.

The interface deliberately requires the one-block hypotheses
at every successive prefix. A separate theorem must verify
those hypotheses for the *particular tagged simultaneous graph*
from CFSimultaneousGraph. This generic induction does not by
itself establish class C_F membership or countable genericity.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- The last finite set after successively appending all blocks,
without changing the order of the old vertices. -/
def localBatchEnd (A : Finset V) (blocks : List (Finset V)) :
    Finset V :=
  blocks.foldl (fun old B => old ∪ B) A

/-- A finite chronological list of local minimal d-closed
attachments. Each fresh block is disjoint from its current
old prefix and has all its old neighbours in one prescribed
strictly d-closed support. The support is recovered exactly
from those neighbours. -/
inductive IsLocalDClosedBatchRun :
    Finset V → List (Finset V) → Prop where
  | nil (A : Finset V) : IsLocalDClosedBatchRun A []
  | cons {A P B : Finset V} {rest : List (Finset V)}
      (hSupportClosed : G.toPredimension.IsDClosed P A)
      (hDisj : Disjoint A B)
      (hBack : ∀ u ∈ B, ∀ v ∈ A, G.adj u v → v ∈ P)
      (hMinimal : G.toPredimension.IsMinimalDClosedStep P (P ∪ B))
      (hExactSupport : G.toPredimension.dClosedHull
        (G.oldNeighbourSet P B) P = P)
      (hTail : IsLocalDClosedBatchRun (A ∪ B) rest) :
      IsLocalDClosedBatchRun A (B :: rest)

/-- Every certified chronological finite batch gives a
chain of nontrivial minimal d-closed steps. This uses the
existing one-block persistence theorem at each induction
step rather than repeating any predimension calculation. -/
theorem IsLocalDClosedBatchRun.toMinimalChain
    {A : Finset V} {blocks : List (Finset V)}
    (h : G.IsLocalDClosedBatchRun A blocks) :
    Predimension.MinimalDClosedChain G.toPredimension
      A (G.localBatchEnd A blocks) := by
  induction h with
  | nil A =>
      exact Predimension.MinimalDClosedChain.refl A
  | @cons A P B rest hP hDisj hBack hMin hExact hTail ih =>
      have hStep : G.toPredimension.IsMinimalDClosedStep A (A ∪ B) :=
        (G.minimalLocalDClosed_support_persists
          P A B hP hDisj hBack hMin hExact).2.1
      change Predimension.MinimalDClosedChain G.toPredimension
        A (G.localBatchEnd (A ∪ B) rest)
      exact Predimension.MinimalDClosedChain.step hStep ih

/-- The original old stage is *strictly d-closed* in the
whole finite batch. Unlike a pairwise assertion, this
quantifies over every intermediate vertex set, including
those meeting several different added blocks. -/
theorem IsLocalDClosedBatchRun.old_dClosed_final
    {A : Finset V} {blocks : List (Finset V)}
    (h : G.IsLocalDClosedBatchRun A blocks) :
    G.toPredimension.IsDClosed
      A (G.localBatchEnd A blocks) := by
  induction h with
  | nil A =>
      exact G.toPredimension.dclosed_refl A
  | @cons A P B rest hP hDisj hBack hMin hExact hTail ih =>
      have hStep : G.toPredimension.IsDClosed A (A ∪ B) :=
        (G.minimalLocalDClosed_support_persists
          P A B hP hDisj hBack hMin hExact).2.1.1
      change G.toPredimension.IsDClosed
        A (G.localBatchEnd (A ∪ B) rest)
      exact G.toPredimension.dclosed_trans hStep ih

end GraphOn
end BigHrushovski
