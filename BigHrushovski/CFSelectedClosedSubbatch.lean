import BigHrushovski.CFBatchRelativeDClosed
import BigHrushovski.CFClosedFactor

/-!
# Closed selected blocks in a simultaneous C_F level

Let A be a strictly d-closed subset of the old finite stage U.
Select any family D of fresh tagged blocks, all of whose literal
old supports lie in A. Then A together with exactly the selected
fresh blocks is strictly d-closed in the entire new stage.

The proof needs no induction over the selected blocks:
* the selected vertices have no neighbours in U \ A;
* the strict right-factor free-amalgamation lemma gives
  A ∪ B_D ≤d U ∪ B_D;
* arbitrary-prefix strictness gives U ∪ B_D ≤d U', and
  transitivity finishes.

This is the finite step used to show that unions of complete
blocks with all their predecessor supports are d-closed.
It does not identify a countable functional reduct or prove
the block-root recovery identity.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A strictly d-closed old subset, together with an arbitrary
selection of fresh blocks supported entirely inside that subset,
is strictly d-closed in the full simultaneous tagged stage. -/
theorem taggedSupportClosedSubbatch_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done : Finset (Requests G Allowed bound))
    (a : Finset (LevelCarrier G Allowed bound))
    (hOldClosed :
      (levelGraph G Allowed bound).toPredimension.IsDClosed
        a (taggedOldDomain G Allowed bound))
    (hSupports : ∀ r ∈ done,
      taggedSupport G Allowed bound r ⊆ a) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (a ∪ done.biUnion (taggedBlock G Allowed bound))
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  classical
  let H := levelGraph G Allowed bound
  let old := taggedOldDomain G Allowed bound
  let fresh := done.biUnion (taggedBlock G Allowed bound)
  have hDisj : Disjoint old fresh := by
    apply Finset.disjoint_left.mpr
    intro v hvOld hvFresh
    obtain ⟨r, _, hvBlock⟩ := Finset.mem_biUnion.mp hvFresh
    exact (Finset.disjoint_left.mp
      (taggedBlock_disjoint_old G Allowed bound r)) hvOld hvBlock
  have hBack : ∀ x ∈ fresh, ∀ y ∈ old,
      H.adj x y → y ∈ a := by
    intro x hx y hy hAdj
    obtain ⟨r, hr, hxBlock⟩ := Finset.mem_biUnion.mp hx
    have hyPrefix :
        y ∈ taggedBatchPrefix G Allowed bound ∅ := by
      simpa [taggedBatchPrefix, old] using hy
    have hSupport :=
      taggedBlock_backNeighbours_prefix G Allowed bound
        ∅ r (by simp)
        x hxBlock y hyPrefix hAdj
    exact hSupports r hr hSupport
  have hNo : H.NoCrossEdges old (a ∪ fresh) :=
    H.noCross_of_backNeighbours old a fresh hOldClosed.1 hBack
  have hFactor : H.toPredimension.IsDClosed
      (a ∪ fresh) (old ∪ fresh) :=
    H.dClosed_local_right_factor a old fresh
      hOldClosed.1 hDisj hNo hOldClosed
  have hPrefix : H.toPredimension.IsDClosed
      (old ∪ fresh) (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
    simpa [taggedBatchPrefix, old, fresh, H] using
      (taggedBatchPrefix_dClosed_full G Allowed bound done)
  exact H.toPredimension.dclosed_trans hFactor hPrefix

end CFStageCatalogue
end BigHrushovski
