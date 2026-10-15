import BigHrushovski.CFBatchGrowthMembership

/-!
# Every sub-batch prefix is d-closed in the full finite C_F stage

The simultaneous tagged graph was shown to have U≤d U', where
U is its complete old stage. The argument can be strengthened:
for *any* finite set D of already attached requests, the graph
induced on U together with exactly those blocks is d-closed in
the whole simultaneous graph.

We prove a relative finite induction over fresh request tags.
The induction starts from an arbitrary fixed set D; for a new
request r not in the current set, the support P_r is d-closed
in that prefix by P_r≤d U≤d prefix, and every neighbour of
its fresh block in that prefix belongs to P_r. The one-block
persistence theorem applies and strict transitivity handles
all intermediate sets meeting several old and new blocks.

This lemma is needed to justify the finite factor argument in
the C_F genericity proof: an extension realized with one
particular block remains d-closed after every other request
at the same level has also been attached.

The theorem is graph-theoretic and does not assert countable
genericity or derive the growth-function class free-amalgamation
property from monotonicity of F.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Adding any set of distinct fresh requests produces a
d-closed extension of the existing tagged prefix. -/
theorem taggedBatchPrefix_dClosed_union
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done extra : Finset (Requests G Allowed bound)) :
    Disjoint done extra →
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedBatchPrefix G Allowed bound done)
      (taggedBatchPrefix G Allowed bound (done ∪ extra)) := by
  classical
  let H := levelGraph G Allowed bound
  induction extra using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.union_empty] using
        H.toPredimension.dclosed_refl
          (taggedBatchPrefix G Allowed bound done)
  | @insert r rest hr ih =>
      intro hDisj
      have hRest : Disjoint done rest := by
        apply Finset.disjoint_left.mpr
        intro v hvDone hvRest
        exact (Finset.disjoint_left.mp hDisj)
          hvDone (Finset.mem_insert_of_mem hvRest)
      have hInd := ih hRest
      have hrFresh : r ∉ done ∪ rest := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hDone | hRestMem
        · exact (Finset.disjoint_left.mp hDisj)
            hDone (Finset.mem_insert_self r rest)
        · exact hr hRestMem
      let A := taggedBatchPrefix G Allowed bound (done ∪ rest)
      let P := taggedSupport G Allowed bound r
      let B := taggedBlock G Allowed bound r
      have hP : H.toPredimension.IsDClosed P A :=
        H.toPredimension.dclosed_trans
          (taggedSupport_dClosed_old G Allowed bound r)
          (taggedOld_dClosed_prefix G Allowed bound (done ∪ rest))
      have hFresh : Disjoint A B :=
        taggedBlock_disjoint_prefix G Allowed bound
          (done ∪ rest) r hrFresh
      have hBack : ∀ x ∈ B, ∀ y ∈ A,
          H.adj x y → y ∈ P :=
        taggedBlock_backNeighbours_prefix G Allowed bound
          (done ∪ rest) r hrFresh
      have hStep : H.toPredimension.IsDClosed A (A ∪ B) :=
        (H.minimalLocalDClosed_support_persists
          P A B hP hFresh hBack
          (taggedLocal_minimal G Allowed bound r)
          (taggedLocal_exactSupport G Allowed bound r)).2.1.1
      have hUnion : done ∪ insert r rest =
          insert r (done ∪ rest) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hUnion, taggedBatchPrefix_insert]
      exact H.toPredimension.dclosed_trans hInd hStep

/-- The batch prefix containing an arbitrary subset of the
requests is d-closed in the entire finite tagged graph. -/
theorem taggedBatchPrefix_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done : Finset (Requests G Allowed bound)) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedBatchPrefix G Allowed bound done)
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  classical
  have hDisj : Disjoint done
      ((Finset.univ : Finset (Requests G Allowed bound)) \ done) := by
    apply Finset.disjoint_left.mpr
    intro r hr hRest
    exact (Finset.mem_sdiff.mp hRest).2 hr
  have h := taggedBatchPrefix_dClosed_union
    G Allowed bound done (Finset.univ \ done) hDisj
  have hUnion :
      done ∪ ((Finset.univ : Finset (Requests G Allowed bound)) \ done) =
      Finset.univ := by
    ext r
    simp [Finset.mem_union, Finset.mem_sdiff]
  rw [hUnion, taggedBatchPrefix_univ] at h
  exact h

/-- In particular the original old stage together with one
specific fresh block is d-closed in the entire tagged stage.
This allows a local extension embedded over an old d-closed
substructure to remain closed after the other blocks are added. -/
theorem taggedSingleBlockPrefix_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedOldDomain G Allowed bound ∪
        taggedBlock G Allowed bound r)
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  have h := taggedBatchPrefix_dClosed_full G Allowed bound
    ({r} : Finset (Requests G Allowed bound))
  have hEq : taggedBatchPrefix G Allowed bound
      ({r} : Finset (Requests G Allowed bound)) =
      taggedOldDomain G Allowed bound ∪
        taggedBlock G Allowed bound r := by
    classical
    simp [taggedBatchPrefix]
  rw [hEq] at h
  exact h

end CFStageCatalogue
end BigHrushovski
