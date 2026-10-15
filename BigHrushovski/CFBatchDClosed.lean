import BigHrushovski.CFTaggedBlockCertificates
import BigHrushovski.CFBatchClosureRun

/-!
# Strict d-closedness of the actual simultaneous tagged C_F graph

The preceding finite certificates identify every local request's
literal old support and fresh block. The tagged graph contains no
edges between different fresh blocks, and every fresh-to-old edge
meets the request's named support.

We prove, by induction over an arbitrary finite set of already
attached request blocks, that the entire original old stage is
strictly d-closed in the induced graph on that prefix. At each
step its original support P is d-closed in the current prefix:
P ≤d old U ≤d current prefix.

The one-block persistence theorem then applies with its *actual*
minimal d-closed local code and exact old-neighbour support.
Strict transitivity handles intermediate sets meeting several
new blocks. At the full request set the prefix is the whole
tagged stage, proving the desired finite old-stage closedness.

This is a graph-predimension theorem; it does not prove that the
restricted growth-function class C_F contains the constructed
simultaneous graph. That separate class-amalgamation assumption is
essential to the paper's countable level construction.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The old stage together with the fresh blocks of a chosen
finite set of requests; other fresh vertices remain outside. -/
noncomputable def taggedBatchPrefix
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done : Finset (Requests G Allowed bound)) :
    Finset (LevelCarrier G Allowed bound) := by
  classical
  exact taggedOldDomain G Allowed bound ∪
    done.biUnion (taggedBlock G Allowed bound)

/-- Inserting a request adds precisely its own fresh block. -/
theorem taggedBatchPrefix_insert
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done : Finset (Requests G Allowed bound))
    (r : Requests G Allowed bound) :
    taggedBatchPrefix G Allowed bound (insert r done) =
      taggedBatchPrefix G Allowed bound done ∪
        taggedBlock G Allowed bound r := by
  classical
  simp [taggedBatchPrefix,
    Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]

/-- Each new request's fresh block is disjoint from an old
prefix containing only different previously attached requests. -/
theorem taggedBlock_disjoint_prefix
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done : Finset (Requests G Allowed bound))
    (r : Requests G Allowed bound) (hr : r ∉ done) :
    Disjoint (taggedBatchPrefix G Allowed bound done)
      (taggedBlock G Allowed bound r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvPrefix hvBlock
  rcases Finset.mem_union.mp hvPrefix with hvOld | hvDone
  · exact (Finset.disjoint_left.mp
      (taggedBlock_disjoint_old G Allowed bound r)) hvOld hvBlock
  · obtain ⟨s, hsDone, hvS⟩ := Finset.mem_biUnion.mp hvDone
    have hsr : s ≠ r := by
      intro hEq
      subst s
      exact hr hsDone
    exact (Finset.disjoint_left.mp
      (taggedBlocks_disjoint G Allowed bound s r hsr)) hvS hvBlock

/-- In a prefix not yet containing r, every edge from its
fresh block to the prefix has its old endpoint in r's
literal support. No old-to-other-block or crossing edge
can contribute a new neighbour. -/
theorem taggedBlock_backNeighbours_prefix
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done : Finset (Requests G Allowed bound))
    (r : Requests G Allowed bound) (hr : r ∉ done) :
    ∀ x ∈ taggedBlock G Allowed bound r,
      ∀ y ∈ taggedBatchPrefix G Allowed bound done,
        (levelGraph G Allowed bound).adj x y →
          y ∈ taggedSupport G Allowed bound r := by
  classical
  intro x hx y hy hAdj
  obtain ⟨i, _, hix⟩ := Finset.mem_image.mp hx
  have hAdj' := hAdj
  rw [← hix] at hAdj'
  rcases Finset.mem_union.mp hy with hyOld | hyDone
  · obtain ⟨u, _, huy⟩ := Finset.mem_image.mp hyOld
    rw [← huy] at hAdj'
    have huSupport : u ∈ r.support :=
      levelGraph_fresh_old_support G Allowed bound r i u hAdj'
    exact Finset.mem_image.mpr ⟨u, huSupport, huy⟩
  · obtain ⟨s, hsDone, hyS⟩ := Finset.mem_biUnion.mp hyDone
    obtain ⟨j, _, hjy⟩ := Finset.mem_image.mp hyS
    have hrs : r ≠ s := by
      intro hEq
      subst s
      exact hr hsDone
    rw [← hjy] at hAdj'
    exact ((levelGraph_no_cross_fresh G Allowed bound r s hrs i j)
      hAdj').elim

/-- Every prefix of the tagged batch contains the original old
stage as a strictly d-closed substructure. This is the genuine
multi-block theorem, not only a pairwise closure assertion. -/
theorem taggedOld_dClosed_prefix
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done : Finset (Requests G Allowed bound)) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedOldDomain G Allowed bound)
      (taggedBatchPrefix G Allowed bound done) := by
  classical
  let H := levelGraph G Allowed bound
  induction done using Finset.induction_on with
  | empty =>
      simpa [taggedBatchPrefix] using
        H.toPredimension.dclosed_refl (taggedOldDomain G Allowed bound)
  | @insert r done hr ih =>
      have hP : H.toPredimension.IsDClosed
          (taggedSupport G Allowed bound r)
          (taggedBatchPrefix G Allowed bound done) :=
        H.toPredimension.dclosed_trans
          (taggedSupport_dClosed_old G Allowed bound r) ih
      have hDisj : Disjoint
          (taggedBatchPrefix G Allowed bound done)
          (taggedBlock G Allowed bound r) :=
        taggedBlock_disjoint_prefix G Allowed bound done r hr
      have hBack : ∀ x ∈ taggedBlock G Allowed bound r,
          ∀ y ∈ taggedBatchPrefix G Allowed bound done,
            H.adj x y → y ∈ taggedSupport G Allowed bound r :=
        taggedBlock_backNeighbours_prefix G Allowed bound done r hr
      have hStep : H.toPredimension.IsDClosed
          (taggedBatchPrefix G Allowed bound done)
          (taggedBatchPrefix G Allowed bound done ∪
            taggedBlock G Allowed bound r) :=
        (H.minimalLocalDClosed_support_persists
          (taggedSupport G Allowed bound r)
          (taggedBatchPrefix G Allowed bound done)
          (taggedBlock G Allowed bound r)
          hP hDisj hBack
          (taggedLocal_minimal G Allowed bound r)
          (taggedLocal_exactSupport G Allowed bound r)).2.1.1
      rw [taggedBatchPrefix_insert]
      exact H.toPredimension.dclosed_trans ih hStep

/-- Attaching *all* finite local requests exhausts the entire
tagged carrier: there are no additional anonymous vertices. -/
theorem taggedBatchPrefix_univ
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    taggedBatchPrefix G Allowed bound
        (Finset.univ : Finset (Requests G Allowed bound)) =
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  classical
  ext v
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    cases v with
    | inl u =>
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩))
    | inr ri =>
        obtain ⟨r, i⟩ := ri
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_biUnion.mpr
            ⟨r, Finset.mem_univ _,
              Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩))

/-- The finite old stage is strictly d-closed in the **entire
actual simultaneous tagged graph** containing every request.
All intermediate subsets, including those meeting different
new blocks, are covered by this theorem. -/
theorem levelGraph_old_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedOldDomain G Allowed bound)
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  have h := taggedOld_dClosed_prefix G Allowed bound
    (Finset.univ : Finset (Requests G Allowed bound))
  rw [taggedBatchPrefix_univ] at h
  exact h

/-- Each request's actual support is d-closed even in the full
finite tagged batch, by transitivity through the old stage. -/
theorem taggedSupport_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedSupport G Allowed bound r)
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  exact (levelGraph G Allowed bound).toPredimension.dclosed_trans
    (taggedSupport_dClosed_old G Allowed bound r)
    (levelGraph_old_dClosed_full G Allowed bound)

end CFStageCatalogue
end BigHrushovski
