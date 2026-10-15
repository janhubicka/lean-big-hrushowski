import BigHrushovski.CFBatchLocalInduced
import BigHrushovski.CFLocalSupportTransport

/-!
# Exact finite vertex sets of tagged C_F stage blocks

A one-level tagged construction keeps the old stage literally, and
for each *actual* local-type request r adds precisely the vertices
(r,i) indexed by its finite ordered increment.

We identify the images of a local code's old and fresh vertex sets
with the actual support in the stage and its own fresh tagged block.
These identities allow the already-certified transport theorems to
give minimal d-closedness and the *exact* old-neighbour support in
each finite induced local image.

The statements do not yet claim that the original old stage is
d-closed in the *whole* simultaneous stage. This remains the
multi-block induction obligation.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- All old vertices, retaining their original names. -/
noncomputable def taggedOldDomain
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    Finset (LevelCarrier G Allowed bound) :=
  (Finset.univ : Finset U).image Sum.inl

/-- The actual old vertices of a request's closed support. -/
noncomputable def taggedSupport
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    Finset (LevelCarrier G Allowed bound) :=
  r.support.image Sum.inl

/-- The fresh vertices of one particular request, with their own
tag, even if a different request has the same abstract local type. -/
noncomputable def taggedBlock
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    Finset (LevelCarrier G Allowed bound) :=
  (Finset.univ : Finset (Fin r.code.1.val)).image
    (fun i => (Sum.inr ⟨r, i⟩ : LevelCarrier G Allowed bound))

/-- The old vertices of the normalized local code map *exactly*
onto its actual named support, rather than an arbitrary isomorphic
copy of that support. -/
theorem localOld_image_eq_taggedSupport
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    ((CFLocalCatalogue.oldVertices
        (SupportCarrier U r.support) r.code.1.val).image
      (localTag G Allowed bound r)) =
        taggedSupport G Allowed bound r := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
    obtain ⟨p, _, hpv⟩ := Finset.mem_image.mp hv
    subst v
    exact Finset.mem_image.mpr
      ⟨p.val, p.property, hvz⟩
  · intro hz
    obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr
      ⟨Sum.inl ⟨u, hu⟩, ?_, huz⟩
    exact Finset.mem_image.mpr
      ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩

/-- The normalized fresh block maps onto the corresponding
request-tagged fresh vertices, with no renaming of its indices. -/
theorem localFresh_image_eq_taggedBlock
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    ((CFLocalCatalogue.freshVertices
        (SupportCarrier U r.support) r.code.1.val).image
      (localTag G Allowed bound r)) =
        taggedBlock G Allowed bound r := by
  classical
  simp only [CFLocalCatalogue.freshVertices, taggedBlock,
    Finset.image_image]
  rfl

/-- The complete induced local graph is carried by its old
support and its own fresh block, and no additional vertices. -/
theorem localUniv_image_eq_support_union_block
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    ((Finset.univ : Finset
        (Sum (SupportCarrier U r.support) (Fin r.code.1.val))).image
      (localTag G Allowed bound r)) =
        taggedSupport G Allowed bound r ∪
          taggedBlock G Allowed bound r := by
  classical
  rw [← CFLocalCatalogue.old_union_fresh
    (SupportCarrier U r.support) r.code.1.val]
  rw [Finset.image_union,
    localOld_image_eq_taggedSupport,
    localFresh_image_eq_taggedBlock]

/-- No fresh vertex can coincide with an old vertex. -/
theorem taggedBlock_disjoint_old
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    Disjoint (taggedOldDomain G Allowed bound)
      (taggedBlock G Allowed bound r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hOld hNew
  obtain ⟨u, _, huz⟩ := Finset.mem_image.mp hOld
  obtain ⟨i, _, hiz⟩ := Finset.mem_image.mp hNew
  exact (Sum.noConfusion (huz.trans hiz.symm))

/-- Fresh blocks of two different requests are disjoint,
even when their supports and ordered graphs are isomorphic. -/
theorem taggedBlocks_disjoint
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : Requests G Allowed bound) (hrs : r ≠ s) :
    Disjoint (taggedBlock G Allowed bound r)
      (taggedBlock G Allowed bound s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hr hs
  obtain ⟨i, _, hiz⟩ := Finset.mem_image.mp hr
  obtain ⟨j, _, hjz⟩ := Finset.mem_image.mp hs
  have heq : (⟨r,i⟩ : FreshCarrier G Allowed bound) =
      (⟨s,j⟩ : FreshCarrier G Allowed bound) :=
    Sum.inr.inj (hiz.trans hjz.symm)
  exact hrs (congrArg Sigma.fst heq)

/-- Each support lies inside the literally retained old stage. -/
theorem taggedSupport_subset_old
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    taggedSupport G Allowed bound r ⊆
      taggedOldDomain G Allowed bound := by
  classical
  exact Finset.image_mono _ (Finset.subset_univ r.support)

/-- A named support d-closed in the old graph remains d-closed
in the *finite induced image* of the old stage inside the
tagged batch graph. -/
theorem taggedSupport_dClosed_old
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedSupport G Allowed bound r)
      (taggedOldDomain G Allowed bound) := by
  classical
  exact (G.dClosed_image_iff (levelGraph G Allowed bound)
    Sum.inl Sum.inl_injective
    (fun u v => (levelGraph_old_iff G Allowed bound u v).symm)
    r.support Finset.univ (Finset.subset_univ _)).mpr r.supportClosed

/-- Each normalized local request is minimal in its complete
finite induced copy inside the batch, expressed using the
actual named support and its fresh tagged block. -/
theorem taggedLocal_minimal
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    (levelGraph G Allowed bound).toPredimension.IsMinimalDClosedStep
      (taggedSupport G Allowed bound r)
      (taggedSupport G Allowed bound r ∪
        taggedBlock G Allowed bound r) := by
  have h := levelGraph_local_minimal_image G Allowed bound r
  rw [localOld_image_eq_taggedSupport,
    localUniv_image_eq_support_union_block] at h
  exact h

/-- The copied block retains the **exact** support supplied by
its ordered local type, as computed by strict d-closure of all
old neighbours inside its named support. -/
theorem taggedLocal_exactSupport
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    (levelGraph G Allowed bound).toPredimension.dClosedHull
      ((levelGraph G Allowed bound).oldNeighbourSet
        (taggedSupport G Allowed bound r)
        (taggedBlock G Allowed bound r))
      (taggedSupport G Allowed bound r) =
        taggedSupport G Allowed bound r := by
  classical
  have h :=
    r.code.2.graph.canonicalOldSupport_image
      (levelGraph G Allowed bound)
      (localTag G Allowed bound r)
      (localTag_injective G Allowed bound r)
      (fun u v => (levelGraph_local_adj_iff G Allowed bound r u v).symm)
      (CFLocalCatalogue.oldVertices
        (SupportCarrier U r.support) r.code.1.val)
      (CFLocalCatalogue.freshVertices
        (SupportCarrier U r.support) r.code.1.val)
  rw [r.code.2.exact_support,
    localOld_image_eq_taggedSupport,
    localFresh_image_eq_taggedBlock] at h
  exact h.symm

end CFStageCatalogue
end BigHrushovski
