import BigHrushovski.CFNormalizedLocalType
import BigHrushovski.CFGrowthClass

/-!
# Relabelling a local C_F extension over an actual named support

A prescribed finite local extension may be supplied with an old
support P whose vertices are not the literal vertices of the
finite stage in which it is to be realized. An equivalence P ≃ Q
identifies P with the chosen named support Q. Relabel only the
old vertices and fix the complete fresh block B.

This is an induced graph equivalence. It preserves exact
growth-class membership, minimal strict d-closedness of the
local extension, and the canonical old-neighbour support.
It also respects the old graph on Q when the given base
equivalence is an induced graph isomorphism.

There is no countable genericity assertion here. Constructing
the base equivalence from a prescribed finite embedding, and
using the normalized code in the actual level, are downstream.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {P Q B : Type*}
variable [Fintype P] [DecidableEq P]
variable [Fintype Q] [DecidableEq Q]
variable [Fintype B] [DecidableEq B]

/-- Relabel the old support along P ≃ Q, leaving each new
vertex of B unchanged. -/
noncomputable def namedBaseEquiv (e : P ≃ Q) :
    Sum Q B ≃ Sum P B :=
  Equiv.sumCongr e.symm (Equiv.refl B)

/-- Full induced graph under the old-support relabelling. -/
noncomputable def namedBaseGraph (e : P ≃ Q)
    (H : GraphOn (Sum P B)) : GraphOn (Sum Q B) :=
  H.pullback (namedBaseEquiv (B := B) e)

theorem namedBaseGraph_adj_iff (e : P ≃ Q)
    (H : GraphOn (Sum P B)) (x y : Sum Q B) :
    (namedBaseGraph e H).adj x y ↔
      H.adj (namedBaseEquiv (B := B) e x)
        (namedBaseEquiv (B := B) e y) :=
  Iff.rfl

/-- Old vertices are mapped exactly onto the old vertices
of the source local graph. -/
theorem namedBase_old_image (e : P ≃ Q) :
    (actualOld Q B).image (namedBaseEquiv (B := B) e) =
      actualOld P B := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
    obtain ⟨q, _, hqw⟩ := Finset.mem_image.mp hw
    subst w
    exact Finset.mem_image.mpr
      ⟨e.symm q, Finset.mem_univ _, by
        simpa [namedBaseEquiv] using hwz⟩
  · intro hz
    obtain ⟨p, _, hpz⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr
      ⟨Sum.inl (e p), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨e p, Finset.mem_univ _, rfl⟩
    · simpa [namedBaseEquiv] using hpz

/-- Fresh vertices are fixed, not merely permuted, by the
old-support relabelling. -/
theorem namedBase_fresh_image (e : P ≃ Q) :
    (actualFresh Q B).image (namedBaseEquiv (B := B) e) =
      actualFresh P B := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
    obtain ⟨b, _, hbw⟩ := Finset.mem_image.mp hw
    subst w
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_univ _, by
        simpa [namedBaseEquiv] using hwz⟩
  · intro hz
    obtain ⟨b, _, hbz⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr
      ⟨Sum.inr b, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
    · simpa [namedBaseEquiv] using hbz

/-- Changing the names of the old support is an induced
equivalence, hence preserves the whole C_F growth predicate. -/
theorem namedBase_growthSparse_iff
    (F : ℕ → ℝ) (e : P ≃ Q)
    (H : GraphOn (Sum P B)) :
    (namedBaseGraph e H).IsGrowthSparse F Finset.univ ↔
      H.IsGrowthSparse F Finset.univ := by
  classical
  let f := namedBaseEquiv (B := B) e
  have h :=
    (namedBaseGraph e H).growthSparse_image_iff
      H F f f.injective
      (fun x y => namedBaseGraph_adj_iff e H x y)
      (Finset.univ : Finset (Sum Q B))
  rw [Finset.image_univ_of_surjective f.surjective] at h
  exact h.symm

/-- Minimal strict d-closedness of the local step is
preserved and reflected by the named-base change. -/
theorem namedBase_minimal_iff
    (e : P ≃ Q) (H : GraphOn (Sum P B)) :
    (namedBaseGraph e H).toPredimension.IsMinimalDClosedStep
      (actualOld Q B) Finset.univ ↔
    H.toPredimension.IsMinimalDClosedStep
      (actualOld P B) Finset.univ := by
  classical
  let f := namedBaseEquiv (B := B) e
  have h :=
    (namedBaseGraph e H).minimalDClosedStep_image_iff
      H f f.injective
      (fun x y => namedBaseGraph_adj_iff e H x y)
      (actualOld Q B) Finset.univ (Finset.subset_univ _)
  rw [namedBase_old_image, Finset.image_univ_of_surjective f.surjective] at h
  exact h.symm

/-- The canonical old-neighbour support, including the
strict d-closed hull, is preserved under the old-base
relabelling. -/
theorem namedBase_exactSupport_iff
    (e : P ≃ Q) (H : GraphOn (Sum P B)) :
    (namedBaseGraph e H).toPredimension.dClosedHull
      ((namedBaseGraph e H).oldNeighbourSet
        (actualOld Q B) (actualFresh Q B))
      (actualOld Q B) = actualOld Q B ↔
    H.toPredimension.dClosedHull
      (H.oldNeighbourSet (actualOld P B) (actualFresh P B))
      (actualOld P B) = actualOld P B := by
  classical
  let f := namedBaseEquiv (B := B) e
  have hImage :=
    (namedBaseGraph e H).canonicalOldSupport_image
      H f f.injective
      (fun x y => namedBaseGraph_adj_iff e H x y)
      (actualOld Q B) (actualFresh Q B)
  rw [namedBase_old_image, namedBase_fresh_image] at hImage
  constructor
  · intro hEq
    have h := congrArg (fun s : Finset (Sum Q B) => s.image f) hEq
    rw [hImage, namedBase_old_image] at h
    exact h
  · intro hEq
    apply Finset.image_injective f.injective
    calc
      ((namedBaseGraph e H).toPredimension.dClosedHull
          ((namedBaseGraph e H).oldNeighbourSet
            (actualOld Q B) (actualFresh Q B))
          (actualOld Q B)).image f =
        H.toPredimension.dClosedHull
          (H.oldNeighbourSet (actualOld P B) (actualFresh P B))
          (actualOld P B) := hImage
      _ = actualOld P B := hEq
      _ = (actualOld Q B).image f := (namedBase_old_image e).symm

/-- Agreement of the old graph is preserved when the
base equivalence P ≃ Q is itself an induced graph
isomorphism. The literal Q vertices are the new names. -/
theorem namedBase_old_adj_iff
    (e : P ≃ Q) (H : GraphOn (Sum P B))
    (baseP : GraphOn P) (baseQ : GraphOn Q)
    (hOld : ∀ p q : P,
      H.adj (Sum.inl p) (Sum.inl q) ↔ baseP.adj p q)
    (hBase : ∀ p q : P,
      baseP.adj p q ↔ baseQ.adj (e p) (e q))
    (q r : Q) :
    (namedBaseGraph e H).adj (Sum.inl q) (Sum.inl r) ↔
      baseQ.adj q r := by
  change H.adj (Sum.inl (e.symm q)) (Sum.inl (e.symm r)) ↔
    baseQ.adj q r
  exact (hOld _ _).trans (by
    simpa using hBase (e.symm q) (e.symm r))

end CFLocalCatalogue
end BigHrushovski
