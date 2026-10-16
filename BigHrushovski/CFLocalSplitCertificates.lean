import BigHrushovski.CFTransportedBoundary
import BigHrushovski.CFLocalSupportTransport
import BigHrushovski.CFGrowthClass

/-!
# The complete local restriction to a canonical C_F support

Given a graph H on a finite old carrier S and new block B, let
P ⊆ S be an old support. The full induced local graph is
presented on the split carrier P ⊕ B, where P is literally
the subtype of the old S vertices.

This module checks the complete induced injection of P ⊕ B into
S ⊕ B, including exact old/fresh images. It transports three
separate properties from the original induced local interval:
membership in the growth class C_F, minimal strict d-closedness
over P, and equality of P with the strict d-closed hull of
its old-neighbour set.

There is no choice of an unrelated isomorphic P and no loss of
boundary nonedges. The canonical support theorem supplies the
ambient minimality and exact-support premises; the resulting
local split certificates are the inputs needed by the named
one-step C_F response.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {S B : Type*} [Fintype S] [DecidableEq S]
  [Fintype B] [DecidableEq B]

/-- Canonical injection of the complete local graph on P⊕B
into the original graph on S⊕B. -/
def oldSubsetInclusion (P : Finset S) :
    Sum {s : S // s ∈ P} B → Sum S B
  | Sum.inl p => Sum.inl p.val
  | Sum.inr b => Sum.inr b

theorem oldSubsetInclusion_injective (P : Finset S) :
    Function.Injective (oldSubsetInclusion (B := B) P) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have hxy : x.val = y.val := Sum.inl.inj h
          exact congrArg Sum.inl (Subtype.ext hxy)
      | inr y => cases h
  | inr x =>
      cases y with
      | inl y => cases h
      | inr y => exact congrArg Sum.inr (Sum.inr.inj h)

/-- The local old vertices have exactly the original names P. -/
theorem oldSubsetOld_image (P : Finset S) :
    (actualOld {s : S // s ∈ P} B).image
      (oldSubsetInclusion (B := B) P) = P.image Sum.inl := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
    obtain ⟨p, _, hpw⟩ := Finset.mem_image.mp hw
    subst w
    exact Finset.mem_image.mpr
      ⟨p.val, p.property, hwz⟩
  · intro hz
    obtain ⟨s, hs, hsz⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr
      ⟨Sum.inl ⟨s, hs⟩, ?_, hsz⟩
    exact Finset.mem_image.mpr
      ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩

/-- The full new block is carried identically. -/
theorem oldSubsetFresh_image (P : Finset S) :
    (actualFresh {s : S // s ∈ P} B).image
      (oldSubsetInclusion (B := B) P) =
        actualFresh S B := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
    obtain ⟨b, _, hbw⟩ := Finset.mem_image.mp hw
    subst w
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_univ _, hwz⟩
  · intro hz
    obtain ⟨b, _, hbz⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr
      ⟨Sum.inr b, ?_, hbz⟩
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_univ _, rfl⟩

private theorem localOld_unionFresh
    (P : Finset S) :
    actualOld {s : S // s ∈ P} B ∪
      actualFresh {s : S // s ∈ P} B =
      (Finset.univ : Finset (Sum {s : S // s ∈ P} B)) := by
  classical
  ext x
  cases x with
  | inl p => simp [actualOld, actualFresh]
  | inr b => simp [actualOld, actualFresh]

/-- The complete local carrier has exactly the old support
and all fresh vertices as its image, with nothing omitted. -/
theorem oldSubsetUniv_image (P : Finset S) :
    (Finset.univ : Finset (Sum {s : S // s ∈ P} B)).image
      (oldSubsetInclusion (B := B) P) =
      P.image Sum.inl ∪ actualFresh S B := by
  classical
  rw [← localOld_unionFresh P, Finset.image_union,
    oldSubsetOld_image, oldSubsetFresh_image]

/-- All induced C_F growth inequalities transport to the complete
local split representation, including nonedges. -/
theorem oldSubsetLocal_growth
    (H : GraphOn (Sum S B)) (F : ℕ → ℝ)
    (P : Finset S)
    (hGrowth : H.IsGrowthSparse F Finset.univ) :
    (oldSubsetLocalGraph H P).IsGrowthSparse F Finset.univ := by
  classical
  have h : H.IsGrowthSparse F
      ((Finset.univ : Finset (Sum {s : S // s ∈ P} B)).image
        (oldSubsetInclusion (B := B) P)) :=
    H.growthSparse_restrict F hGrowth (Finset.subset_univ _)
  exact ((oldSubsetLocalGraph H P).growthSparse_image_iff
    H F (oldSubsetInclusion (B := B) P)
    (oldSubsetInclusion_injective P)
    (fun _ _ => Iff.rfl)
    Finset.univ).mp h

/-- Minimal strict d-closedness of the original induced
local interval is preserved in its complete split graph. -/
theorem oldSubsetLocal_minimal
    (H : GraphOn (Sum S B))
    (P : Finset S)
    (hMinimal : H.toPredimension.IsMinimalDClosedStep
      (P.image Sum.inl) (P.image Sum.inl ∪ actualFresh S B)) :
    (oldSubsetLocalGraph H P).toPredimension.IsMinimalDClosedStep
      (actualOld {s : S // s ∈ P} B) Finset.univ := by
  classical
  apply ((oldSubsetLocalGraph H P).minimalDClosedStep_image_iff
    H (oldSubsetInclusion (B := B) P)
    (oldSubsetInclusion_injective P)
    (fun _ _ => Iff.rfl)
    (actualOld {s : S // s ∈ P} B)
    Finset.univ (Finset.subset_univ _)).mp
  rw [oldSubsetOld_image, oldSubsetUniv_image]
  exact hMinimal

/-- Exact canonical support is preserved, including the least
strict d-closed hull of all old neighbours of the fresh block. -/
theorem oldSubsetLocal_exactSupport
    (H : GraphOn (Sum S B))
    (P : Finset S)
    (hSupport : H.toPredimension.dClosedHull
      (H.oldNeighbourSet (P.image Sum.inl) (actualFresh S B))
      (P.image Sum.inl) = P.image Sum.inl) :
    (oldSubsetLocalGraph H P).toPredimension.dClosedHull
      ((oldSubsetLocalGraph H P).oldNeighbourSet
        (actualOld {s : S // s ∈ P} B)
        (actualFresh {s : S // s ∈ P} B))
      (actualOld {s : S // s ∈ P} B) =
        actualOld {s : S // s ∈ P} B := by
  classical
  let i := oldSubsetInclusion (B := B) P
  have hi : Function.Injective i := oldSubsetInclusion_injective P
  have hTransport :=
    (oldSubsetLocalGraph H P).canonicalOldSupport_image
      H i hi (fun _ _ => Iff.rfl)
      (actualOld {s : S // s ∈ P} B)
      (actualFresh {s : S // s ∈ P} B)
  rw [oldSubsetOld_image, oldSubsetFresh_image] at hTransport
  apply Finset.image_injective hi
  calc
    ((oldSubsetLocalGraph H P).toPredimension.dClosedHull
      ((oldSubsetLocalGraph H P).oldNeighbourSet
        (actualOld {s : S // s ∈ P} B)
        (actualFresh {s : S // s ∈ P} B))
      (actualOld {s : S // s ∈ P} B)).image i =
      H.toPredimension.dClosedHull
        (H.oldNeighbourSet (P.image Sum.inl) (actualFresh S B))
        (P.image Sum.inl) := hTransport
    _ = P.image Sum.inl := hSupport
    _ = (actualOld {s : S // s ∈ P} B).image i :=
      (oldSubsetOld_image P).symm

/-- All three required normalized local inputs are supplied at
once by induced restriction of an ambient minimal C_F local
interval with the exact old support P. -/
theorem oldSubsetLocal_certificates
    (H : GraphOn (Sum S B)) (F : ℕ → ℝ)
    (P : Finset S)
    (hGrowth : H.IsGrowthSparse F Finset.univ)
    (hMinimal : H.toPredimension.IsMinimalDClosedStep
      (P.image Sum.inl) (P.image Sum.inl ∪ actualFresh S B))
    (hSupport : H.toPredimension.dClosedHull
      (H.oldNeighbourSet (P.image Sum.inl) (actualFresh S B))
      (P.image Sum.inl) = P.image Sum.inl) :
    (oldSubsetLocalGraph H P).IsGrowthSparse F Finset.univ ∧
    (oldSubsetLocalGraph H P).toPredimension.IsMinimalDClosedStep
      (actualOld {s : S // s ∈ P} B) Finset.univ ∧
    (oldSubsetLocalGraph H P).toPredimension.dClosedHull
      ((oldSubsetLocalGraph H P).oldNeighbourSet
        (actualOld {s : S // s ∈ P} B)
        (actualFresh {s : S // s ∈ P} B))
      (actualOld {s : S // s ∈ P} B) =
        actualOld {s : S // s ∈ P} B :=
  ⟨oldSubsetLocal_growth H F P hGrowth,
   oldSubsetLocal_minimal H P hMinimal,
   oldSubsetLocal_exactSupport H P hSupport⟩

end CFLocalCatalogue
end BigHrushovski
