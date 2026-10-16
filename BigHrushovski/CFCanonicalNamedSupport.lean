import BigHrushovski.CFLocalSupport
import BigHrushovski.CFNormalizedLocalType

/-!
# The canonical d-closed old support as a literal old vertex subset

The finite local-support lemma supplies a strict d-closed hull
inside the actual old vertices of a minimal extension. For a
graph presented on S ⊕ B, we can identify this hull uniquely
with a literal subset P of the old type S.

This avoids choosing arbitrary names for P and gives four
properties in the original complete graph: the old graph
on P is d-closed in the old graph on S; all old neighbours
of new vertices belong to P; the induced interval
P <_d P ⊕ B is minimal; and P is exactly the d-closed hull
of its old-neighbour set. The next split-graph transport
module will carry these properties to the carrier P ⊕ B.

All results are finite and do not use growth or countability.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {S B : Type*} [Fintype S] [DecidableEq S]
  [Fintype B] [DecidableEq B]

/-- The literal old vertices inside a graph with carrier S ⊕ B. -/
private theorem old_fresh_union_univ :
    actualOld S B ∪ actualFresh S B =
      (Finset.univ : Finset (Sum S B)) := by
  classical
  ext x
  cases x with
  | inl s => simp [actualOld, actualFresh]
  | inr b => simp [actualOld, actualFresh]

private theorem actual_old_fresh_disjoint_local :
    Disjoint (actualOld S B) (actualFresh S B) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
  cases hs.trans hb.symm

/-- The canonical old-neighbour d-closed hull, with its old
vertices presented by their original S-names. -/
noncomputable def canonicalNamedSupport (H : GraphOn (Sum S B)) :
    Finset S := by
  classical
  let A := actualOld S B
  let D := actualFresh S B
  let T := H.toPredimension.dClosedHull (H.oldNeighbourSet A D) A
  exact Finset.univ.filter (fun s : S => Sum.inl s ∈ T)

/-- The canonical named support maps exactly onto the least
d-closed hull inside the old part of the entire extension. -/
theorem canonicalNamedSupport_image (H : GraphOn (Sum S B)) :
    (canonicalNamedSupport H).image Sum.inl =
      H.toPredimension.dClosedHull
        (H.oldNeighbourSet (actualOld S B) (actualFresh S B))
        (actualOld S B) := by
  classical
  let A := actualOld S B
  let D := actualFresh S B
  let T := H.toPredimension.dClosedHull (H.oldNeighbourSet A D) A
  have hTsub : T ⊆ A :=
    (H.toPredimension.dClosedHull_dclosed
      (H.oldNeighbourSet A D) A).1
  change ((Finset.univ : Finset S).filter
    (fun s : S => Sum.inl s ∈ T)).image Sum.inl = T
  ext x
  cases x with
  | inl s =>
      constructor
      · intro hx
        obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hx
        have htT := (Finset.mem_filter.mp ht).2
        have hEq : t = s := Sum.inl.inj hts
        subst s
        exact htT
      · intro hx
        exact Finset.mem_image.mpr
          ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  | inr b =>
      constructor
      · intro hx
        obtain ⟨s, _, h⟩ := Finset.mem_image.mp hx
        cases h
      · intro hx
        have hOld : Sum.inr b ∈ A := hTsub hx
        obtain ⟨s, _, h⟩ := Finset.mem_image.mp hOld
        cases h

/-- Minimality of the whole old-to-new extension identifies
the canonical literal old support P, proves it is strictly
d-closed in S, forbids all old/fresh edges outside P, and
supplies the minimal and exact-support local interval. -/
theorem canonicalNamedSupport_certificates
    (H : GraphOn (Sum S B))
    (hMin : H.toPredimension.IsMinimalDClosedStep
      (actualOld S B) Finset.univ) :
    let P := canonicalNamedSupport H
    (H.pullback Sum.inl).toPredimension.IsDClosed P Finset.univ ∧
    (∀ x : S, ∀ b : B,
      H.adj (Sum.inl x) (Sum.inr b) → x ∈ P) ∧
    H.toPredimension.IsMinimalDClosedStep
      (P.image Sum.inl) (P.image Sum.inl ∪ actualFresh S B) ∧
    H.toPredimension.dClosedHull
      (H.oldNeighbourSet (P.image Sum.inl) (actualFresh S B))
      (P.image Sum.inl) = P.image Sum.inl := by
  classical
  let A := actualOld S B
  let D := actualFresh S B
  let N := H.oldNeighbourSet A D
  let T := H.toPredimension.dClosedHull N A
  let P := canonicalNamedSupport H
  have hUnion : A ∪ D = (Finset.univ : Finset (Sum S B)) :=
    old_fresh_union_univ
  have hMinimal : H.toPredimension.IsMinimalDClosedStep A (A ∪ D) := by
    simpa only [hUnion] using hMin
  obtain ⟨hTClosed, hNoCross, hTMin, hTRight, hTExact⟩ :=
    H.canonical_dClosed_local_support A D actual_old_fresh_disjoint_local hMinimal
  have hTsub : T ⊆ A := hTClosed.1
  have hNsubT : N ⊆ T :=
    H.toPredimension.subset_dClosedHull
      (H.oldNeighbourSet_subset A D)
  have hImage : P.image Sum.inl = T :=
    canonicalNamedSupport_image H
  have hPClosed :
      (H.pullback Sum.inl).toPredimension.IsDClosed P Finset.univ := by
    apply ((H.pullback Sum.inl).dClosed_image_iff H
      Sum.inl Sum.inl_injective
      (fun _ _ => Iff.rfl) P Finset.univ
      (Finset.subset_univ _)).mp
    have hOldEq :
        (Finset.univ : Finset S).image Sum.inl = A := rfl
    rw [hImage, hOldEq]
    exact hTClosed
  have hBack : ∀ x : S, ∀ b : B,
      H.adj (Sum.inl x) (Sum.inr b) → x ∈ P := by
    intro x b hAdj
    have hD : Sum.inr b ∈ D := by
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
    have hA : Sum.inl x ∈ A := by
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    have hN : Sum.inl x ∈ N :=
      H.oldNeighbourSet_contains A D hD hA
        (H.symm _ _ hAdj)
    have hT : Sum.inl x ∈ T := hNsubT hN
    change x ∈ (Finset.univ : Finset S).filter
      (fun s => Sum.inl s ∈ T)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
  have hNT : H.oldNeighbourSet T D = N := by
    ext x
    constructor
    · intro hx
      have hxT : x ∈ T :=
        (Finset.mem_filter.mp hx).1
      exact Finset.mem_filter.mpr
        ⟨hTsub hxT, (Finset.mem_filter.mp hx).2⟩
    · intro hx
      exact Finset.mem_filter.mpr
        ⟨hNsubT hx, (Finset.mem_filter.mp hx).2⟩
  have hExact : H.toPredimension.dClosedHull
      (H.oldNeighbourSet (P.image Sum.inl) D)
      (P.image Sum.inl) = P.image Sum.inl := by
    simpa only [hImage, hNT] using hTExact
  have hLocalMinimal :
      H.toPredimension.IsMinimalDClosedStep
        (P.image Sum.inl) (P.image Sum.inl ∪ D) := by
    simpa only [hImage] using hTMin
  exact ⟨hPClosed, hBack, hLocalMinimal, hExact⟩

end CFLocalCatalogue
end BigHrushovski
