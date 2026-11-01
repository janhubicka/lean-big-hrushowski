import BigHrushovski.CFStageCatalogue
import BigHrushovski.CFOneLevelResponse
import BigHrushovski.CFRealFiniteGenericity

/-!
# Literal singleton request at an arbitrary finite C_F level

The paper's remaining countable genericity gap is the claim that
the singleton minimal strict d-closed extension over the empty
support occurs as an *actual* StageRequest at every level.
This module proves the finite statement under its exact
necessary inputs: the empty support is strictly d-closed in
the old stage, the singleton and empty finite graphs satisfy
the growth inequality, and the uniform block-size bound allows
one fresh vertex.

No total map of the old stage, chosen nonempty target, or
unverified Fraisse-limit hypothesis is introduced.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

private abbrev SingletonCarrier (U : Type*) :=
  Sum (SupportCarrier U ∅) (Fin 1)

/-- The one-vertex graph, with no old vertices or edges. -/
private def singletonLocalGraph (U : Type*) :
    GraphOn (SingletonCarrier U) where
  adj := fun _ _ => False
  symm := by intro _ _ h; exact False.elim h
  irrefl := by intro _ h; exact False.elim h

/-- This literal local carrier has exactly one vertex, namely
the first fresh ordinal. -/
private theorem singletonCarrier_eq
    (x y : SingletonCarrier U) : x = y := by
  cases x with
  | inl p => simp at p.property
  | inr i =>
    cases y with
    | inl p => simp at p.property
    | inr j => exact congrArg Sum.inr (Subsingleton.elim i j)

/-- The old part of the one-vertex local extension is empty. -/
private theorem singleton_old_empty :
    CFLocalCatalogue.oldVertices (SupportCarrier U ∅) 1 = ∅ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hx
    have h : p.val ∈ (∅ : Finset U) := p.property
    simp at h
  · simp

/-- An arbitrary nonempty subset of a singleton carrier is its
whole vertex set. -/
private theorem singleton_subset_univ
    (s : Finset (SingletonCarrier U)) (hs : s ≠ ∅) :
    s = Finset.univ := by
  classical
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
  obtain ⟨y, hy⟩ := hne
  ext x
  simp only [Finset.mem_univ, iff_true]
  have hxy : x = y := singletonCarrier_eq x y
  simpa [hxy] using hy

/-- All finite induced edge sets of the singleton local graph
are empty. -/
private theorem singleton_no_edges
    (s : Finset (SingletonCarrier U)) :
    (singletonLocalGraph U).edgesWithin s = ∅ := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨_, hEdge⟩ :=
      ((singletonLocalGraph U).mem_edgesWithin_iff s e).mp he
    obtain ⟨_, x, _, y, _, hxy⟩ := hEdge
    exact False.elim hxy
  · simp

private theorem singleton_predim
    (s : Finset (SingletonCarrier U)) :
    (singletonLocalGraph U).predim s = 2 * (s.card : ℤ) := by
  simp [GraphOn.predim, singleton_no_edges]

private theorem singleton_univ_card :
    (Finset.univ : Finset (SingletonCarrier U)).card = 1 := by
  classical
  have hEq : (Finset.univ : Finset (SingletonCarrier U)) =
      {Sum.inr (0 : Fin 1)} := by
    ext x
    constructor
    · intro _
      have h : x = Sum.inr (0 : Fin 1) :=
        singletonCarrier_eq x (Sum.inr 0)
      simpa [h]
    · intro _
      exact Finset.mem_univ _
  simp [hEq]

/-- A real growth function with F(0)≤0 and F(1)≤2 admits
the singleton no-edge graph on its complete literal carrier. -/
private theorem singleton_growth
    (F : ℕ → ℝ)
    (hZero : F 0 ≤ 0)
    (hOne : F 1 ≤ 2) :
    (singletonLocalGraph U).IsGrowthSparse F Finset.univ := by
  classical
  intro s _
  by_cases hs : s = ∅
  · subst s
    simpa [singleton_predim] using hZero
  · have hu : s = Finset.univ :=
      singleton_subset_univ s hs
    subst s
    simpa [singleton_predim, singleton_univ_card] using hOne

/-- The singleton local graph is a proper minimal strict d-closed
extension of its empty old part. There are no intermediate subsets. -/
private theorem singleton_minimal :
    (singletonLocalGraph U).toPredimension.IsMinimalDClosedStep
      (CFLocalCatalogue.oldVertices (SupportCarrier U ∅) 1)
      Finset.univ := by
  classical
  rw [singleton_old_empty]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Finset.empty_subset _, ?_⟩
    intro c _ hcNe _
    have hUniv : c = Finset.univ :=
      singleton_subset_univ c hcNe
    subst c
    change (singletonLocalGraph U).predim ∅ <
      (singletonLocalGraph U).predim Finset.univ
    simp [singleton_predim, singleton_univ_card]
  · intro hEq
    have hx : (Sum.inr (0 : Fin 1) : SingletonCarrier U) ∈
        (Finset.univ : Finset (SingletonCarrier U)) :=
      Finset.mem_univ _
    rw [← hEq] at hx
    simpa using hx
  · intro z _ _ _
    by_cases hz : z = ∅
    · exact Or.inl hz
    · exact Or.inr (singleton_subset_univ z hz)

/-- The old-neighbour support of the singleton extension is
exactly empty, including its strict d-closed hull in the old part. -/
private theorem singleton_exact_support :
    (singletonLocalGraph U).toPredimension.dClosedHull
      ((singletonLocalGraph U).oldNeighbourSet
        (CFLocalCatalogue.oldVertices (SupportCarrier U ∅) 1)
        (CFLocalCatalogue.freshVertices (SupportCarrier U ∅) 1))
      (CFLocalCatalogue.oldVertices (SupportCarrier U ∅) 1) =
        CFLocalCatalogue.oldVertices (SupportCarrier U ∅) 1 := by
  classical
  apply le_antisymm
  · exact ((singletonLocalGraph U).toPredimension.dClosedHull_dclosed
      _ _).1
  · rw [singleton_old_empty]
    exact Finset.empty_subset _

/-- A one-vertex local extension gives an actual member of the
bounded stage request catalogue at the empty support. -/
theorem singletonStageRequest_exists
    (G : GraphOn U) (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hEmpty : G.toPredimension.IsDClosed ∅ Finset.univ)
    (hZero : F 0 ≤ 0)
    (hOne : F 1 ≤ 2)
    (hK : 1 ≤ K 0) :
    Nonempty (StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card)) := by
  classical
  let P : Finset U := ∅
  let H : GraphOn (Sum (SupportCarrier U P) (Fin 1)) :=
    singletonLocalGraph U
  let t : CFLocalCatalogue.OrderedLocalType
      (SupportCarrier U P) (supportGraph G P)
      (GrowthAllowedLocal F P) 1 :=
    { graph := H
      base_agrees := by
        intro p q
        have hp : p.val ∈ (∅ : Finset U) := p.property
        simp at hp
      allowed := singleton_growth F hZero hOne
      minimal := singleton_minimal
      exact_support := singleton_exact_support }
  refine ⟨⟨P, hEmpty, ?_⟩⟩
  exact CFLocalCatalogue.toBounded
    (supportGraph G P) (GrowthAllowedLocal F P)
    (K 0) 1 hK t

end CFStageCatalogue
end BigHrushovski
