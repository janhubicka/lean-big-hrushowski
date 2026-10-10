import BigHrushovski.LabelledDiagrams
import BigHrushovski.GenericityCriterion

/-!
# Strong extension property for arbitrary finite graph types

The fair catalogue and conditional genericity criterion were originally
formulated for finite graphs on Fin n and Fin m. The completeness theorem
for labelled strong diagrams now transfers the extension property to
arbitrary finite 2-sparse graph structures, with a strong induced map
of the common base.

This is still a conditional result: its hypothesis is the labelled
strong extension property of an ambient graph on ℕ. The construction
of such an ambient graph remains a separate task.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- The labelled extension property extends to every finite 2-sparse
strong-embedding diagram, regardless of the vertex labels. -/
theorem arbitrary_finite_strong_extension
    (M : GraphOn ℕ) (hExt : HasStrongExtensionProperty M)
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (GA : GraphOn A) (GB : GraphOn B)
    (i : A → B) (hi : Function.Injective i)
    (hInducedI : ∀ x y : A,
      GA.adj x y ↔ GB.adj (i x) (i y))
    (hSparseA : GA.IsTwoSparse (Finset.univ : Finset A))
    (hSparseB : GB.IsTwoSparse (Finset.univ : Finset B))
    (hStrongI : GB.toPredimension.IsStrong
      ((Finset.univ : Finset A).image i)
      (Finset.univ : Finset B))
    (f : A → ℕ) (hf : Function.Injective f)
    (hInducedF : ∀ x y : A,
      GA.adj x y ↔ M.adj (f x) (f y))
    (hStrongF : M.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset A).image f)) :
    ∃ g : B → ℕ,
      Function.Injective g ∧
      (∀ x y : B, GB.adj x y ↔ M.adj (g x) (g y)) ∧
      (∀ x : A, g (i x) = f x) ∧
      M.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset B).image g) := by
  classical
  obtain ⟨eA, eB, d, hSource, hTarget, hMap⟩ :=
    exists_labelled_strong_diagram GA GB i hi hInducedI
      hSparseA hSparseB hStrongI
  let req : ExtensionRequestCatalogue :=
    ⟨Fintype.card A, Fintype.card B, (d, fun x => f (eA x))⟩
  have hInjReq : Function.Injective
      (fun x : Fin (Fintype.card A) => f (eA x)) := by
    intro x y hxy
    exact eA.injective (hf hxy)
  have hSourceInduced : ∀ x y : Fin (Fintype.card A),
      d.source.adj x y ↔ M.adj (f (eA x)) (f (eA y)) := by
    intro x y
    exact (hSource x y).trans (hInducedF (eA x) (eA y))
  have hImageSource :
      (Finset.univ : Finset (Fin (Fintype.card A))).image
          (fun x => f (eA x)) =
        (Finset.univ : Finset A).image f := by
    calc
      _ = (Finset.univ : Finset (Fin (Fintype.card A))).image
          (f ∘ eA) := rfl
      _ = ((Finset.univ : Finset (Fin (Fintype.card A))).image eA).image f := by
            rw [Finset.image_image]
      _ = (Finset.univ : Finset A).image f := by
            rw [Finset.image_univ_of_surjective eA.surjective]
  have hApplicable : AppliesGlobally M req := by
    change Function.Injective (fun x : Fin (Fintype.card A) => f (eA x)) ∧
      (∀ x y : Fin (Fintype.card A),
        d.source.adj x y ↔ M.adj (f (eA x)) (f (eA y))) ∧
      M.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset (Fin (Fintype.card A))).image
          (fun x => f (eA x)))
    refine ⟨hInjReq, hSourceInduced, ?_⟩
    rw [hImageSource]
    exact hStrongF
  obtain ⟨k, hkInj, hkInduced, hkBase, hkStrong⟩ :=
    hExt req hApplicable
  let g : B → ℕ := fun b => k (eB.symm b)
  have hgInj : Function.Injective g := by
    intro x y hxy
    exact eB.symm.injective (hkInj hxy)
  have hgInduced : ∀ x y : B,
      GB.adj x y ↔ M.adj (g x) (g y) := by
    intro x y
    have h := (hTarget (eB.symm x) (eB.symm y)).symm.trans
      (hkInduced (eB.symm x) (eB.symm y))
    simpa [g] using h
  have hgBase : ∀ a : A, g (i a) = f a := by
    intro a
    have hMapEq :
        d.embedding (eA.symm a) = eB.symm (i a) := by
      apply eB.injective
      simpa using hMap (eA.symm a)
    change k (eB.symm (i a)) = f a
    rw [← hMapEq]
    simpa using hkBase (eA.symm a)
  have hImageTarget :
      (Finset.univ : Finset B).image g =
        (Finset.univ : Finset (Fin (Fintype.card B))).image k := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr
        ⟨eB.symm b, Finset.mem_univ _, hb⟩
    · intro hz
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
      refine Finset.mem_image.mpr ⟨eB x, Finset.mem_univ _, ?_⟩
      simpa [g] using hx
  refine ⟨g, hgInj, hgInduced, hgBase, ?_⟩
  rw [hImageTarget]
  exact hkStrong

end FiniteCatalogue
end BigHrushovski
