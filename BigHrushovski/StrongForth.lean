import BigHrushovski.UnlabelledExtension
import BigHrushovski.CountableCover
import BigHrushovski.SpanNormalization

/-!
# Extending a finite strong partial isomorphism in one direction

Let M and N be 2-sparse countable graphs. Given a finite partial
isomorphism between globally strong finite subsets of M and N,
choose a finite globally strong container in M containing the old
domain and one prescribed vertex. The arbitrary finite strong
extension property of N produces an induced, globally strong copy
of that container, respecting every old value of the partial map.

This is the finite *forth* lemma for a strong Fraïssé back-and-forth.
The symmetric *back* lemma and the alternating infinite union are
separate formalization obligations.
-/

namespace BigHrushovski
namespace FiniteCatalogue

private theorem subtype_val_image_univ (s : Finset ℕ) :
    (Finset.univ : Finset {x : ℕ // x ∈ s}).image Subtype.val = s := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Extend the given globally strong partial isomorphism across a
prescribed finite container. We require that the old source a is
globally strong, hence strong in the new finite container c. -/
theorem strong_forth_on_container
    (M N : GraphOn ℕ)
    (hSparseM : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hExtN : HasStrongExtensionProperty N)
    (a b c : Finset ℕ)
    (hac : a ⊆ c)
    (ha : M.toPredimension.IsGloballyStrong a)
    (hb : N.toPredimension.IsGloballyStrong b)
    (p : {x : ℕ // x ∈ a} ≃ {x : ℕ // x ∈ b})
    (hIndP : ∀ x y : {x : ℕ // x ∈ a},
      M.adj x.val y.val ↔ N.adj (p x).val (p y).val) :
    ∃ g : {x : ℕ // x ∈ c} → ℕ,
      Function.Injective g ∧
      (∀ x y : {x : ℕ // x ∈ c},
        M.adj x.val y.val ↔ N.adj (g x) (g y)) ∧
      (∀ x : {x : ℕ // x ∈ a},
        g ⟨x.val, hac x.property⟩ = (p x).val) ∧
      N.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset {x : ℕ // x ∈ c}).image g) := by
  classical
  let A := {x : ℕ // x ∈ a}
  let C := {x : ℕ // x ∈ c}
  let GA : GraphOn A := M.pullback (Subtype.val : A → ℕ)
  let GC : GraphOn C := M.pullback (Subtype.val : C → ℕ)
  let i : A → C := fun x => ⟨x.val, hac x.property⟩
  let f : A → ℕ := fun x => (p x).val
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg Subtype.val h)
  have hf : Function.Injective f := by
    intro x y h
    exact p.injective (Subtype.ext h)
  have hIndI : ∀ x y : A, GA.adj x y ↔ GC.adj (i x) (i y) :=
    fun _ _ => Iff.rfl
  have hIndF : ∀ x y : A, GA.adj x y ↔ N.adj (f x) (f y) :=
    hIndP
  have hSparseA : GA.IsTwoSparse (Finset.univ : Finset A) := by
    have h := GA.twoSparse_image_iff M
      (Subtype.val : A → ℕ)
      (Subtype.val_injective)
      (fun _ _ => Iff.rfl)
      (Finset.univ : Finset A)
    rw [subtype_val_image_univ a] at h
    exact h.mp (by intro s _; exact hSparseM s)
  have hSparseC : GC.IsTwoSparse (Finset.univ : Finset C) := by
    have h := GC.twoSparse_image_iff M
      (Subtype.val : C → ℕ)
      (Subtype.val_injective)
      (fun _ _ => Iff.rfl)
      (Finset.univ : Finset C)
    rw [subtype_val_image_univ c] at h
    exact h.mpr (by intro s _; exact hSparseM s)
  have hImageI :
      (((Finset.univ : Finset A).image i).image
        (Subtype.val : C → ℕ)) = a := by
    rw [Finset.image_image]
    have hComp : (Subtype.val : C → ℕ) ∘ i =
        (Subtype.val : A → ℕ) := by
      funext x
      rfl
    rw [hComp]
    exact subtype_val_image_univ a
  have hStrongI :
      GC.toPredimension.IsStrong
        ((Finset.univ : Finset A).image i)
        (Finset.univ : Finset C) := by
    have h := (GC.strong_image_iff M
      (Subtype.val : C → ℕ)
      (Subtype.val_injective)
      (fun _ _ => Iff.rfl)
      ((Finset.univ : Finset A).image i)
      (Finset.univ : Finset C)
      (Finset.subset_univ _)).mp (by
        rw [hImageI, subtype_val_image_univ c]
        exact ha c hac)
    exact h
  have hImageF : (Finset.univ : Finset A).image f = b := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
      rw [← hx]
      exact (p x).property
    · intro hz
      refine Finset.mem_image.mpr
        ⟨p.symm ⟨z, hz⟩, Finset.mem_univ _, ?_⟩
      simp [f]
  have hStrongF :
      N.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset A).image f) := by
    rw [hImageF]
    exact hb
  obtain ⟨g, hg, hgInd, hgBase, hgStrong⟩ :=
    arbitrary_finite_strong_extension N hExtN
      GA GC i hi hIndI
      hSparseA hSparseC hStrongI f hf hIndF hStrongF
  exact ⟨g, hg, hgInd, hgBase, hgStrong⟩


end FiniteCatalogue
end BigHrushovski
