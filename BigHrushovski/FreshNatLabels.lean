import BigHrushovski.SpanNormalization
import Mathlib.Data.Fintype.EquivFin

/-!
# Extending finite injections into the natural-number carrier

For a finite embedding f : A → B and an existing injective labelling
e : A → ℕ, we extend the labelling to B while fixing the labels of A.

The new vertices receive labels above every existing label, using
a finite ordinal encoding of B. This is a constructive carrier step
needed for a countable chain with literally increasing domains inside ℕ.
It does not yet construct a graph on those domains.
-/

namespace BigHrushovski
namespace FiniteSpan

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Extend the labels of the old finite domain along an arbitrary
injective finite map. A vertex outside the image of f gets a new
natural-number label above the maximum existing label. -/
noncomputable def extendNatLabels (f : A → B) (e : A → ℕ) : B → ℕ := by
  classical
  exact fun b =>
    if h : ∃ a : A, f a = b then
      e (Classical.choose h)
    else
      (Finset.univ : Finset A).sup e + 1 +
        ((Fintype.equivFin B) b).val

/-- The extended labels agree exactly with the old ones along f. -/
theorem extendNatLabels_comp
    (f : A → B) (hf : Function.Injective f)
    (e : A → ℕ) (a : A) :
    extendNatLabels f e (f a) = e a := by
  classical
  unfold extendNatLabels
  split_ifs with h
  · have hEq : Classical.choose h = a :=
      hf (Classical.choose_spec h)
    exact congrArg e hEq
  · exact (h ⟨a, rfl⟩).elim

/-- A new vertex receives its explicit upper-range label. -/
theorem extendNatLabels_of_not_mem
    (f : A → B) (e : A → ℕ) (b : B)
    (hb : ¬ ∃ a : A, f a = b) :
    extendNatLabels f e b =
      (Finset.univ : Finset A).sup e + 1 +
        ((Fintype.equivFin B) b).val := by
  classical
  simp [extendNatLabels, hb]

/-- Every new label is larger than the supremum of the old labels. -/
theorem extendNatLabels_above_old
    (f : A → B) (e : A → ℕ) (b : B)
    (hb : ¬ ∃ a : A, f a = b) :
    (Finset.univ : Finset A).sup e < extendNatLabels f e b := by
  rw [extendNatLabels_of_not_mem f e b hb]
  omega

/-- In particular no new vertex gets a label used by an old vertex. -/
theorem extendNatLabels_fresh
    (f : A → B) (e : A → ℕ) (a : A) (b : B)
    (hb : ¬ ∃ a : A, f a = b) :
    e a < extendNatLabels f e b := by
  have hOld : e a ≤ (Finset.univ : Finset A).sup e :=
    Finset.le_sup (f := e) (Finset.mem_univ a)
  exact hOld.trans_lt (extendNatLabels_above_old f e b hb)

/-- An injective old labelling extends to an injective new labelling.
This avoids all unintended identifications at a successor stage. -/
theorem extendNatLabels_injective
    (f : A → B) (hf : Function.Injective f)
    (e : A → ℕ) (he : Function.Injective e) :
    Function.Injective (extendNatLabels f e) := by
  classical
  intro b c hEq
  by_cases hb : ∃ a : A, f a = b
  · obtain ⟨a, ha⟩ := hb
    by_cases hc : ∃ a : A, f a = c
    · obtain ⟨a', ha'⟩ := hc
      have hOldEq : e a = e a' := by
        calc
          e a = extendNatLabels f e (f a) :=
            (extendNatLabels_comp f hf e a).symm
          _ = extendNatLabels f e b := by rw [ha]
          _ = extendNatLabels f e c := hEq
          _ = extendNatLabels f e (f a') := by rw [ha']
          _ = e a' := extendNatLabels_comp f hf e a'
      calc
        b = f a := ha.symm
        _ = f a' := congrArg f (he hOldEq)
        _ = c := ha'
    · have hBelow : extendNatLabels f e b ≤
          (Finset.univ : Finset A).sup e := by
        rw [← ha, extendNatLabels_comp f hf e a]
        exact Finset.le_sup (f := e) (Finset.mem_univ a)
      have hAbove := extendNatLabels_above_old f e c hc
      omega
  · by_cases hc : ∃ a : A, f a = c
    · obtain ⟨a, ha⟩ := hc
      have hBelow : extendNatLabels f e c ≤
          (Finset.univ : Finset A).sup e := by
        rw [← ha, extendNatLabels_comp f hf e a]
        exact Finset.le_sup (f := e) (Finset.mem_univ a)
      have hAbove := extendNatLabels_above_old f e b hb
      omega
    · have hVal : ((Fintype.equivFin B) b).val =
          ((Fintype.equivFin B) c).val := by
        rw [extendNatLabels_of_not_mem f e b hb,
          extendNatLabels_of_not_mem f e c hc] at hEq
        omega
      exact (Fintype.equivFin B).injective (Fin.ext hVal)

end FiniteSpan
end BigHrushovski
