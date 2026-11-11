import BigHrushovski.N0LocalCodeFibre
import Mathlib.Tactic

/-!
# Minimum complete local codes and their fibre cardinalities

Fix a finite orientation, an old vertex set P, and a nonempty finite
set of complete enumerations that agree on P. Assume also that the
admissible enumerations contain every code-equivalent transport by
an automorphism fixing P pointwise.

The least complete directed adjacency code then has exactly
|Aut(C)_(P)| admissible enumerations. The order chosen on the
possible codes does not affect this cardinality.

This is a finite statement conditional on a concrete admissible
family. Its application to the recursively chosen permitted orders
of N₀ still requires constructing that family for every ordered
lower successor part.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The complete directed adjacency matrix of an enumeration,
including both nonedges and the direction of each arrow. -/
def completeDirectedMatrix {n : ℕ}
    (e : Fin n ≃ V) : Fin n → Fin n → Bool :=
  fun i j => decide (e j ∈ O.out (e i))

/-- Equality of complete Boolean matrices is precisely equality
of the full oriented adjacency codes. -/
theorem completeDirectedMatrix_eq_iff {n : ℕ}
    (e f : Fin n ≃ V) :
    O.completeDirectedMatrix e = O.completeDirectedMatrix f ↔
      O.SameOrientedCode e f := by
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    change decide (e j ∈ O.out (e i)) =
      decide (f j ∈ O.out (f i)) at hij
    exact decide_eq_decide.mp hij
  · intro h
    funext i j
    exact decide_eq_decide.mpr (h i j)

/-- Among a nonempty finite family of enumerations, keep those
attaining the smallest value of a complete code. -/
noncomputable def minimumCodeClass {n : ℕ} {κ : Type*}
    [LinearOrder κ]
    (choices : Finset (Fin n ≃ V))
    (code : (Fin n ≃ V) → κ)
    (hne : choices.Nonempty) : Finset (Fin n ≃ V) := by
  classical
  exact choices.filter
    (fun f => code f =
      (choices.image code).min' (Finset.image_nonempty.mpr hne))

theorem mem_minimumCodeClass_iff {n : ℕ} {κ : Type*}
    [LinearOrder κ]
    (choices : Finset (Fin n ≃ V))
    (code : (Fin n ≃ V) → κ)
    (hne : choices.Nonempty) (f : Fin n ≃ V) :
    f ∈ minimumCodeClass choices code hne ↔
      f ∈ choices ∧
      code f = (choices.image code).min'
        (Finset.image_nonempty.mpr hne) := by
  classical
  simp only [minimumCodeClass, Finset.mem_filter]

/-- Every enumeration in the minimum class does attain a
minimum: its code is no larger than that of any admissible
enumeration. -/
theorem minimumCodeClass_is_minimal {n : ℕ} {κ : Type*}
    [LinearOrder κ]
    (choices : Finset (Fin n ≃ V))
    (code : (Fin n ≃ V) → κ)
    (hne : choices.Nonempty)
    {f : Fin n ≃ V}
    (hf : f ∈ minimumCodeClass choices code hne)
    {g : Fin n ≃ V} (hg : g ∈ choices) :
    code f ≤ code g := by
  classical
  obtain ⟨_, hEq⟩ :=
    (mem_minimumCodeClass_iff choices code hne f).mp hf
  rw [hEq]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)

/-- Conditional exact minimum-code fibre theorem. Distinct
admissible enumerations may depend on the already chosen order
of P. The assumptions say the family fixes those old
positions and is invariant under the local pointwise
automorphism group; no independence of choice sets is assumed. -/
theorem minimumCodeClass_card {n : ℕ} {κ : Type*}
    [LinearOrder κ]
    (P : Finset V)
    (choices : Finset (Fin n ≃ V))
    (code : (Fin n ≃ V) → κ)
    (hne : choices.Nonempty)
    (hLower : ∀ e ∈ choices, ∀ f ∈ choices,
      SameLowerPositions P e f)
    (hClosed : ∀ e ∈ choices,
      O.localCodeFibre P e ⊆ choices)
    (hComplete : ∀ e f : Fin n ≃ V,
      code e = code f ↔ O.SameOrientedCode e f) :
    (minimumCodeClass choices code hne).card =
      (O.pointwiseLowerAutomorphisms P).card := by
  classical
  let m : κ := (choices.image code).min'
    (Finset.image_nonempty.mpr hne)
  have hm : m ∈ choices.image code :=
    Finset.min'_mem _ _
  obtain ⟨e, he, hCode⟩ := Finset.mem_image.mp hm
  have hClass :
      minimumCodeClass choices code hne =
        O.localCodeFibre P e := by
    ext f
    rw [mem_minimumCodeClass_iff choices code hne f,
      O.mem_localCodeFibre_iff]
    change (f ∈ choices ∧ code f = m) ↔ _
    constructor
    · rintro ⟨hf, hfm⟩
      have hefCode : code e = code f :=
        hCode.trans hfm.symm
      exact ⟨(hComplete e f).mp hefCode,
        hLower e he f hf⟩
    · rintro ⟨hCodeEq, hOld⟩
      have hFibre : f ∈ O.localCodeFibre P e :=
        (O.mem_localCodeFibre_iff P e f).mpr
          ⟨hCodeEq, hOld⟩
      have hf : f ∈ choices := hClosed e he hFibre
      have heq : code e = code f :=
        (hComplete e f).mpr hCodeEq
      exact ⟨hf, heq.symm.trans hCode⟩
  rw [hClass]
  exact O.localCodeFibre_card P e

end FiniteOrientation
end BigHrushovski
