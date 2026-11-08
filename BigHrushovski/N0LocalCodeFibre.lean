import BigHrushovski.N0LocalCode
import Mathlib.Tactic

/-!
# Exact cardinality of a complete local adjacency-code fibre

Fix a finite orientation O, a finite lower part P, and a complete
enumeration e of the oriented graph. The enumerations f whose
complete directed adjacency code equals that of e, and which agree
with e at all positions occupied by P, are exactly the images of e
under orientation automorphisms fixing P pointwise.

The proof supplies an explicit bijection between that finite code
fibre and the stabilizer, establishing the local factor required by
the manuscript's N₀ exact-degree formula.

This concerns finite enumerations of one oriented closure; it is
not yet the count of globally permitted orders on A, and it does
not prove the infinite Ramsey assertion.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The finite fibre of complete directed adjacency codes among
enumerations fixing all positions of the lower part P. -/
noncomputable def localCodeFibre (P : Finset V) {n : ℕ}
    (e : Fin n ≃ V) : Finset (Fin n ≃ V) := by
  classical
  exact Finset.univ.filter (fun f =>
    O.SameOrientedCode e f ∧ SameLowerPositions P e f)

theorem mem_localCodeFibre_iff (P : Finset V) {n : ℕ}
    (e f : Fin n ≃ V) :
    f ∈ O.localCodeFibre P e ↔
      O.SameOrientedCode e f ∧ SameLowerPositions P e f := by
  classical
  simp [localCodeFibre]

/-- Every local code-equivalent enumeration is uniquely of the
form e followed by a pointwise-lower-part automorphism. -/
theorem localCodeFibre_eq_automorphism_image
    (P : Finset V) {n : ℕ} (e : Fin n ≃ V) :
    O.localCodeFibre P e =
      (O.pointwiseLowerAutomorphisms P).image (fun h => e.trans h) := by
  classical
  ext f
  rw [O.mem_localCodeFibre_iff P e f]
  constructor
  · intro hf
    let h : Equiv.Perm V := e.symm.trans f
    have hh : h ∈ O.pointwiseLowerAutomorphisms P :=
      (O.codeAndLower_iff_mem_pointwiseAut P e f).mp hf
    have heq : e.trans h = f := by
      apply Equiv.ext
      intro i
      simp [h, Equiv.trans_apply]
    exact Finset.mem_image.mpr ⟨h, hh, heq⟩
  · intro hf
    obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp hf
    subst f
    apply (O.codeAndLower_iff_mem_pointwiseAut P e (e.trans h)).mpr
    have hId : e.symm.trans (e.trans h) = h := by
      apply Equiv.ext
      intro x
      obtain ⟨i, rfl⟩ := e.surjective x
      simp [Equiv.trans_apply]
    rw [hId]
    exact hh

/-- The exact cardinality of the local code fibre is the order
of the pointwise stabilizer of the lower part. -/
theorem localCodeFibre_card (P : Finset V) {n : ℕ}
    (e : Fin n ≃ V) :
    (O.localCodeFibre P e).card =
      (O.pointwiseLowerAutomorphisms P).card := by
  classical
  rw [O.localCodeFibre_eq_automorphism_image P e]
  apply Finset.card_image_iff.mpr
  intro h hh k hk heq
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ := e.surjective x
  have hi := congrArg (fun f : Fin n ≃ V => f i) heq
  simpa only [Equiv.trans_apply] using hi

end FiniteOrientation
end BigHrushovski
