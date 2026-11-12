import BigHrushovski.N0ActualLocalFactors
import BigHrushovski.N0RowMajorLexCode
import Mathlib.Tactic

/-!
# Canonical local orders on actual one-component closures

For a strongly connected component B, write C_B for its complete successor
closure and P_B for the strict lower part. On the *induced* orientation on C_B,
fix any enumeration of P_B. Among all complete enumerations keeping the old
positions fixed, choose those with lexicographically least complete directed
adjacency matrix.

The resulting local class has cardinality g_A(B), the pointwise stabilizer
of P_B in Aut(A[C_B]). It depends only on the ordered lower part, not on the
arbitrary initial enumeration of the remaining vertices.

These are finite local statements. Identifying the resulting choices with
the globally permitted orders, and the infinite N0 Ramsey theorem, remain
separate obligations.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The family of complete enumerations fixing the ordered old positions
does not depend on how the other vertices were listed in the base. -/
theorem fixedLowerEnumerations_eq_of_sameLowerPositions
    (P : Finset V) {n : ℕ} (base₁ base₂ : Fin n ≃ V)
    (hbase : SameLowerPositions P base₁ base₂) :
    fixedLowerEnumerations P base₁ =
      fixedLowerEnumerations P base₂ := by
  classical
  ext f
  rw [mem_fixedLowerEnumerations_iff P base₁ f,
    mem_fixedLowerEnumerations_iff P base₂ f]
  constructor
  · intro hf
    exact sameLowerPositions_trans P base₂ base₁ f
      (sameLowerPositions_symm P base₁ base₂ hbase) hf
  · intro hf
    exact sameLowerPositions_trans P base₁ base₂ f hbase hf

/-- Equality of finite choice sets transports their minimum-code
classes. The nonemptiness proofs are proof-irrelevant, so this avoids
rewriting through a dependent nonemptiness argument. -/
theorem minimumCodeClass_eq_of_choice_set_eq
    {n : ℕ} {κ : Type*} [LinearOrder κ]
    (S T : Finset (Fin n ≃ V))
    (code : (Fin n ≃ V) → κ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : S = T) :
    minimumCodeClass S code hS =
      minimumCodeClass T code hT := by
  cases hST
  rfl

variable (O : FiniteOrientation V)

/-- The actual local canonical class: full row-major lexicographic
minimizers in the induced one-component closure, for a prescribed
ordering of the lower successor part. -/
noncomputable def canonicalComponentLexClass (x : V) {n : ℕ}
    (base : Fin n ≃ O.componentClosure x) :
    Finset (Fin n ≃ O.componentClosure x) := by
  classical
  exact minimumCodeClass
    (fixedLowerEnumerations (O.inducedLowerPart x) base)
    ((O.inducedComponentOrientation x).completeRowMajorLexCode)
    (fixedLowerEnumerations_nonempty (O.inducedLowerPart x) base)

/-- Every canonical local enumeration agrees at each old position with
the prescribed enumeration, not merely on the old vertex set. -/
theorem canonicalComponentLexClass_fixedLower
    (x : V) {n : ℕ}
    (base f : Fin n ≃ O.componentClosure x)
    (hf : f ∈ O.canonicalComponentLexClass x base) :
    SameLowerPositions (O.inducedLowerPart x) base f := by
  change f ∈ minimumCodeClass
    (fixedLowerEnumerations (O.inducedLowerPart x) base)
    ((O.inducedComponentOrientation x).completeRowMajorLexCode)
    (fixedLowerEnumerations_nonempty (O.inducedLowerPart x) base) at hf
  have hmem := (mem_minimumCodeClass_iff
    (fixedLowerEnumerations (O.inducedLowerPart x) base)
    ((O.inducedComponentOrientation x).completeRowMajorLexCode)
    (fixedLowerEnumerations_nonempty (O.inducedLowerPart x) base) f).mp hf
  exact (mem_fixedLowerEnumerations_iff
    (O.inducedLowerPart x) base f).mp hmem.1

/-- Replacing the arbitrary base enumeration without changing its
ordered lower part leaves the *entire* canonical local class unchanged. -/
theorem canonicalComponentLexClass_eq_of_sameLowerPositions
    (x : V) {n : ℕ}
    (base₁ base₂ : Fin n ≃ O.componentClosure x)
    (hbase : SameLowerPositions (O.inducedLowerPart x) base₁ base₂) :
    O.canonicalComponentLexClass x base₁ =
      O.canonicalComponentLexClass x base₂ := by
  exact minimumCodeClass_eq_of_choice_set_eq
    (fixedLowerEnumerations (O.inducedLowerPart x) base₁)
    (fixedLowerEnumerations (O.inducedLowerPart x) base₂)
    ((O.inducedComponentOrientation x).completeRowMajorLexCode)
    (fixedLowerEnumerations_nonempty (O.inducedLowerPart x) base₁)
    (fixedLowerEnumerations_nonempty (O.inducedLowerPart x) base₂)
    (fixedLowerEnumerations_eq_of_sameLowerPositions
      (O.inducedLowerPart x) base₁ base₂ hbase)

/-- The exact local canonical-order cardinality, in the induced
orientation on C_B rather than the ambient graph. -/
theorem canonicalComponentLexClass_card
    (x : V) {n : ℕ}
    (base : Fin n ≃ O.componentClosure x) :
    (O.canonicalComponentLexClass x base).card =
      O.actualLocalFactor x := by
  simpa only [canonicalComponentLexClass, actualLocalFactor,
    actualLocalStabilizer] using
    (O.inducedComponentOrientation x).allFixedLowerMinimumLexCode_card
      (O.inducedLowerPart x) base

/-- There is always a canonical local enumeration. -/
theorem canonicalComponentLexClass_nonempty
    (x : V) {n : ℕ}
    (base : Fin n ≃ O.componentClosure x) :
    (O.canonicalComponentLexClass x base).Nonempty := by
  apply Finset.card_pos.mp
  rw [O.canonicalComponentLexClass_card x base]
  exact O.actualLocalFactor_pos x

/-- Every canonical minimum-code class is exactly the orbit of any
one of its members under the pointwise stabilizer of the lower part.
Unlike the cardinal theorem, this identifies the actual *set* of
admissible local enumerations. -/
set_option maxHeartbeats 800000 in
theorem canonicalComponentLexClass_eq_automorphism_orbit_of_mem
    (x : V) {n : ℕ}
    (base e : Fin n ≃ O.componentClosure x)
    (he : e ∈ O.canonicalComponentLexClass x base) :
    O.canonicalComponentLexClass x base =
      ((O.inducedComponentOrientation x).pointwiseLowerAutomorphisms
        (O.inducedLowerPart x)).image (fun h => e.trans h) := by
  classical
  let I := O.inducedComponentOrientation x
  let P := O.inducedLowerPart x
  let S := fixedLowerEnumerations P base
  let code : (Fin n ≃ O.componentClosure x) →
      Lex (Fin n → Lex (Fin n → Bool)) :=
    fun t => I.completeRowMajorLexCode t
  have hne : S.Nonempty := fixedLowerEnumerations_nonempty P base
  change e ∈ minimumCodeClass S code hne at he
  have heMin := (mem_minimumCodeClass_iff S code hne e).mp he
  have heOld : SameLowerPositions P base e :=
    (mem_fixedLowerEnumerations_iff P base e).mp heMin.1
  change minimumCodeClass S code hne =
    (I.pointwiseLowerAutomorphisms P).image (fun h => e.trans h)
  calc
    minimumCodeClass S code hne = I.localCodeFibre P e := by
      ext f
      rw [mem_minimumCodeClass_iff S code hne f,
        I.mem_localCodeFibre_iff P e f]
      constructor
      · rintro ⟨hfS, hfMin⟩
        have hfOld : SameLowerPositions P base f :=
          (mem_fixedLowerEnumerations_iff P base f).mp hfS
        have hefCode : code e = code f := heMin.2.trans hfMin.symm
        have hefOld : SameLowerPositions P e f :=
          sameLowerPositions_trans P e base f
            (sameLowerPositions_symm P base e heOld) hfOld
        exact ⟨(I.completeRowMajorLexCode_eq_iff e f).mp hefCode,
          hefOld⟩
      · rintro ⟨hcode, hold⟩
        have hfOld : SameLowerPositions P base f :=
          sameLowerPositions_trans P base e f heOld hold
        have hfS : f ∈ S :=
          (mem_fixedLowerEnumerations_iff P base f).mpr hfOld
        have hefCode : code e = code f :=
          (I.completeRowMajorLexCode_eq_iff e f).mpr hcode
        exact ⟨hfS, hefCode.symm.trans heMin.2⟩
    _ = _ := I.localCodeFibre_eq_automorphism_image P e

/-- A canonical local order exists and generates its whole canonical
class by the pointwise lower-part automorphism action. -/
theorem exists_canonicalComponentLexClass_orbit
    (x : V) {n : ℕ}
    (base : Fin n ≃ O.componentClosure x) :
    ∃ e : Fin n ≃ O.componentClosure x,
      e ∈ O.canonicalComponentLexClass x base ∧
      O.canonicalComponentLexClass x base =
        ((O.inducedComponentOrientation x).pointwiseLowerAutomorphisms
          (O.inducedLowerPart x)).image (fun h => e.trans h) := by
  obtain ⟨e, he⟩ := O.canonicalComponentLexClass_nonempty x base
  exact ⟨e, he, O.canonicalComponentLexClass_eq_automorphism_orbit_of_mem
    x base e he⟩

/-- The formulation indexed by an actual SCC B, instead of a
chosen generator. The generator is used only to name its carrier. -/
noncomputable def componentCanonicalLexClass
    (B : O.ComponentObject) {n : ℕ}
    (base : Fin n ≃ O.componentClosure (O.componentGenerator B)) :
    Finset (Fin n ≃ O.componentClosure (O.componentGenerator B)) :=
  O.canonicalComponentLexClass (O.componentGenerator B) base

/-- The canonical local class for B has cardinality precisely g_A(B). -/
theorem componentCanonicalLexClass_card
    (B : O.ComponentObject) {n : ℕ}
    (base : Fin n ≃ O.componentClosure (O.componentGenerator B)) :
    (O.componentCanonicalLexClass B base).card =
      O.componentLocalFactor B := by
  exact O.canonicalComponentLexClass_card
    (O.componentGenerator B) base

end FiniteOrientation
end BigHrushovski
