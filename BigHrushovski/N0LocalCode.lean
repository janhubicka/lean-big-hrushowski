import BigHrushovski.N0LocalSymmetry
import Mathlib.Tactic

/-!
# Adjacency codes and the local stabilizer factor

For two complete finite enumerations e,f of the same oriented
closure, equality of their complete adjacency matrices means
precisely that the change of enumeration e.symm.trans f is a
digraph automorphism. Requiring the enumerations to agree at
positions occupied by the old successor part P means that this
automorphism fixes P pointwise.

This identifies the local canonical-matrix equivalence class
with the pointwise stabilizer already counted in
N0LocalSymmetry.lean. It does not yet identify all permitted
global orders or establish the infinite degree-one theorem.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Equality of the entire directed adjacency matrices under
two enumerations of the same finite oriented graph. -/
def SameOrientedCode {n : ℕ}
    (e f : Fin n ≃ V) : Prop :=
  ∀ i j : Fin n,
    (e j ∈ O.out (e i)) ↔ (f j ∈ O.out (f i))

/-- Every position of the old part P is left untouched by
the change of enumeration. This is pointwise, not setwise,
agreement of the lower part. -/
def SameLowerPositions {n : ℕ}
    (P : Finset V) (e f : Fin n ≃ V) : Prop :=
  ∀ i : Fin n, e i ∈ P → f i = e i

/-- Complete matrix agreement is equivalent to preservation and
reflection of every directed edge by the change-of-enumeration
permutation. -/
theorem sameOrientedCode_iff_automorphism {n : ℕ}
    (e f : Fin n ≃ V) :
    O.SameOrientedCode e f ↔
      (∀ x y : V,
        y ∈ O.out x ↔
          (e.symm.trans f) y ∈ O.out ((e.symm.trans f) x)) := by
  constructor
  · intro h x y
    obtain ⟨i, rfl⟩ := e.surjective x
    obtain ⟨j, rfl⟩ := e.surjective y
    simpa [Equiv.trans_apply, SameOrientedCode] using h i j
  · intro h i j
    simpa [Equiv.trans_apply] using h (e i) (e j)

/-- Agreement at all old positions is exactly pointwise
fixation of the lower part. -/
theorem sameLowerPositions_iff_fixed {n : ℕ}
    (P : Finset V) (e f : Fin n ≃ V) :
    SameLowerPositions P e f ↔
      (∀ x : V, x ∈ P → (e.symm.trans f) x = x) := by
  constructor
  · intro h x hx
    obtain ⟨i, rfl⟩ := e.surjective x
    simpa [Equiv.trans_apply] using h i hx
  · intro h i hi
    simpa [Equiv.trans_apply] using h (e i) hi

/-- The exact local dictionary between complete orientation
codes and pointwise lower-part automorphisms. -/
theorem codeAndLower_iff_pointwiseAut {n : ℕ}
    (P : Finset V) (e f : Fin n ≃ V) :
    (O.SameOrientedCode e f ∧ SameLowerPositions P e f) ↔
      O.IsPointwiseLowerAutomorphism P (e.symm.trans f) := by
  constructor
  · rintro ⟨hCode, hLower⟩
    exact ⟨(O.sameOrientedCode_iff_automorphism e f).mp hCode,
      (sameLowerPositions_iff_fixed P e f).mp hLower⟩
  · rintro ⟨hCode, hLower⟩
    exact ⟨(O.sameOrientedCode_iff_automorphism e f).mpr hCode,
      (sameLowerPositions_iff_fixed P e f).mpr hLower⟩

/-- Equivalently, the change of enumeration lies in the
finite pointwise-stabilizer set. -/
theorem codeAndLower_iff_mem_pointwiseAut {n : ℕ}
    (P : Finset V) (e f : Fin n ≃ V) :
    (O.SameOrientedCode e f ∧ SameLowerPositions P e f) ↔
      e.symm.trans f ∈ O.pointwiseLowerAutomorphisms P := by
  classical
  constructor
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
       (O.codeAndLower_iff_pointwiseAut P e f).mp h⟩
  · intro h
    exact (O.codeAndLower_iff_pointwiseAut P e f).mpr
      (Finset.mem_filter.mp h).2

/-- A local enumeration has the canonical complete code and the
same old positions if and only if it is a transport of the
chosen representative by a pointwise lower-part automorphism. -/
theorem codeAndLower_iff_transported {n : ℕ}
    (P : Finset V) (e f : Fin n ≃ V) :
    (O.SameOrientedCode e f ∧ SameLowerPositions P e f) ↔
      ∃ h : Equiv.Perm V,
        h ∈ O.pointwiseLowerAutomorphisms P ∧
        (∀ i : Fin n, f i = h (e i)) := by
  constructor
  · intro hCode
    let h : Equiv.Perm V := e.symm.trans f
    refine ⟨h, (O.codeAndLower_iff_mem_pointwiseAut P e f).mp hCode, ?_⟩
    intro i
    simp [h, Equiv.trans_apply]
  · rintro ⟨h, hh, hMap⟩
    have hEq : e.symm.trans f = h := by
      apply Equiv.ext
      intro x
      obtain ⟨i, rfl⟩ := e.surjective x
      simpa [Equiv.trans_apply] using hMap i
    apply (O.codeAndLower_iff_mem_pointwiseAut P e f).mpr
    rw [hEq]
    exact hh

end FiniteOrientation
end BigHrushovski
