import BigHrushovski.N0MinimumCodeClass
import Mathlib.Tactic

/-!
# Canonical finite code fibres over a literally fixed lower part

For a fixed enumeration e of a finite oriented closure C and a finite
old part P, consider *all* complete enumerations which agree with e at
the positions occupied by P. Agreement is automatically symmetric and
transitive: injectivity rules out a new vertex entering an old position.
Consequently this family is closed under the pointwise stabilizer of P.

The least class of any *complete* adjacency code therefore has precisely
the pointwise stabilizer cardinality, without independently postulating
closure of the admissible family or agreement between each two members.

A finite ordinal index of the entire Boolean directed adjacency matrix
supplies one concrete complete code. Its chosen index order need not be
the manuscript's lexicographic order. The cardinality is independent of
the choice of linear order on complete codes.

This is a finite local assertion only. It does not reconstruct all
permitted global vertex orders and does not prove a big Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Positionwise agreement on P is symmetric for bijective enumerations.
The proof uses surjectivity of the base and injectivity of the second
enumeration, not merely setwise preservation of P. -/
theorem sameLowerPositions_symm {n : ℕ} (P : Finset V)
    (e f : Fin n ≃ V)
    (hef : SameLowerPositions P e f) :
    SameLowerPositions P f e := by
  intro i hfi
  obtain ⟨j, hj⟩ := e.surjective (f i)
  have hjP : e j ∈ P := by simpa only [hj] using hfi
  have hfj : f j = f i := (hef j hjP).trans hj
  have hji : j = i := f.injective hfj
  subst j
  exact hj

/-- Transitivity of pointwise old-position agreement. -/
theorem sameLowerPositions_trans {n : ℕ} (P : Finset V)
    (e f g : Fin n ≃ V)
    (hef : SameLowerPositions P e f)
    (hfg : SameLowerPositions P f g) :
    SameLowerPositions P e g := by
  intro i hei
  have hfi : f i ∈ P := by
    rw [hef i hei]
    exact hei
  exact (hfg i hfi).trans (hef i hei)

/-- All complete enumerations that agree with the chosen base at old
positions. Every vertex outside P can be rearranged. -/
noncomputable def fixedLowerEnumerations {n : ℕ}
    (P : Finset V) (base : Fin n ≃ V) :
    Finset (Fin n ≃ V) := by
  classical
  exact Finset.univ.filter (SameLowerPositions P base)

theorem mem_fixedLowerEnumerations_iff {n : ℕ}
    (P : Finset V) (base f : Fin n ≃ V) :
    f ∈ fixedLowerEnumerations P base ↔
      SameLowerPositions P base f := by
  classical
  simp [fixedLowerEnumerations]

theorem fixedLowerEnumerations_nonempty {n : ℕ}
    (P : Finset V) (base : Fin n ≃ V) :
    (fixedLowerEnumerations P base).Nonempty := by
  refine ⟨base, (mem_fixedLowerEnumerations_iff P base base).mpr ?_⟩
  intro i hi
  rfl

variable (O : FiniteOrientation V)

/-- The local family of all fixed-lower-position enumerations satisfies
both conditions needed for the minimum complete-code fibre theorem. -/
theorem fixedLowerMinimumCodeClass_card {n : ℕ} {κ : Type*}
    [LinearOrder κ] (P : Finset V) (base : Fin n ≃ V)
    (code : (Fin n ≃ V) → κ)
    (hComplete : ∀ e f : Fin n ≃ V,
      code e = code f ↔ O.SameOrientedCode e f) :
    (O.minimumCodeClass (fixedLowerEnumerations P base) code
      (fixedLowerEnumerations_nonempty P base)).card =
      (O.pointwiseLowerAutomorphisms P).card := by
  classical
  refine O.minimumCodeClass_card P
    (fixedLowerEnumerations P base) code
    (fixedLowerEnumerations_nonempty P base) ?_ ?_ hComplete
  · intro f hf g hg
    have hbf : SameLowerPositions P base f :=
      (mem_fixedLowerEnumerations_iff P base f).mp hf
    have hbg : SameLowerPositions P base g :=
      (mem_fixedLowerEnumerations_iff P base g).mp hg
    exact sameLowerPositions_trans P f base g
      (sameLowerPositions_symm P base f hbf) hbg
  · intro f hf g hg
    have hbf : SameLowerPositions P base f :=
      (mem_fixedLowerEnumerations_iff P base f).mp hf
    have hfg : SameLowerPositions P f g :=
      (O.mem_localCodeFibre_iff P f g).mp hg |>.2
    apply (mem_fixedLowerEnumerations_iff P base g).mpr
    exact sameLowerPositions_trans P base f g hbf hfg

/-- Encode the entire finite Boolean directed adjacency matrix by a
finite ordinal, using a fixed bijection of matrix tables. Equality of
indices is exactly equality of complete oriented codes; no claim is
made that the chosen ordinal order is lexicographic. -/
noncomputable def fullMatrixIndex {n : ℕ} (e : Fin n ≃ V) :
    Fin (Fintype.card (Fin n → Fin n → Bool)) :=
  (Fintype.equivFin (Fin n → Fin n → Bool))
    (O.completeDirectedMatrix e)

theorem fullMatrixIndex_eq_iff {n : ℕ} (e f : Fin n ≃ V) :
    O.fullMatrixIndex e = O.fullMatrixIndex f ↔
      O.SameOrientedCode e f := by
  constructor
  · intro h
    apply (O.completeDirectedMatrix_eq_iff e f).mp
    exact (Fintype.equivFin (Fin n → Fin n → Bool)).injective h
  · intro h
    exact congrArg (Fintype.equivFin (Fin n → Fin n → Bool))
      ((O.completeDirectedMatrix_eq_iff e f).mpr h)

/-- A fully instantiated finite minimum-code count. The family, its
old-position agreement, its stabilizer closure, and the complete code
are now all concrete, not assumed hypotheses. -/
theorem allFixedLowerMinimumMatrixCode_card {n : ℕ}
    (P : Finset V) (base : Fin n ≃ V) :
    (O.minimumCodeClass (fixedLowerEnumerations P base)
      O.fullMatrixIndex
      (fixedLowerEnumerations_nonempty P base)).card =
      (O.pointwiseLowerAutomorphisms P).card := by
  exact O.fixedLowerMinimumCodeClass_card P base O.fullMatrixIndex
    (fun e f => O.fullMatrixIndex_eq_iff e f)

end FiniteOrientation
end BigHrushovski
