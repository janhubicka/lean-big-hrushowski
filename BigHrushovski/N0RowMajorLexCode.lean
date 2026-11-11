import BigHrushovski.N0AllFixedLowerMinimum
import Mathlib.Order.PiLex
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
# Literal lexicographic least complete directed adjacency codes

The manuscript (v52, Section 7.4.4) fixes an ordered representative
for each un-ordered local closure type with its lower part ordered.
It does *not* require lexicographic minimization. Choosing the
lexicographically least complete directed adjacency matrix is one
concrete uniform realization of the permitted representative choice.
The earlier complete matrix index was arbitrary and so proved only
the code-order-independent fibre cardinality.

This module uses the real *row-major lexicographic order*: each row
is a lexicographically ordered Bool vector indexed by Fin n and the
rows themselves form another lexicographically ordered vector.
Equality of these nested lex codes is equivalent to equality of
every directed edge/nonedge entry. The general minimum-fibre theorem then gives the stabilizer
cardinality for the lexicographic minimum among all enumerations
fixing old positions, thus selecting one possible local order orbit.

The old part's positions can be an arbitrary subset of the index set.
In the eventual component-order application they must be an initial
segment; proving that identification and the global order bijection
are still separate tasks. No infinite Ramsey claim is made.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Literal row-major lexicographic code: the outer lex order compares
rows in index order, and the inner lex order compares columns. -/
noncomputable def completeRowMajorLexCode {n : ℕ}
    (e : Fin n ≃ V) :
    Lex (Fin n → Lex (Fin n → Bool)) :=
  toLex (fun i : Fin n =>
    (toLex (O.completeDirectedMatrix e i) :
      Lex (Fin n → Bool)))

/-- Literal lex-code equality detects *all* arrows and nonarrows. -/
theorem completeRowMajorLexCode_eq_iff {n : ℕ}
    (e f : Fin n ≃ V) :
    O.completeRowMajorLexCode e = O.completeRowMajorLexCode f ↔
      O.SameOrientedCode e f := by
  constructor
  · intro h
    have hRows :
        (fun i : Fin n =>
          (toLex (O.completeDirectedMatrix e i) :
            Lex (Fin n → Bool))) =
        (fun i : Fin n =>
          (toLex (O.completeDirectedMatrix f i) :
            Lex (Fin n → Bool))) :=
      congrArg ofLex h
    have hMatrix : O.completeDirectedMatrix e =
        O.completeDirectedMatrix f := by
      funext i j
      have hRow : (toLex (O.completeDirectedMatrix e i) :
          Lex (Fin n → Bool)) =
          (toLex (O.completeDirectedMatrix f i) :
            Lex (Fin n → Bool)) := congrFun hRows i
      exact congrFun (congrArg ofLex hRow) j
    exact (O.completeDirectedMatrix_eq_iff e f).mp hMatrix
  · intro h
    have hMatrix : O.completeDirectedMatrix e =
        O.completeDirectedMatrix f :=
      (O.completeDirectedMatrix_eq_iff e f).mpr h
    exact congrArg
      (fun M : Fin n → Fin n → Bool =>
        (toLex (fun i : Fin n =>
          (toLex (M i) : Lex (Fin n → Bool))) :
          Lex (Fin n → Lex (Fin n → Bool)))) hMatrix

/-- Choosing a *lexicographically least* complete-code fibre among all
pointwise fixed-lower-position enumerations is one valid realization
of the manuscript's fixed-representative convention. Its size equals
the pointwise lower-part automorphism group, for every prescribed
ordering of the old part. -/
theorem allFixedLowerMinimumLexCode_card {n : ℕ}
    (P : Finset V) (base : Fin n ≃ V) :
    (minimumCodeClass (fixedLowerEnumerations P base)
      O.completeRowMajorLexCode
      (fixedLowerEnumerations_nonempty P base)).card =
      (O.pointwiseLowerAutomorphisms P).card := by
  exact O.fixedLowerMinimumCodeClass_card P base O.completeRowMajorLexCode
    (fun e f => O.completeRowMajorLexCode_eq_iff e f)

end FiniteOrientation
end BigHrushovski
