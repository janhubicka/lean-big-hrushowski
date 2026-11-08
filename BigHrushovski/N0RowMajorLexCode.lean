import BigHrushovski.N0AllFixedLowerMinimum
import Mathlib.Order.PiLex
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
# Literal lexicographic least complete directed adjacency codes

The printed N0 local order uses the lexicographically least complete
directed adjacency matrix after fixing the already ordered lower part.
The earlier complete matrix index was arbitrary, and thus only
proved order-independent fibre cardinality.

This module uses the real *row-major lexicographic order*: each row
is a lexicographically ordered Bool vector indexed by Fin n and the
rows themselves form another lexicographically ordered vector.
Equality of these nested lex codes is equivalent to equality of
every directed edge/nonedge entry. The general minimum-fibre theorem
then gives the precise stabilizer cardinality for the literal
lexicographic minimum among all enumerations fixing old positions.

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

/-- Literal *lexicographically least* complete-code fibre for all
pointwise fixed-lower-position enumerations has the size of the
pointwise lower-part automorphism group, independently of the
chosen preliminary order of the old part. -/
theorem allFixedLowerMinimumLexCode_card {n : ℕ}
    (P : Finset V) (base : Fin n ≃ V) :
    (O.minimumCodeClass (fixedLowerEnumerations P base)
      O.completeRowMajorLexCode
      (fixedLowerEnumerations_nonempty P base)).card =
      (O.pointwiseLowerAutomorphisms P).card := by
  exact O.fixedLowerMinimumCodeClass_card P base O.completeRowMajorLexCode
    (fun e f => O.completeRowMajorLexCode_eq_iff e f)

end FiniteOrientation
end BigHrushovski
