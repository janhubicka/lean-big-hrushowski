import BigHrushovski.N0LocalCodeFibre
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Finite enumerations and actual linear orders

An enumeration e : Fin n ≃ V induces the strict linear order on
the labelled vertex set V given by comparing the inverse ranks
of its vertices. Two enumerations give the same order relation
if and only if the enumerations are literally equal.

Consequently the already-verified local code fibre, counted by
the pointwise stabilizer, consists of that many **distinct labelled
linear orders**, rather than merely that many enumerations.

The theorem does not count globally permitted N₀ orders or prove
the infinite big Ramsey degree formula.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The strict order on the fixed labelled vertex set induced
by the enumeration e. -/
def OrderBefore {n : ℕ} (e : Fin n ≃ V) (x y : V) : Prop :=
  e.symm x < e.symm y

theorem orderBefore_irrefl {n : ℕ} (e : Fin n ≃ V) (x : V) :
    ¬ OrderBefore e x x :=
  lt_irrefl _

theorem orderBefore_trans {n : ℕ} (e : Fin n ≃ V)
    {x y z : V}
    (hxy : OrderBefore e x y) (hyz : OrderBefore e y z) :
    OrderBefore e x z :=
  lt_trans hxy hyz

theorem orderBefore_total {n : ℕ} (e : Fin n ≃ V)
    {x y : V} (hxy : x ≠ y) :
    OrderBefore e x y ∨ OrderBefore e y x := by
  have hxy' : e.symm x ≠ e.symm y := by
    intro h
    exact hxy (e.symm.injective h)
  exact lt_or_gt_of_ne hxy'

/-- Equality of the induced order relations implies equality
of complete finite enumerations. No automorphism quotient is
taken when counting labelled linear orders. -/
theorem enumeration_eq_of_same_order {n : ℕ}
    (e f : Fin n ≃ V)
    (hsame : ∀ x y : V, OrderBefore e x y ↔ OrderBefore f x y) :
    e = f := by
  let σ : Fin n ≃ Fin n := f.trans e.symm
  have hlt (i j : Fin n) : σ i < σ j ↔ i < j := by
    have h := hsame (f i) (f j)
    simpa [OrderBefore, σ, Equiv.trans_apply] using h
  have hle (i j : Fin n) : (i ≤ j) ↔ (σ i ≤ σ j) := by
    constructor
    · intro hij
      rcases lt_or_eq_of_le hij with hij | hij
      · exact ((hlt i j).mpr hij).le
      · simpa [hij]
    · intro hij
      rcases lt_or_eq_of_le hij with hij | hij
      · exact ((hlt i j).mp hij).le
      · exact le_of_eq (σ.injective hij)
  let E : Fin n ≃o Fin n :=
    { toEquiv := σ, map_rel_iff' := hle }
  have hid (i : Fin n) : σ i = i := by
    have h := Fin.coe_orderIso_apply E i
    change (σ i : ℕ) = (i : ℕ) at h
    exact Fin.ext h
  apply Equiv.ext
  intro i
  have hefi : f i = e i := by
    have h := congrArg e (hid i)
    simpa [σ, Equiv.trans_apply] using h
  exact hefi.symm

theorem sameOrder_iff_eq {n : ℕ}
    (e f : Fin n ≃ V) :
    (∀ x y : V, OrderBefore e x y ↔ OrderBefore f x y) ↔
      e = f := by
  constructor
  · exact enumeration_eq_of_same_order e f
  · intro h
    subst f
    intro x y
    rfl

theorem orderBefore_injective {n : ℕ} :
    Function.Injective
      (fun e : Fin n ≃ V => OrderBefore e) := by
  intro e f h
  apply enumeration_eq_of_same_order e f
  intro x y
  have hxy : OrderBefore e x y = OrderBefore f x y :=
    congrFun (congrFun h x) y
  exact ⟨fun hp => hxy ▸ hp, fun hq => hxy.symm ▸ hq⟩

variable (O : FiniteOrientation V)

/-- This is a set of actual strict linear order relations
on the fixed vertex set, not an isomorphism-class quotient. -/
noncomputable def localCodeOrderRelations
    (P : Finset V) {n : ℕ} (e : Fin n ≃ V) :
    Finset (V → V → Prop) := by
  classical
  exact (O.localCodeFibre P e).image OrderBefore

/-- The number of *distinct labelled strict linear orders*
from the complete local adjacency-code fibre is exactly
the pointwise lower-part stabilizer cardinality. -/
theorem localCodeOrderRelations_card
    (P : Finset V) {n : ℕ} (e : Fin n ≃ V) :
    (O.localCodeOrderRelations P e).card =
      (O.pointwiseLowerAutomorphisms P).card := by
  classical
  change ((O.localCodeFibre P e).image OrderBefore).card =
    (O.pointwiseLowerAutomorphisms P).card
  rw [Finset.card_image_iff.mpr ?_]
  · exact O.localCodeFibre_card P e
  · intro f hf g hg h
    exact orderBefore_injective h

end FiniteOrientation
end BigHrushovski
