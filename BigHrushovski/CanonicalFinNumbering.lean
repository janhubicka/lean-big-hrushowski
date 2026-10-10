import BigHrushovski.InitialSegmentLabels

/-!
# The canonical initial-segment numbering of Fin n

The gap-free extension theorem takes an equivalence between the old
finite carrier and Fin(card old). When the old carrier is already Fin n,
we need the equivalence preserving each *numerical* old vertex label.
An arbitrary Fintype.equivFin may permute the old labels and so is
not suitable for a coherent Nat-labelled Fraisse construction.
-/

namespace BigHrushovski
namespace FiniteSpan

/-- The size of Fin n is n, with no arbitrary enumeration of vertices. -/
noncomputable def canonicalFinNumbering (n : ℕ) :
    Fin n ≃ Fin (Fintype.card (Fin n)) :=
  finCongr (Fintype.card_fin n).symm

/-- The canonical numbering fixes the numerical label of every vertex. -/
@[simp] theorem canonicalFinNumbering_val (n : ℕ) (x : Fin n) :
    (canonicalFinNumbering n x).val = x.val := by
  rfl

end FiniteSpan
end BigHrushovski
