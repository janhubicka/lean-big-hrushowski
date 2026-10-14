import BigHrushovski.CFStrictLocal

/-!
# Local free-extension transfer for both C0 and CF

Let P be contained in the old vertex set A and let B be a fresh
block. Suppose B has no edges to A \ P. In that case the relative
predimension of every intermediate set over P equals the corresponding
relative predimension over A.

The three exported equivalences express the same elementary
calculation for:
* weak self-sufficiency (strongness);
* strict d-closedness;
* minimal strong extensions.

The minimal strict d-closed extension analogue is not proved here.
The C0 and CF countable functional constructions are also separate.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- The same local no-cross attachment is strong over P if and only
if it is strong after adjoining the larger old graph A. -/
theorem localFreeStrong_iff
    (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B)) :
    G.toPredimension.IsStrong P (P ∪ B) ↔
      G.toPredimension.IsStrong A (A ∪ B) := by
  constructor
  · exact G.enlarged_strong_of_local_strong P A B hPA hDisj hNo
  · exact G.local_strong_of_enlarged_strong P A B hPA hDisj hNo

/-- Strict d-closedness is preserved and reflected by the same free
attachment. No ambient genericity, enumeration or closure bound is used. -/
theorem localFreeDClosed_iff
    (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B)) :
    G.toPredimension.IsDClosed P (P ∪ B) ↔
      G.toPredimension.IsDClosed A (A ∪ B) := by
  constructor
  · exact G.dClosed_enlarged_of_noCross P A B hPA hDisj hNo
  · exact G.dClosed_local_of_noCross P A B hPA hDisj hNo

/-- A single reusable statement of the currently certified strong,
strict d-closed and minimal-strong transfer interfaces. The minimal
d-closed analogue is deliberately not asserted. -/
theorem localFreeTransfer
    (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B)) :
    (G.toPredimension.IsStrong P (P ∪ B) ↔
      G.toPredimension.IsStrong A (A ∪ B)) ∧
    (G.toPredimension.IsDClosed P (P ∪ B) ↔
      G.toPredimension.IsDClosed A (A ∪ B)) ∧
    (G.toPredimension.IsMinimalStrongStep P (P ∪ B) ↔
      G.toPredimension.IsMinimalStrongStep A (A ∪ B)) :=
  ⟨G.localFreeStrong_iff P A B hPA hDisj hNo,
   G.localFreeDClosed_iff P A B hPA hDisj hNo,
   G.minimalStrongStep_free_iff P A B hPA hDisj hNo⟩

end GraphOn
end BigHrushovski
