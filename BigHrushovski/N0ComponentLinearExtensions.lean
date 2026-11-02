import BigHrushovski.N0ComponentLowerPart
import BigHrushovski.N0ComponentRankPrefixes
import Mathlib.Tactic

/-!
# Finite component-linear-extension data for N₀

A component order is a bijection from the actual set of strongly
connected components to a finite ordinal, strictly respecting the
intrinsic component dependency relation. Thus the count ell(A)
is represented literally as a cardinality of linear extensions,
not as the number of arbitrary vertex enumerations.

Independent local choice sets can be assembled over these rankings.
Their data cardinality satisfies the expected product formula. This
is a combinatorial counting interface; identifying this data with
all permitted vertex orders, and proving the infinite Ramsey
statement, remain separate obligations.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The finite type of actual strongly connected components. -/
abbrev ComponentObject : Type _ :=
  {B : Finset V // B ∈ O.components}

/-- A component enumeration by consecutive ordinal positions. -/
abbrev ComponentRanking : Type _ :=
  O.ComponentObject ≃ Fin (Fintype.card O.ComponentObject)

/-- A legal component ranking puts every proper successor
component strictly before the component depending on it. -/
def IsLinearComponentRanking (r : O.ComponentRanking) : Prop :=
  ∀ B C : O.ComponentObject,
    O.ComponentPrecedes B.val C.val → r B < r C

/-- All legal linear extensions of the finite component poset. -/
noncomputable def linearComponentRankings :
    Finset O.ComponentRanking := by
  classical
  exact Finset.univ.filter O.IsLinearComponentRanking

theorem mem_linearComponentRankings
    (r : O.ComponentRanking) :
    r ∈ O.linearComponentRankings ↔
      O.IsLinearComponentRanking r := by
  classical
  simp [linearComponentRankings]

/-- The finite component-order count from the manuscript. -/
noncomputable def componentLinearExtensionCount : ℕ :=
  O.linearComponentRankings.card

/-- Extend the consecutive component ranks arbitrarily outside
the actual component set; the dummy value is never used for
a component that appears in the graph. -/
noncomputable def componentRankOnAll
    (r : O.ComponentRanking) (B : Finset V) : ℕ :=
  if hB : B ∈ O.components then (r ⟨B, hB⟩).val else 0

theorem componentRankOnAll_respects
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r) :
    O.RespectsComponentDependencies (O.componentRankOnAll r) := by
  intro B C hBC
  obtain ⟨lower, upper, hB, hC, hProper⟩ := hBC
  have hBm : B ∈ O.components := by
    rw [← hB]
    exact O.component_mem_components lower
  have hCm : C ∈ O.components := by
    rw [← hC]
    exact O.component_mem_components upper
  have hRank := hr ⟨B, hBm⟩ ⟨C, hCm⟩
    ⟨lower, upper, hB, hC, hProper⟩
  simpa [componentRankOnAll, hBm, hCm, Fin.lt_def] using hRank

/-- Every prefix of a finite component linear extension is
successor-closed. -/
theorem linearComponentPrefix_isClosed
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r) (n : ℕ) :
    O.IsSuccessorClosed
      (O.componentRankPrefix (O.componentRankOnAll r) n) :=
  O.componentRankPrefix_isSuccessorClosed
    (O.componentRankOnAll r)
    (O.componentRankOnAll_respects r hr) n

/-- Each such prefix is also strong in the underlying graph. -/
theorem linearComponentPrefix_isStrong
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r) (n : ℕ) :
    O.underlying.toPredimension.IsStrong
      (O.componentRankPrefix (O.componentRankOnAll r) n) Finset.univ :=
  O.componentRankPrefix_isStrong
    (O.componentRankOnAll r)
    (O.componentRankOnAll_respects r hr) n

/-- Independent local choices indexed by actual components.
These are data, not yet the permitted orders of the manuscript. -/
noncomputable def localComponentChoices
    {α : Type*} [DecidableEq α]
    (choices : O.ComponentObject → Finset α) :
    Finset (O.ComponentObject → α) := by
  classical
  exact Finset.univ.pi choices

theorem localComponentChoices_card
    {α : Type*} [DecidableEq α]
    (choices : O.ComponentObject → Finset α) :
    (O.localComponentChoices choices).card =
      ∏ B : O.ComponentObject, (choices B).card := by
  classical
  simp [localComponentChoices]

/-- A linear extension together with an independent choice
from the local option set of each component. -/
noncomputable def finiteOrderData
    {α : Type*} [DecidableEq α]
    (choices : O.ComponentObject → Finset α) :
    Finset (O.ComponentRanking × (O.ComponentObject → α)) :=
  O.linearComponentRankings.product
    (O.localComponentChoices choices)

/-- Exact product count for the finite *data* above. The
remaining mathematical task is a bijection between this
data and permitted linear orders on the actual graph vertices. -/
theorem finiteOrderData_card
    {α : Type*} [DecidableEq α]
    (choices : O.ComponentObject → Finset α) :
    (O.finiteOrderData choices).card =
      O.componentLinearExtensionCount *
        ∏ B : O.ComponentObject, (choices B).card := by
  classical
  simp [finiteOrderData, componentLinearExtensionCount,
    localComponentChoices]

end FiniteOrientation
end BigHrushovski
