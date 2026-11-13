import BigHrushovski.N0GeneratorCanonicality
import BigHrushovski.N0StageActualFibreInterface
import BigHrushovski.N0TaggedHistoryCount

/-!
# Uniform finite SCC-choice counts, without generator hypotheses

For a legal SCC ranking and an arbitrary family of actual labelled
component orders, generator independence identifies the original
all-generator canonicality predicate with its chosen-generator test.
The existing fixed-old enumeration bijection then gives the true
local stabilizer factor for every context.

Applying the reachable-history counting lemma yields the product
for genuine dependent tagged SCC-choice histories. This does not
identify the histories with all permitted global vertex orders, and
it does not prove an infinite Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The actual all-generator next-component choice set has cardinality
the full lower-part stabilizer factor, with no generator-equivalence
hypothesis left in the statement. -/
theorem canonicalNextComponentChoices_card_unconditional
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    (O.canonicalNextComponentChoices r orders B).card =
      O.componentLocalFactor B := by
  apply O.canonicalNextComponentChoices_card_of_generatorCriterion
    r hr orders B
  intro choice
  simpa only [stageClosureFromTop] using
    (O.isCanonicalAtComponent_iff_generator r
      (O.withComponentOrder orders B choice) B)

/-- Uniform finite product for reachable dependent histories of
actual labelled SCC-order choices along a fixed legal component
ranking. The final history-to-permitted-global-order bijection is
not claimed by this theorem. -/
theorem reachableTaggedHistories_card_unconditional
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r) :
    (BigHrushovski.FiniteChoiceHistory.reachableHistories
      (O.canonicalTaggedNextChoices r)
      (Fintype.card O.ComponentObject)).card =
      ∏ i ∈ Finset.range (Fintype.card O.ComponentObject),
        O.rankLocalFactor r i := by
  apply O.reachableTaggedHistories_card_of_uniform r
  intro orders B
  exact O.canonicalNextComponentChoices_card_unconditional
    r hr orders B

end FiniteOrientation
end BigHrushovski
