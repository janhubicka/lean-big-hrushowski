import BigHrushovski.N0StageGeneratorFibreCount
import Mathlib.Tactic

/-!
# From the generator fibre to actual canonical next-component choices

The existing definition of actual next-component choices checks the
canonical complete-code condition at every generator of the SCC.
The uniform local count theorem uses one chosen generator.

This module makes the only intervening hypothesis explicit:
the all-generator test is equivalent to the test at that chosen
generator. Under this hypothesis, the actual permitted next-component
choice set has exactly the required stabilizer cardinality.

The generator-independence theorem is developed separately.
No assertion is made here that the hypothesis is already certified.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Conditional uniform count for the *original concrete*
next-SCC choice set, making the generator-transport hypothesis
an explicit input rather than silently changing the predicate. -/
theorem canonicalNextComponentChoices_card_of_generatorCriterion
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (hCriterion :
      ∀ choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val),
        O.IsCanonicalAtComponent r
          (O.withComponentOrder orders B choice) B ↔
        (let e := O.stageClosureFromTop r orders B choice;
          e ∈ O.canonicalComponentLexClass
            (O.componentGenerator B) e)) :
    (O.canonicalNextComponentChoices r orders B).card =
      O.componentLocalFactor B := by
  have hSets :
      O.canonicalNextComponentChoices r orders B =
        O.canonicalNextGeneratorChoices r orders B := by
    classical
    ext choice
    rw [O.mem_canonicalNextComponentChoices]
    exact (hCriterion choice).trans
      (O.canonicalGeneratorTest_iff_fixedBase r hr orders B choice)
  rw [hSets]
  exact O.canonicalNextGeneratorChoices_card r hr orders B

/-- The same conditional count for *whole assignment records*:
different chosen orders of B give different updated assignments.
No numerical synthetic factor choices are introduced. -/
theorem canonicalNextComponentAssignments_card_of_generatorCriterion
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (hCriterion :
      ∀ choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val),
        O.IsCanonicalAtComponent r
          (O.withComponentOrder orders B choice) B ↔
        (let e := O.stageClosureFromTop r orders B choice;
          e ∈ O.canonicalComponentLexClass
            (O.componentGenerator B) e)) :
    (O.canonicalNextComponentAssignments r orders B).card =
      O.componentLocalFactor B := by
  calc
    (O.canonicalNextComponentAssignments r orders B).card =
        (O.canonicalNextComponentChoices r orders B).card :=
      O.canonicalNextComponentAssignments_card r orders B
    _ = O.componentLocalFactor B :=
      O.canonicalNextComponentChoices_card_of_generatorCriterion
        r hr orders B hCriterion

end FiniteOrientation
end BigHrushovski
