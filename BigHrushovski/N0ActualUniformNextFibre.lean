import BigHrushovski.N0StageGeneratorFibreCount
import BigHrushovski.N0GeneratorCanonicality
import Mathlib.Tactic

/-!
# Uniform canonical next-component fibres for the actual SCC orders

Fix a legal ranking of the actual strongly connected components and
*any* complete family of their internal enumerations. The original
next-component choice set uses the full canonical complete-code
condition, quantified over every vertex of B.

The generator-invariance theorem identifies this predicate with the
test at one component generator. The fixed-old closure-order bijection
and the canonical local code-fibre theorem count those generator choices
by the induced pointwise stabilizer factor g_A(B).

We obtain the unconditional finite statement that the actual concrete
next-component order set has exactly g_A(B) members, uniformly over
all choices of orders on the other components. This is the decisive
local counting ingredient for the finite N₀ expansion formula.

It does not identify chronological histories with complete canonical
assignments and does not prove the infinite big Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The actual next-component choices from PR #497 coincide *as
finite sets* with the generator-based canonical choices from the
fixed-old closure-order bijection. No quotient by automorphisms
or isomorphism classes is used. -/
theorem canonicalNextComponentChoices_eq_generatorChoices
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    O.canonicalNextComponentChoices r orders B =
      O.canonicalNextGeneratorChoices r orders B := by
  classical
  ext choice
  calc
    choice ∈ O.canonicalNextComponentChoices r orders B ↔
        (let e := O.stageClosureFromTop r orders B choice;
          e ∈ O.canonicalComponentLexClass
            (O.componentGenerator B) e) :=
      O.mem_canonicalNextComponentChoices_iff_generator
        r orders B choice
    _ ↔ choice ∈ O.canonicalNextGeneratorChoices r orders B :=
      O.canonicalGeneratorTest_iff_fixedBase r hr orders B choice

/-- **Uniform actual next-SCC fibre theorem.**
For every legal ranking, every complete component-order context,
and every actual strongly connected component B, the number
of permissible labelled internal orders of B is exactly the
pointwise stabilizer cardinality g_A(B) in the induced closure C_B. -/
theorem canonicalNextComponentChoices_card_uniform
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    (O.canonicalNextComponentChoices r orders B).card =
      O.componentLocalFactor B := by
  rw [O.canonicalNextComponentChoices_eq_generatorChoices
    r hr orders B]
  exact O.canonicalNextGeneratorChoices_card r hr orders B

/-- The corresponding finite set of *whole labelled assignments*
obtained by changing B has exactly the same stabilizer cardinality. -/
theorem canonicalNextComponentAssignments_card_uniform
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    (O.canonicalNextComponentAssignments r orders B).card =
      O.componentLocalFactor B := by
  calc
    (O.canonicalNextComponentAssignments r orders B).card =
        (O.canonicalNextComponentChoices r orders B).card :=
      O.canonicalNextComponentAssignments_card r orders B
    _ = O.componentLocalFactor B :=
      O.canonicalNextComponentChoices_card_uniform r hr orders B

/-- In particular there is always at least one permissible next
component order. Positivity comes from the identity automorphism
of the induced closure fixing the lower part pointwise. -/
theorem canonicalNextComponentChoices_nonempty
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    (O.canonicalNextComponentChoices r orders B).Nonempty := by
  apply Finset.card_pos.mp
  rw [O.canonicalNextComponentChoices_card_uniform r hr orders B]
  change 0 < O.actualLocalFactor (O.componentGenerator B)
  exact O.actualLocalFactor_pos (O.componentGenerator B)

end FiniteOrientation
end BigHrushovski
