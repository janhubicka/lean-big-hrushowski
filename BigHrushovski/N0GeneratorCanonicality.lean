import BigHrushovski.N0CanonicalStageChoices
import Mathlib.Tactic

/-!
# Canonical closure orders depend only on the SCC

For a finite orientation O, the complete successor closure C_x and
strict lower part P_x of a vertex x depend only on the strongly
connected component containing x. Consequently, for any fixed
global labelled enumeration, the canonical complete-code test
of the induced C_x order has the same truth value for every
generator of one SCC.

Thus the definition of a canonical next-SCC choice, which originally
quantified over every vertex of the SCC, is equivalent to checking
one actual chosen component generator. This is useful for applying
the local fixed-old enumeration fibre theorem without duplicating
the dependent subtype carrier.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Canonicality of the complete induced closure enumeration depends
only on the strongly connected component, not on its generator.
The complete adjacency code (including nonedges) is unchanged. -/
theorem canonicalClosureMembership_iff_of_component_eq
    {n : ℕ} (global : Fin n ≃ V)
    {x y : V} (hComp : O.component x = O.component y) :
    (O.inheritedComponentEnumeration global x ∈
      O.canonicalComponentLexClass x
        (O.inheritedComponentEnumeration global x)) ↔
    (O.inheritedComponentEnumeration global y ∈
      O.canonicalComponentLexClass y
        (O.inheritedComponentEnumeration global y)) := by
  classical
  dsimp only [inheritedComponentEnumeration,
    canonicalComponentLexClass, inducedComponentOrientation,
    inducedLowerPart, lowerPart, componentClosure]
  rw [hComp]

/-- The actual chosen generator belongs to the SCC which it names. -/
theorem componentGenerator_mem (B : O.ComponentObject) :
    O.componentGenerator B ∈ B.val := by
  rw [← O.componentGenerator_spec B]
  exact O.self_mem_component (O.componentGenerator B)

/-- The componentwise canonical predicate can be checked at its
chosen generator, without changing the admissible set of labelled
component-order assignments. -/
theorem isCanonicalAtComponent_iff_generator
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    O.IsCanonicalAtComponent r orders B ↔
      (let e := O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders)
        (O.componentGenerator B);
       e ∈ O.canonicalComponentLexClass
         (O.componentGenerator B) e) := by
  constructor
  · intro h
    exact h (O.componentGenerator B) (O.componentGenerator_mem B)
  · intro h y hy
    have hComp :
        O.component (O.componentGenerator B) = O.component y := by
      have hyComp := O.component_eq_of_mem_componentObject B hy
      exact (O.componentGenerator_spec B).trans hyComp.symm
    exact (O.canonicalClosureMembership_iff_of_component_eq
      (O.assembleComponentEnumerations r orders) hComp).mp h

/-- Membership in the genuine next-SCC choice set reduces to one
canonical complete closure test, at the chosen generator of B. -/
theorem mem_canonicalNextComponentChoices_iff_generator
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    choice ∈ O.canonicalNextComponentChoices r orders B ↔
      (let e := O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r
          (O.withComponentOrder orders B choice))
        (O.componentGenerator B);
       e ∈ O.canonicalComponentLexClass
         (O.componentGenerator B) e) := by
  exact (O.mem_canonicalNextComponentChoices
    r orders B choice).trans
    (O.isCanonicalAtComponent_iff_generator r
      (O.withComponentOrder orders B choice) B)

end FiniteOrientation
end BigHrushovski
