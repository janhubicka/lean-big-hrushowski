import BigHrushovski.N0StageFixedOldClosureBijection
import Mathlib.Tactic

/-!
# Exact canonical next-order count at an actual SCC generator

Fix a legal ranking of the strongly connected components and any
complete assignment of their internal orders. Let B be one actual SCC
and let x be its chosen generator.

The map from orders of B to complete C_B enumerations, after changing
only B, is a bijection onto the enumerations fixing the old positions
of P_B. The canonical code minimum class in that fixed-old family
has cardinality g_A(B). Its inverse image under the bijection
therefore gives exactly g_A(B) distinct next orders of B.

This module establishes the cardinality for the concrete canonical
test at x. An independent generator-invariance lemma identifies this
test with the existing predicate quantifying over every x in B.
The module does not assume or prove the infinite Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Actual next orders of B whose induced complete C_B enumeration
belongs to the fixed-old canonical minimum-code class determined by
the current context. These are labelled orders of the true B. -/
noncomputable def canonicalNextGeneratorChoices
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    Finset (Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) := by
  classical
  exact Finset.univ.filter (fun choice =>
    O.stageClosureFromTop r orders B choice ∈
      O.canonicalComponentLexClass (O.componentGenerator B)
        (O.stageBaseClosureEnumeration r orders B))

theorem mem_canonicalNextGeneratorChoices
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    choice ∈ O.canonicalNextGeneratorChoices r orders B ↔
      O.stageClosureFromTop r orders B choice ∈
        O.canonicalComponentLexClass (O.componentGenerator B)
          (O.stageBaseClosureEnumeration r orders B) := by
  classical
  simp [canonicalNextGeneratorChoices]

/-- The canonical code criterion with the *current enumeration
itself* as base agrees with the fixed-context canonical class,
because changing the top B order keeps every old position fixed. -/
theorem canonicalGeneratorTest_iff_fixedBase
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    (let e := O.stageClosureFromTop r orders B choice;
      e ∈ O.canonicalComponentLexClass (O.componentGenerator B) e) ↔
    choice ∈ O.canonicalNextGeneratorChoices r orders B := by
  have hOld := O.stageClosureFromTop_fixedLower r hr orders B choice
  have hClasses : O.canonicalComponentLexClass (O.componentGenerator B)
      (O.stageBaseClosureEnumeration r orders B) =
    O.canonicalComponentLexClass (O.componentGenerator B)
      (O.stageClosureFromTop r orders B choice) :=
    O.canonicalComponentLexClass_eq_of_sameLowerPositions
      (O.componentGenerator B)
      (O.stageBaseClosureEnumeration r orders B)
      (O.stageClosureFromTop r orders B choice) hOld
  rw [O.mem_canonicalNextGeneratorChoices]
  change (O.stageClosureFromTop r orders B choice ∈
      O.canonicalComponentLexClass (O.componentGenerator B)
        (O.stageClosureFromTop r orders B choice)) ↔
    (O.stageClosureFromTop r orders B choice ∈
      O.canonicalComponentLexClass (O.componentGenerator B)
        (O.stageBaseClosureEnumeration r orders B))
  rw [hClasses]

/-- The entire canonical fixed-old complete enumeration class is
the exact image of the admissible *labelled top-B orders*.
Both inclusion directions use actual closure enumerations. -/
theorem canonicalFixedOldClass_eq_generatorChoiceImage
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    O.canonicalComponentLexClass (O.componentGenerator B)
      (O.stageBaseClosureEnumeration r orders B) =
    (O.canonicalNextGeneratorChoices r orders B).image
      (O.stageClosureFromTop r orders B) := by
  classical
  ext f
  constructor
  · intro hf
    have hOld :=
      O.canonicalComponentLexClass_fixedLower
        (O.componentGenerator B)
        (O.stageBaseClosureEnumeration r orders B) f hf
    let choice := O.topOrderFromClosure B f
    have hSurj :=
      O.stageClosureFromTop_surjective_fixedLower r hr orders B f hOld
    apply Finset.mem_image.mpr
    refine ⟨choice, ?_, hSurj⟩
    apply (O.mem_canonicalNextGeneratorChoices r orders B choice).mpr
    simpa only [choice, hSurj] using hf
  · intro hf
    obtain ⟨choice, hChoice, hEq⟩ := Finset.mem_image.mp hf
    have hMember :=
      (O.mem_canonicalNextGeneratorChoices r orders B choice).mp hChoice
    exact hEq ▸ hMember

/-- The actual canonical choice fibre has cardinality exactly the
local stabilizer factor g_A(B), for *every legal ranking and every
context*, without requiring that the other component orders are
canonical. This is a finite count at the chosen generator of B. -/
theorem canonicalNextGeneratorChoices_card
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    (O.canonicalNextGeneratorChoices r orders B).card =
      O.componentLocalFactor B := by
  classical
  have hImage := O.canonicalFixedOldClass_eq_generatorChoiceImage
    r hr orders B
  have hCardImage :
      ((O.canonicalNextGeneratorChoices r orders B).image
        (O.stageClosureFromTop r orders B)).card =
      (O.canonicalNextGeneratorChoices r orders B).card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact O.stageClosureFromTop_injective r orders B hab
  calc
    (O.canonicalNextGeneratorChoices r orders B).card =
      ((O.canonicalNextGeneratorChoices r orders B).image
        (O.stageClosureFromTop r orders B)).card := hCardImage.symm
    _ = (O.canonicalComponentLexClass (O.componentGenerator B)
          (O.stageBaseClosureEnumeration r orders B)).card :=
      congrArg Finset.card hImage.symm
    _ = O.actualLocalFactor (O.componentGenerator B) :=
      O.canonicalComponentLexClass_card
        (O.componentGenerator B)
        (O.stageBaseClosureEnumeration r orders B)
    _ = O.componentLocalFactor B :=
      O.componentLocalFactor_eq_of_generator B
        (O.componentGenerator_spec B)

end FiniteOrientation
end BigHrushovski
