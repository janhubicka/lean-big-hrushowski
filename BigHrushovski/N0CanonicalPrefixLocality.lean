import BigHrushovski.N0AssemblyDataInverse
import Mathlib.Tactic

/-!
# Prefix locality of canonical finite SCC orders

Fix a legal consecutive ranking of the actual strongly connected
components. Every proper successor component of B has smaller rank,
so the complete successor closure C_B lies in the component prefix
through B.

It follows that the canonical complete-code condition for B depends
only on the component orders already chosen through that rank.
Component orders that occur later cannot affect an earlier canonical
condition. This is the exact locality needed to interpret finite
canonical assignments as reachable successive histories.

These lemmas do not yet assert uniform counts for next-component
choices or the global finite product formula.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Every component in the complete successor closure of x
has rank at most the rank of x's own SCC. The legal-ranking
hypothesis is essential. -/
theorem componentClosure_rank_le
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (x y : V)
    (hy : y ∈ O.componentClosure x) :
    r ⟨O.component y, O.component_mem_components y⟩ ≤
      r ⟨O.component x, O.component_mem_components x⟩ := by
  by_cases hsc : O.StronglyConnected x y
  · have hComp : O.component y = O.component x :=
      (O.component_eq_of_stronglyConnected hsc).symm
    have hObj :
        (⟨O.component y, O.component_mem_components y⟩ :
          O.ComponentObject) =
        ⟨O.component x, O.component_mem_components x⟩ :=
      Subtype.ext hComp
    rw [hObj]
  · have hyNotTop : y ∉ O.component x := by
      intro hyTop
      exact hsc ((O.mem_component_iff x y).mp hyTop)
    have hyLower : y ∈ O.lowerPart x :=
      Finset.mem_sdiff.mpr ⟨hy, hyNotTop⟩
    have hStrict : O.StrictSuccessor x y :=
      (O.strictSuccessor_iff_mem_lowerPart x y).mpr hyLower
    have hPre : O.ComponentPrecedes
        (O.component y) (O.component x) :=
      (O.componentPrecedes_iff_strictSuccessor x y).mpr hStrict
    exact (hr ⟨O.component y, O.component_mem_components y⟩
      ⟨O.component x, O.component_mem_components x⟩ hPre).le

/-- The two local component-order assignments coincide on
the SCC prefix up to the rank of B (inclusive). -/
def AgreeThroughComponentRank
    (r : O.ComponentRanking)
    (orders₁ orders₂ : O.ComponentLocalEnumerations)
    (k : Fin (Fintype.card O.ComponentObject)) : Prop :=
  ∀ B : O.ComponentObject, r B ≤ k → orders₁ B = orders₂ B

/-- A complete successor-closure enumeration cannot see
component-order changes made *after* the rank of its top SCC. -/
theorem inheritedComponentEnumeration_eq_of_rankPrefixAgreement
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders₁ orders₂ : O.ComponentLocalEnumerations)
    (x : V)
    (hAgree : O.AgreeThroughComponentRank r orders₁ orders₂
      (r ⟨O.component x, O.component_mem_components x⟩)) :
    O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders₁) x =
      O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders₂) x := by
  apply O.inheritedComponentEnumeration_eq_of_component_agreement
    r orders₁ orders₂ x
  intro B hSubset
  obtain ⟨z, hz⟩ := O.componentObject_nonempty B
  have hzClosure : z ∈ O.componentClosure x := hSubset hz
  have hRank := O.componentClosure_rank_le r hr x z hzClosure
  have hObj :
      (⟨O.component z, O.component_mem_components z⟩ :
        O.ComponentObject) = B :=
    Subtype.ext (O.component_eq_of_mem_componentObject B hz)
  rw [hObj] at hRank
  exact hAgree B hRank

/-- The canonical-code condition at x is unchanged when only
later components' internal orders are altered. The top SCC itself
must remain fixed here; its canonical choices are precisely what
the next stage of the counting argument varies. -/
theorem canonicalCondition_eq_of_rankPrefixAgreement
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders₁ orders₂ : O.ComponentLocalEnumerations)
    (x : V)
    (hAgree : O.AgreeThroughComponentRank r orders₁ orders₂
      (r ⟨O.component x, O.component_mem_components x⟩)) :
    (let e := O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders₁) x
      e ∈ O.canonicalComponentLexClass x e) ↔
    (let e := O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders₂) x
      e ∈ O.canonicalComponentLexClass x e) := by
  have hEq := O.inheritedComponentEnumeration_eq_of_rankPrefixAgreement
    r hr orders₁ orders₂ x hAgree
  change
    (O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r orders₁) x ∈
      O.canonicalComponentLexClass x
        (O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r orders₁) x)) ↔
    (O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r orders₂) x ∈
      O.canonicalComponentLexClass x
        (O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r orders₂) x))
  rw [hEq]

/-- All canonical tests for components of rank at most k. This
definition only evaluates the actual inherited complete closures. -/
def IsCanonicalThroughRank
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (k : Fin (Fintype.card O.ComponentObject)) : Prop :=
  ∀ x : V,
    r ⟨O.component x, O.component_mem_components x⟩ ≤ k →
      (let e := O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders) x
       e ∈ O.canonicalComponentLexClass x e)

/-- Canonicality of a prefix depends only on component orders
chosen within that prefix, even though the whole assignment is
needed to construct the ambient lexicographic enumeration. -/
theorem canonicalThroughRank_iff_of_prefixAgreement
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders₁ orders₂ : O.ComponentLocalEnumerations)
    (k : Fin (Fintype.card O.ComponentObject))
    (hAgree : O.AgreeThroughComponentRank r orders₁ orders₂ k) :
    O.IsCanonicalThroughRank r orders₁ k ↔
      O.IsCanonicalThroughRank r orders₂ k := by
  constructor
  · intro h x hx
    have hHere : O.AgreeThroughComponentRank r orders₁ orders₂
        (r ⟨O.component x, O.component_mem_components x⟩) := by
      intro B hB
      exact hAgree B (le_trans hB hx)
    exact (O.canonicalCondition_eq_of_rankPrefixAgreement
      r hr orders₁ orders₂ x hHere).mp (h x hx)
  · intro h x hx
    have hHere : O.AgreeThroughComponentRank r orders₁ orders₂
        (r ⟨O.component x, O.component_mem_components x⟩) := by
      intro B hB
      exact hAgree B (le_trans hB hx)
    exact (O.canonicalCondition_eq_of_rankPrefixAgreement
      r hr orders₁ orders₂ x hHere).mpr (h x hx)

end FiniteOrientation
end BigHrushovski
