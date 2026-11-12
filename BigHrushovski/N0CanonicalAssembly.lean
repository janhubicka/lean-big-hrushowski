import BigHrushovski.N0ComponentClosureLocality
import Mathlib.Tactic

/-!
# Canonical global enumerations and SCC-order assembly

The geometric SCC-order assembly of the preceding modules has an
exact version for the finite family of globally canonical
enumerations. It is useful to express the local canonical condition
directly on the data (an SCC ranking and an enumeration of each SCC).

For a legal component ranking, the assembled enumeration is
globally canonical if and only if all its inherited component-closure
orders attain their prescribed least complete directed adjacency code.
Conversely, every actual globally canonical component-interval
enumeration is reconstructed from its actual ranking and the
enumerations inherited by its SCCs.

This is the existence/surjectivity direction of the finite coding
argument. It does not yet count canonical histories, and is not an
infinite Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Canonicality stated directly on a ranking and choices of
internal orders on the *actual* strongly connected components. -/
def IsCanonicalComponentAssignment
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) : Prop :=
  ∀ x : V,
    let e := O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r orders) x
    e ∈ O.canonicalComponentLexClass x e

/-- For a legal ranking, the criterion on the component choices
is precisely the canonical-order condition on the resulting actual
labelled enumeration; the SCC intervals and successor-first
requirements follow from the assembly theorem. -/
theorem assembled_isFiniteCanonical_iff
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (hr : O.IsLinearComponentRanking r) :
    O.IsFiniteCanonicalComponentEnumeration
      (O.assembleComponentEnumerations r orders) ↔
      O.IsCanonicalComponentAssignment r orders := by
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨O.assembleComponentEnumerations_isComponentInterval r orders,
      O.assembleComponentEnumerations_isSuccessorFirst r orders hr,
      h⟩

/-- Every genuine globally canonical finite enumeration is obtained
by assembling its *actual* SCC ranking and the induced enumerations
of its SCCs. The result is equality of labelled enumerations, not
merely equality of their abstract order types. -/
theorem canonicalEnumeration_has_componentAssembly
    (e : Fin (Fintype.card V) ≃ V)
    (he : O.IsFiniteCanonicalComponentEnumeration e) :
    ∃ r : O.ComponentRanking,
      O.IsLinearComponentRanking r ∧
      ∃ orders : O.ComponentLocalEnumerations,
        O.IsCanonicalComponentAssignment r orders ∧
        O.assembleComponentEnumerations r orders = e := by
  let r : O.ComponentRanking := O.rankingFromEnumeration e
  let orders : O.ComponentLocalEnumerations :=
    O.componentOrdersFromEnumeration e
  have hEq : O.assembleComponentEnumerations r orders = e := by
    apply enumeration_eq_of_same_order
    intro x y
    exact O.assembleComponentEnumerations_reconstructs_order e he.1 x y
  refine ⟨r, O.rankingFromEnumeration_isLegal e he.2.1, orders, ?_, hEq⟩
  intro x
  change O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r orders) x ∈
    O.canonicalComponentLexClass x
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders) x)
  rw [hEq]
  exact he.2.2 x

/-- A family of canonical component choices in legal SCC order
always produces a genuine globally canonical labelled enumeration. -/
theorem legalCanonicalAssignment_gives_global
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (hr : O.IsLinearComponentRanking r)
    (hCanon : O.IsCanonicalComponentAssignment r orders) :
    O.IsFiniteCanonicalComponentEnumeration
      (O.assembleComponentEnumerations r orders) :=
  (O.assembled_isFiniteCanonical_iff r orders hr).mpr hCanon

end FiniteOrientation
end BigHrushovski
