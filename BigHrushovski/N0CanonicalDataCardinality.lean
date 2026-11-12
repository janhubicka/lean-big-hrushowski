import BigHrushovski.N0AssemblyDataInverse
import BigHrushovski.N0CanonicalTopOrderFibres
import Mathlib.Tactic

/-!
# Canonical finite SCC data and actual labelled global order counts

For a finite orientation O, a labelled canonical order is equivalent
to a legal ranking of its actual strongly connected components,
together with an enumeration of every component satisfying the
complete local adjacency-code conditions.

The preceding finite construction and its inverse give an exact
bijection, not merely a correspondence modulo isomorphism. Here we
express that fact as equality of finite cardinalities and isolate
the remaining uniform local-fibre counting obligation.

The conditional counting theorem does NOT assert that the uniform
fibre hypothesis has yet been verified. In particular this module
is not a proof of the exact big Ramsey degree.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Actual finite canonical data: a legal order of the SCCs and
one component enumeration for each SCC, satisfying the complete
local code conditions of the global assembly. -/
noncomputable def canonicalComponentOrderData :
    Finset (O.ComponentRanking × O.ComponentLocalEnumerations) := by
  classical
  exact Finset.univ.filter
    (fun d => O.IsLinearComponentRanking d.1 ∧
      O.IsCanonicalComponentAssignment d.1 d.2)

theorem mem_canonicalComponentOrderData
    (d : O.ComponentRanking × O.ComponentLocalEnumerations) :
    d ∈ O.canonicalComponentOrderData ↔
      O.IsLinearComponentRanking d.1 ∧
        O.IsCanonicalComponentAssignment d.1 d.2 := by
  classical
  simp [canonicalComponentOrderData]

/-- The set of genuine globally canonical labelled enumerations
is literally the image of the legal canonical component data
under the already-constructed finite SCC concatenation. -/
theorem finiteCanonicalEnumerations_eq_image_of_data :
    (O.finiteCanonicalComponentEnumerations
      (n := Fintype.card V)) =
    (O.canonicalComponentOrderData).image
      (fun d => O.assembleComponentEnumerations d.1 d.2) := by
  classical
  ext e
  rw [O.mem_finiteCanonicalComponentEnumerations e]
  constructor
  · intro he
    obtain ⟨r, hr, orders, hCanon, hEq⟩ :=
      O.canonicalEnumeration_has_componentAssembly e he
    apply Finset.mem_image.mpr
    refine ⟨(r, orders), ?_, hEq⟩
    exact (O.mem_canonicalComponentOrderData (r, orders)).mpr
      ⟨hr, hCanon⟩
  · intro hImage
    obtain ⟨⟨r, orders⟩, hData, hEq⟩ :=
      Finset.mem_image.mp hImage
    obtain ⟨hr, hCanon⟩ :=
      (O.mem_canonicalComponentOrderData (r, orders)).mp hData
    rw [← hEq]
    exact O.legalCanonicalAssignment_gives_global r orders hr hCanon

/-- The global canonical enumerations and the admissible SCC-order
data have exactly the same cardinality. No automorphism quotient
is taken in either set. -/
theorem finiteCanonicalEnumerations_card_eq_data :
    (O.finiteCanonicalComponentEnumerations
      (n := Fintype.card V)).card =
      (O.canonicalComponentOrderData).card := by
  classical
  rw [O.finiteCanonicalEnumerations_eq_image_of_data]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hEq
  exact O.assembleComponentEnumerations_injective hEq

/-- Therefore the number of genuine labelled strict linear order
relations in the finite canonical family equals the number
of canonical SCC-order data. -/
theorem finiteCanonicalOrderRelations_card_eq_data :
    ((O.finiteCanonicalComponentEnumerations
      (n := Fintype.card V)).image OrderBefore).card =
      (O.canonicalComponentOrderData).card := by
  rw [O.finiteCanonicalGlobalOrderRelations_card,
      O.finiteCanonicalEnumerations_card_eq_data]

/-- Canonically admissible component enumerations for one
specific legal SCC ranking. Their sets may differ with the ranking,
even if their total cardinalities eventually agree. -/
noncomputable def canonicalAssignmentsAtRanking
    (r : O.ComponentRanking) :
    Finset O.ComponentLocalEnumerations := by
  classical
  exact Finset.univ.filter (O.IsCanonicalComponentAssignment r)

theorem mem_canonicalAssignmentsAtRanking
    (r : O.ComponentRanking) (orders : O.ComponentLocalEnumerations) :
    orders ∈ O.canonicalAssignmentsAtRanking r ↔
      O.IsCanonicalComponentAssignment r orders := by
  classical
  simp [canonicalAssignmentsAtRanking]

end FiniteOrientation
end BigHrushovski
