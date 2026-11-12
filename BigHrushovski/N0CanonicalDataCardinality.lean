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

/-- The canonical data set is the disjoint union of the admissible
component-enumeration fibres over the legal SCC rankings. -/
theorem canonicalComponentOrderData_eq_rank_union :
    O.canonicalComponentOrderData =
      O.linearComponentRankings.biUnion
        (fun r => (O.canonicalAssignmentsAtRanking r).image
          (fun orders => (r, orders))) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨hr, hCanon⟩ :=
      (O.mem_canonicalComponentOrderData d).mp hd
    apply Finset.mem_biUnion.mpr
    refine ⟨d.1, (O.mem_linearComponentRankings d.1).mpr hr, ?_⟩
    exact Finset.mem_image.mpr
      ⟨d.2, (O.mem_canonicalAssignmentsAtRanking d.1 d.2).mpr hCanon,
        by cases d; rfl⟩
  · intro hd
    obtain ⟨r, hr, hImage⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨orders, hOrders, hEq⟩ := Finset.mem_image.mp hImage
    have hR : O.IsLinearComponentRanking r :=
      (O.mem_linearComponentRankings r).mp hr
    have hC : O.IsCanonicalComponentAssignment r orders :=
      (O.mem_canonicalAssignmentsAtRanking r orders).mp hOrders
    subst d
    exact (O.mem_canonicalComponentOrderData (r, orders)).mpr
      ⟨hR, hC⟩

/-- The number of canonical data records is the sum of the
cardinalities of their fibres over actual legal SCC rankings. -/
theorem canonicalComponentOrderData_card_eq_rank_sum :
    (O.canonicalComponentOrderData).card =
      ∑ r ∈ O.linearComponentRankings,
        (O.canonicalAssignmentsAtRanking r).card := by
  classical
  rw [O.canonicalComponentOrderData_eq_rank_union]
  have hDisjoint :
      (((O.linearComponentRankings : Finset O.ComponentRanking) :
        Set O.ComponentRanking)).PairwiseDisjoint
        (fun r => (O.canonicalAssignmentsAtRanking r).image
          (fun orders => (r, orders))) := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro d hd he
    obtain ⟨ordersR, hOrdersR, hEqR⟩ := Finset.mem_image.mp hd
    obtain ⟨ordersS, hOrdersS, hEqS⟩ := Finset.mem_image.mp he
    have hEq : r = s := by
      have hPair := congrArg Prod.fst (hEqR.trans hEqS.symm)
      simpa using hPair
    exact hrs hEq
  calc
    (O.linearComponentRankings.biUnion
      (fun r => (O.canonicalAssignmentsAtRanking r).image
        (fun orders => (r, orders)))).card =
      ∑ r ∈ O.linearComponentRankings,
        ((O.canonicalAssignmentsAtRanking r).image
          (fun orders => (r, orders))).card :=
      Finset.card_biUnion hDisjoint
    _ = ∑ r ∈ O.linearComponentRankings,
        (O.canonicalAssignmentsAtRanking r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      exact congrArg Prod.snd hab

/-- The last finite counting obligation, explicitly isolated:
if for *each legal SCC ranking* the number of compatible
canonical component-order choices is the product of the actual
local stabilizer factors, then this same product times the
number of legal SCC rankings counts the **actual labelled
permitted vertex orders**.

This is deliberately conditional; the uniformity hypothesis
remains an open proof obligation, not an assumed manuscript fact. -/
theorem finiteCanonicalOrderCount_of_uniformRankingFibres
    (hUniform :
      ∀ r ∈ O.linearComponentRankings,
        (O.canonicalAssignmentsAtRanking r).card =
          ∏ B : O.ComponentObject, O.componentLocalFactor B) :
    ((O.finiteCanonicalComponentEnumerations
        (n := Fintype.card V)).image OrderBefore).card =
      O.finiteComponentTypeCount := by
  classical
  rw [O.finiteCanonicalOrderRelations_card_eq_data,
    O.canonicalComponentOrderData_card_eq_rank_sum]
  calc
    (∑ r ∈ O.linearComponentRankings,
      (O.canonicalAssignmentsAtRanking r).card) =
        ∑ r ∈ O.linearComponentRankings,
          ∏ B : O.ComponentObject, O.componentLocalFactor B := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hUniform r hr
    _ = O.componentLinearExtensionCount *
        ∏ B : O.ComponentObject, O.componentLocalFactor B := by
      simp [componentLinearExtensionCount]
    _ = O.finiteComponentTypeCount := rfl


end FiniteOrientation
end BigHrushovski
