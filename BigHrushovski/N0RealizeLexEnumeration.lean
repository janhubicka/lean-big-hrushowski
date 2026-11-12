import BigHrushovski.N0InducedClosureOrders
import BigHrushovski.N0GlobalOrderSurjectivity
import Mathlib.Tactic

/-!
# Realizing finite component lexicographic orders by actual enumerations

The earlier construction defines a strict comparison relation on the
labelled vertices using a legal SCC ranking and locally injective
numerical ranks. Here that relation is realized as an actual bijective
enumeration of V by the consecutive ordinal Fin (card V).

This closes the gap between the abstract strict relation and actual
finite ordered structures. Every such enumeration consists of whole
SCC intervals and, for legal component rankings, is successor-first.

Conversely every component-interval enumeration produces the *same*
labelled strict order as one of these explicit realizations.

No adjacency-code restriction is imposed on the local numerical
ranks; in particular this is not yet the canonical-order product
count or any infinite Ramsey statement.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Enumerate V in the actual lexicographic order determined by
component ranks and locally injective vertex ranks. The resulting
enumeration has the correct consecutive finite ordinal carrier. -/
noncomputable def lexComponentEnumeration
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hloc : O.LocallyInjective localRank) :
    Fin (Fintype.card V) ≃ V := by
  classical
  letI : LinearOrder V :=
    LinearOrder.lift'
      (fun v : V =>
        (toLex (O.vertexLexKey r localRank v) : ℕ ×ₗ ℕ))
      (by
        intro x y h
        exact O.vertexLexKey_injective r localRank hloc
          (congrArg ofLex h))
  exact (Fintype.orderIsoFinOfCardEq V rfl).toEquiv

/-- The actual induced labelled order of this enumeration is
exactly the previously constructed global lexicographic relation. -/
theorem lexComponentEnumeration_order_iff
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hloc : O.LocallyInjective localRank)
    (x y : V) :
    OrderBefore (O.lexComponentEnumeration r localRank hloc) x y ↔
      O.GlobalLexBefore r localRank x y := by
  classical
  letI : LinearOrder V :=
    LinearOrder.lift'
      (fun v : V =>
        (toLex (O.vertexLexKey r localRank v) : ℕ ×ₗ ℕ))
      (by
        intro u v h
        exact O.vertexLexKey_injective r localRank hloc
          (congrArg ofLex h))
  let E : Fin (Fintype.card V) ≃o V :=
    Fintype.orderIsoFinOfCardEq V rfl
  change E.symm x < E.symm y ↔
    O.GlobalLexBefore r localRank x y
  change E.symm x < E.symm y ↔ x < y
  constructor
  · intro h
    simpa using E.strictMono h
  · intro h
    exact E.symm.strictMono h

/-- The realized enumeration has each actual strongly connected
component as an interval, irrespective of whether the given
component ranking respects the dependency order. -/
theorem lexComponentEnumeration_isComponentInterval
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hloc : O.LocallyInjective localRank) :
    O.IsComponentIntervalEnumeration
      (O.lexComponentEnumeration r localRank hloc) := by
  intro B x y z hx hz hxy hyz
  have hcx : O.component x = B.val :=
    O.component_eq_of_mem_componentObject B hx
  have hcz : O.component z = B.val :=
    O.component_eq_of_mem_componentObject B hz
  have hxz : O.StronglyConnected x z :=
    (O.stronglyConnected_iff_component_eq x z).mpr
      (hcx.trans hcz.symm)
  have hxylex : O.GlobalLexBefore r localRank x y :=
    (O.lexComponentEnumeration_order_iff r localRank hloc x y).mp hxy
  have hyzlex : O.GlobalLexBefore r localRank y z :=
    (O.lexComponentEnumeration_order_iff r localRank hloc y z).mp hyz
  have hxyconnected : O.StronglyConnected x y :=
    O.globalLexBefore_component_interval r localRank hxz hxylex hyzlex
  have hcy : O.component y = B.val :=
    (O.component_eq_of_stronglyConnected hxyconnected).symm.trans hcx
  simpa [hcy] using (O.self_mem_component y)

/-- Legal component rankings give successor-first actual
enumerations, not merely abstract successor-first relations. -/
theorem lexComponentEnumeration_isSuccessorFirst
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hloc : O.LocallyInjective localRank)
    (hr : O.IsLinearComponentRanking r) :
    O.IsSuccessorFirstEnumeration
      (O.lexComponentEnumeration r localRank hloc) := by
  intro x y hxy
  change OrderBefore (O.lexComponentEnumeration r localRank hloc) y x
  apply (O.lexComponentEnumeration_order_iff r localRank hloc y x).mpr
  exact O.globalLexBefore_successor_first r localRank hr hxy

/-- The constructed enumeration is an actual element of the
already-defined finite family of successor-first interval
enumerations whenever its component ranking is legal. -/
theorem lexComponentEnumeration_mem_successorFirstIntervals
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hloc : O.LocallyInjective localRank)
    (hr : O.IsLinearComponentRanking r) :
    O.lexComponentEnumeration r localRank hloc ∈
      (O.successorFirstIntervalEnumerations
        (n := Fintype.card V)) := by
  apply (O.mem_successorFirstIntervalEnumerations
    (O.lexComponentEnumeration r localRank hloc)).mpr
  exact ⟨O.lexComponentEnumeration_isComponentInterval r localRank hloc,
    O.lexComponentEnumeration_isSuccessorFirst r localRank hloc hr⟩

/-- The realized enumeration and its inherited order on any
actual finite subset S agree with the lex relation there. -/
theorem lexComponentEnumeration_induced_order_iff
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hloc : O.LocallyInjective localRank)
    (S : Finset V) (u v : ↥S) :
    OrderBefore
      (inducedEnumerationOn
        (O.lexComponentEnumeration r localRank hloc) S) u v ↔
      O.GlobalLexBefore r localRank u.val v.val := by
  exact (inducedEnumerationOn_order_iff
      (O.lexComponentEnumeration r localRank hloc) S u v).trans
    (O.lexComponentEnumeration_order_iff
      r localRank hloc u.val v.val)

/-- Every genuine SCC-interval order on the labelled set V is
literally realized, as an order relation, by the lexicographic
construction for its recovered SCC ranking and finite vertex
position function. The source enumeration may have a different
but necessarily equinumerous finite ordinal index type. -/
theorem lexComponentEnumeration_reconstructs_order
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsComponentIntervalEnumeration e) (x y : V) :
    OrderBefore
      (O.lexComponentEnumeration (O.rankingFromEnumeration e)
        (fun v : V => (e.symm v).val)
        (O.enumerationPosition_locallyInjective e)) x y ↔
      OrderBefore e x y := by
  calc
    OrderBefore
        (O.lexComponentEnumeration (O.rankingFromEnumeration e)
          (fun v : V => (e.symm v).val)
          (O.enumerationPosition_locallyInjective e)) x y ↔
      O.GlobalLexBefore (O.rankingFromEnumeration e)
        (fun v : V => (e.symm v).val) x y :=
      O.lexComponentEnumeration_order_iff _ _
        (O.enumerationPosition_locallyInjective e) x y
    _ ↔ OrderBefore e x y :=
      O.globalLexBefore_reconstructs_enumeration e he x y

/-- The constructed enumeration also recovers any genuine
successor-first SCC-interval order, and its ranking is legal. -/
theorem exists_lexComponentEnumeration_for_successorFirst
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsComponentIntervalEnumeration e)
    (hs : O.IsSuccessorFirstEnumeration e) :
    ∃ r : O.ComponentRanking,
      O.IsLinearComponentRanking r ∧
      ∃ localRank : V → ℕ,
        ∃ hloc : O.LocallyInjective localRank,
          ∀ x y : V,
            OrderBefore
                (O.lexComponentEnumeration r localRank hloc) x y ↔
              OrderBefore e x y := by
  refine ⟨O.rankingFromEnumeration e,
    O.rankingFromEnumeration_isLegal e hs,
    (fun v : V => (e.symm v).val),
    O.enumerationPosition_locallyInjective e, ?_⟩
  intro x y
  exact O.lexComponentEnumeration_reconstructs_order e he x y

end FiniteOrientation
end BigHrushovski
