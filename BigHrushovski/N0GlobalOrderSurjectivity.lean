import BigHrushovski.N0LowerInitialSegment
import BigHrushovski.N0ComponentFirstPositions
-- The parent orientation branch supplies the component-position module.
import Mathlib.Tactic

/-!
# Every genuine component-interval enumeration is a global lex order

The previous construction starts from a legal ranking of strongly
connected components and locally injective vertex ranks. Here we
prove the converse at the level of *actual labelled vertex orders*.

For an enumeration e with SCC intervals, rank its actual components
by their first appearance and give each vertex its numerical e-position
as local rank. The lexicographic order from these data reproduces
the precise original comparison x <_e y, not just an isomorphic
unlabelled order. When e is successor-first, the extracted component
ranking is legal.

This proves the surjectivity part of the finite global order
construction. It does *not* prove that locally permitted closure
orders are exactly any particular family of matrix-code minima,
nor the infinite N0 big Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Ranking components by first appearance not only extends the
dependency order under successor-first enumeration; it *reflects*
all comparisons between distinct components of the enumeration. -/
theorem rankingFromEnumeration_lt_iff_firstPosition {n : ℕ}
    (e : Fin n ≃ V) (B C : O.ComponentObject) :
    O.rankingFromEnumeration e B < O.rankingFromEnumeration e C ↔
      O.firstComponentPosition e B < O.firstComponentPosition e C := by
  classical
  letI : LinearOrder O.ComponentOrderCarrier :=
    O.componentOrderCarrierLinearOrder e
  have hcard : Fintype.card O.ComponentOrderCarrier =
      Fintype.card O.ComponentObject :=
    Fintype.card_congr O.componentOrderCarrierEquiv.symm
  let E : O.ComponentOrderCarrier ≃o
      Fin (Fintype.card O.ComponentObject) :=
    (Fintype.orderIsoFinOfCardEq O.ComponentOrderCarrier hcard).symm
  constructor
  · intro h
    change E ⟨B⟩ < E ⟨C⟩ at h
    have hCarrier := E.symm.strictMono h
    have hBC : (⟨B⟩ : O.ComponentOrderCarrier) <
        ⟨C⟩ := by simpa using hCarrier
    change O.firstComponentPosition e B <
      O.firstComponentPosition e C at hBC
    exact hBC
  · intro h
    have hCarrier : (⟨B⟩ : O.ComponentOrderCarrier) <
        ⟨C⟩ := h
    have hFin := E.strictMono hCarrier
    change E ⟨B⟩ < E ⟨C⟩
    exact hFin

/-- Actual enumeration positions are injective, hence locally
injective in every SCC. This does not assign arbitrary extra
labels to the outgoing neighbour sets. -/
theorem enumerationPosition_locallyInjective {n : ℕ}
    (e : Fin n ≃ V) :
    O.LocallyInjective (fun x : V => (e.symm x).val) := by
  intro x y _ h
  exact e.symm.injective (Fin.ext h)

/-- The concrete global lexicographic construction from the
first-occurrence component ranking and positions in e reproduces
the original labelled order of *every* component-interval enumeration.
No successor-first hypothesis is required for this reconstruction. -/
theorem globalLexBefore_reconstructs_enumeration {n : ℕ}
    (e : Fin n ≃ V)
    (hInterval : O.IsComponentIntervalEnumeration e)
    (x y : V) :
    O.GlobalLexBefore (O.rankingFromEnumeration e)
      (fun v : V => (e.symm v).val) x y ↔
      OrderBefore e x y := by
  by_cases hConnected : O.StronglyConnected x y
  · calc
      O.GlobalLexBefore (O.rankingFromEnumeration e)
          (fun v : V => (e.symm v).val) x y ↔
        (e.symm x).val < (e.symm y).val :=
        O.globalLexBefore_sameComponent_iff
          (O.rankingFromEnumeration e)
          (fun v : V => (e.symm v).val) hConnected
      _ ↔ OrderBefore e x y := by
        simp only [OrderBefore, Fin.lt_def]
  · let B : O.ComponentObject :=
        ⟨O.component x, O.component_mem_components x⟩
    let C : O.ComponentObject :=
        ⟨O.component y, O.component_mem_components y⟩
    have hDistinct : O.component x ≠ O.component y := by
      intro hEq
      exact hConnected
        ((O.stronglyConnected_iff_component_eq x y).mpr hEq)
    have hBC : B ≠ C := by
      intro h
      exact hDistinct (congrArg Subtype.val h)
    have hxB : x ∈ B.val := O.self_mem_component x
    have hyC : y ∈ C.val := O.self_mem_component y
    calc
      O.GlobalLexBefore (O.rankingFromEnumeration e)
          (fun v : V => (e.symm v).val) x y ↔
        (O.vertexLexKey (O.rankingFromEnumeration e)
          (fun v : V => (e.symm v).val) x).1 <
        (O.vertexLexKey (O.rankingFromEnumeration e)
          (fun v : V => (e.symm v).val) y).1 :=
        O.globalLexBefore_distinctComponents_iff
          (O.rankingFromEnumeration e)
          (fun v : V => (e.symm v).val) hDistinct
      _ ↔ O.firstComponentPosition e B <
          O.firstComponentPosition e C := by
        change ((O.rankingFromEnumeration e B).val <
          (O.rankingFromEnumeration e C).val) ↔ _
        simpa only [Fin.lt_def] using
          (O.rankingFromEnumeration_lt_iff_firstPosition e B C)
      _ ↔ OrderBefore e x y := by
        have h := O.vertices_before_iff_component_first_before
          e hInterval B C hBC hxB hyC
        simpa only [OrderBefore] using h.symm

/-- Therefore every actual labelled order with component intervals
lies in the image of the global lex construction. -/
theorem exists_globalLexRepresentation_of_componentIntervals {n : ℕ}
    (e : Fin n ≃ V)
    (hInterval : O.IsComponentIntervalEnumeration e) :
    ∃ r : O.ComponentRanking, ∃ localRank : V → ℕ,
      O.LocallyInjective localRank ∧
      ∀ x y : V,
        O.GlobalLexBefore r localRank x y ↔
          OrderBefore e x y := by
  refine ⟨O.rankingFromEnumeration e,
    (fun v : V => (e.symm v).val),
    O.enumerationPosition_locallyInjective e, ?_⟩
  intro x y
  exact O.globalLexBefore_reconstructs_enumeration e hInterval x y

/-- If the enumeration is also successor-first, the recovered
ranking is a legal linear extension of the intrinsic SCC order. -/
theorem exists_legal_globalLexRepresentation {n : ℕ}
    (e : Fin n ≃ V)
    (hInterval : O.IsComponentIntervalEnumeration e)
    (hSuccessor : O.IsSuccessorFirstEnumeration e) :
    ∃ r : O.ComponentRanking,
      O.IsLinearComponentRanking r ∧
      ∃ localRank : V → ℕ,
        O.LocallyInjective localRank ∧
        ∀ x y : V,
          O.GlobalLexBefore r localRank x y ↔
            OrderBefore e x y := by
  refine ⟨O.rankingFromEnumeration e,
    O.rankingFromEnumeration_isLegal e hSuccessor,
    (fun v : V => (e.symm v).val),
    O.enumerationPosition_locallyInjective e, ?_⟩
  intro x y
  exact O.globalLexBefore_reconstructs_enumeration e hInterval x y

end FiniteOrientation
end BigHrushovski
