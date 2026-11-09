import BigHrushovski.N0GlobalLexOrder
import Mathlib.Tactic

/-!
# Reconstructing a finite component-interval order from comparisons

The lexicographic order built from a ranking of the actual strongly
connected components and local vertex ranks has two independent
comparison regimes:
* between distinct SCCs, only their component ranks matter;
* within one SCC, only the relative local vertex ranks matter.

Conversely these two types of comparisons determine the entire strict
linear order. This is a uniqueness/reconstruction lemma about genuine
relations on the fixed labelled vertex set, not a count of synthetic
rank tuples. It is a precursor to the bijection with permitted orders.

The local canonical adjacency-code restriction and the infinite
Ramsey argument are not supplied here.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Explicit lexicographic comparison of the two coordinates. -/
theorem globalLexBefore_iff_key_comparison
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (x y : V) :
    O.GlobalLexBefore r localRank x y ↔
      (O.vertexLexKey r localRank x).1 <
        (O.vertexLexKey r localRank y).1 ∨
      ((O.vertexLexKey r localRank x).1 =
        (O.vertexLexKey r localRank y).1 ∧
        localRank x < localRank y) := by
  exact Prod.Lex.toLex_lt_toLex

/-- For distinct SCCs, the local ranks have no effect whatsoever. -/
theorem globalLexBefore_distinctComponents_iff
    (r : O.ComponentRanking) (localRank : V → ℕ)
    {x y : V} (hDistinct : O.component x ≠ O.component y) :
    O.GlobalLexBefore r localRank x y ↔
      (O.vertexLexKey r localRank x).1 <
        (O.vertexLexKey r localRank y).1 := by
  have hKeyNe : (O.vertexLexKey r localRank x).1 ≠
      (O.vertexLexKey r localRank y).1 := by
    intro hEq
    have hr : r ⟨O.component x, O.component_mem_components x⟩ =
        r ⟨O.component y, O.component_mem_components y⟩ :=
      Fin.ext hEq
    have hObject : (⟨O.component x, O.component_mem_components x⟩ :
          O.ComponentObject) =
        ⟨O.component y, O.component_mem_components y⟩ :=
      r.injective hr
    exact hDistinct (congrArg Subtype.val hObject)
  constructor
  · intro h
    rcases (O.globalLexBefore_iff_key_comparison r localRank x y).mp h with
      hFirst | ⟨hEqual, _⟩
    · exact hFirst
    · exact (hKeyNe hEqual).elim
  · intro h
    exact (O.globalLexBefore_iff_key_comparison r localRank x y).mpr
      (Or.inl h)

/-- Within a strongly connected component, only local ranks
determine the strict order; global component ranks disappear. -/
theorem globalLexBefore_sameComponent_iff
    (r : O.ComponentRanking) (localRank : V → ℕ)
    {x y : V} (hConnected : O.StronglyConnected x y) :
    O.GlobalLexBefore r localRank x y ↔
      localRank x < localRank y := by
  have hComponent : O.component x = O.component y :=
    O.component_eq_of_stronglyConnected hConnected
  have hKey : (O.vertexLexKey r localRank x).1 =
      (O.vertexLexKey r localRank y).1 := by
    simp only [vertexLexKey, hComponent]
  constructor
  · intro h
    rcases (O.globalLexBefore_iff_key_comparison r localRank x y).mp h with
      hFirst | ⟨_, hSecond⟩
    · have hNot : ¬ (O.vertexLexKey r localRank x).1 <
        (O.vertexLexKey r localRank y).1 := by
        rw [hKey]
        exact lt_irrefl _
      exact (hNot hFirst).elim
    · exact hSecond
  · intro h
    exact (O.globalLexBefore_iff_key_comparison r localRank x y).mpr
      (Or.inr ⟨hKey, h⟩)

/-- Equality of two complete labelled lexicographic order relations
is exactly agreement on component comparisons and on internal SCC
comparisons. The result does not identify different numerical rank
representations which happen to induce the same internal order. -/
theorem globalLexBefore_agree_iff_component_and_local
    (r s : O.ComponentRanking) (a b : V → ℕ) :
    (∀ x y : V,
      O.GlobalLexBefore r a x y ↔
        O.GlobalLexBefore s b x y) ↔
      (∀ x y : V,
        O.component x ≠ O.component y →
        ((O.vertexLexKey r a x).1 <
            (O.vertexLexKey r a y).1 ↔
          (O.vertexLexKey s b x).1 <
            (O.vertexLexKey s b y).1)) ∧
      (∀ x y : V,
        O.StronglyConnected x y →
        (a x < a y ↔ b x < b y)) := by
  constructor
  · intro h
    constructor
    · intro x y hDistinct
      calc
        (O.vertexLexKey r a x).1 <
            (O.vertexLexKey r a y).1 ↔
            O.GlobalLexBefore r a x y :=
          (O.globalLexBefore_distinctComponents_iff r a hDistinct).symm
        _ ↔ O.GlobalLexBefore s b x y := h x y
        _ ↔ (O.vertexLexKey s b x).1 <
            (O.vertexLexKey s b y).1 :=
          O.globalLexBefore_distinctComponents_iff s b hDistinct
    · intro x y hConnected
      calc
        a x < a y ↔ O.GlobalLexBefore r a x y :=
          (O.globalLexBefore_sameComponent_iff r a hConnected).symm
        _ ↔ O.GlobalLexBefore s b x y := h x y
        _ ↔ b x < b y :=
          O.globalLexBefore_sameComponent_iff s b hConnected
  · rintro ⟨hComponent, hLocal⟩ x y
    by_cases hConnected : O.StronglyConnected x y
    · calc
        O.GlobalLexBefore r a x y ↔ a x < a y :=
          O.globalLexBefore_sameComponent_iff r a hConnected
        _ ↔ b x < b y := hLocal x y hConnected
        _ ↔ O.GlobalLexBefore s b x y :=
          (O.globalLexBefore_sameComponent_iff s b hConnected).symm
    · have hDistinct : O.component x ≠ O.component y := by
        intro hEq
        exact hConnected
          ((O.stronglyConnected_iff_component_eq x y).mpr hEq)
      calc
        O.GlobalLexBefore r a x y ↔
          (O.vertexLexKey r a x).1 <
            (O.vertexLexKey r a y).1 :=
          O.globalLexBefore_distinctComponents_iff r a hDistinct
        _ ↔ (O.vertexLexKey s b x).1 <
          (O.vertexLexKey s b y).1 := hComponent x y hDistinct
        _ ↔ O.GlobalLexBefore s b x y :=
          (O.globalLexBefore_distinctComponents_iff s b hDistinct).symm

end FiniteOrientation
end BigHrushovski
