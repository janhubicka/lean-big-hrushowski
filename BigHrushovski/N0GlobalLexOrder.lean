import BigHrushovski.N0ComponentLinearExtensions
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic

/-!
# A finite successor-first component-interval order

Given a legal linear extension of the actual SCC dependency order,
and injective local numerical ranks within every component, arrange
vertices lexicographically by (component rank, local rank).

This produces a strict linear order on the fixed labelled vertex
set. Proper successors occur before their sources, and each SCC
is an interval. There is no need to choose an enumeration of
components before defining the construction.

This does not impose the canonical local adjacency-code rule.
The further step identifying canonical local choices with the
permitted ordered expansions remains separate.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The local rank distinguishes vertices of the same SCC.
Different components may reuse the same local numbers. -/
def LocallyInjective (local : V → ℕ) : Prop :=
  ∀ x y : V, O.StronglyConnected x y →
    local x = local y → x = y

/-- Every finite labelled set admits locally injective ranks;
the stronger global injectivity is not necessary later. -/
theorem exists_locallyInjective :
    ∃ local : V → ℕ, O.LocallyInjective local := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  refine ⟨fun x => (e x).val, ?_⟩
  intro x y hsc h
  exact e.injective (Fin.ext h)

/-- A vertex's component rank and its local rank. -/
noncomputable def vertexLexKey
    (r : O.ComponentRanking) (local : V → ℕ) (x : V) : ℕ × ℕ :=
  ((r ⟨O.component x, O.component_mem_components x⟩).val, local x)

theorem vertexLexKey_injective
    (r : O.ComponentRanking) (local : V → ℕ)
    (hloc : O.LocallyInjective local) :
    Function.Injective (O.vertexLexKey r local) := by
  intro x y h
  have hFirst : (O.vertexLexKey r local x).1 =
      (O.vertexLexKey r local y).1 :=
    congrArg Prod.fst h
  have hSecond : local x = local y := by
    exact congrArg Prod.snd h
  have hr : r ⟨O.component x, O.component_mem_components x⟩ =
      r ⟨O.component y, O.component_mem_components y⟩ := by
    exact Fin.ext hFirst
  have hObj : (⟨O.component x, O.component_mem_components x⟩ :
        O.ComponentObject) =
      ⟨O.component y, O.component_mem_components y⟩ :=
    r.injective hr
  have hComp : O.component x = O.component y :=
    congrArg Subtype.val hObj
  exact hloc x y
    ((O.stronglyConnected_iff_component_eq x y).mpr hComp) hSecond

/-- Lexicographic strict order on the actual labelled vertex
set, with component rank as its first coordinate. -/
noncomputable def GlobalLexBefore
    (r : O.ComponentRanking) (local : V → ℕ)
    (x y : V) : Prop :=
  (toLex (O.vertexLexKey r local x) : ℕ ×ₗ ℕ) <
    (toLex (O.vertexLexKey r local y) : ℕ ×ₗ ℕ)

theorem globalLexBefore_irrefl
    (r : O.ComponentRanking) (local : V → ℕ) (x : V) :
    ¬ O.GlobalLexBefore r local x x :=
  lt_irrefl _

theorem globalLexBefore_trans
    (r : O.ComponentRanking) (local : V → ℕ)
    {x y z : V}
    (hxy : O.GlobalLexBefore r local x y)
    (hyz : O.GlobalLexBefore r local y z) :
    O.GlobalLexBefore r local x z :=
  lt_trans hxy hyz

theorem globalLexBefore_total
    (r : O.ComponentRanking) (local : V → ℕ)
    (hloc : O.LocallyInjective local)
    {x y : V} (hxy : x ≠ y) :
    O.GlobalLexBefore r local x y ∨
      O.GlobalLexBefore r local y x := by
  have hKey : O.vertexLexKey r local x ≠
      O.vertexLexKey r local y := by
    intro h
    exact hxy (O.vertexLexKey_injective r local hloc h)
  have hLex : (toLex (O.vertexLexKey r local x) : ℕ ×ₗ ℕ) ≠
      (toLex (O.vertexLexKey r local y) : ℕ ×ₗ ℕ) := by
    intro h
    exact hKey (congrArg ofLex h)
  exact lt_or_gt_of_ne hLex

/-- Every earlier SCC rank puts all its vertices before the
vertices of the later SCC, regardless of their internal ranks. -/
theorem globalLexBefore_of_componentRank_lt
    (r : O.ComponentRanking) (local : V → ℕ)
    {x y : V}
    (hRank :
      r ⟨O.component x, O.component_mem_components x⟩ <
      r ⟨O.component y, O.component_mem_components y⟩) :
    O.GlobalLexBefore r local x y := by
  apply (Prod.Lex.toLex_lt_toLex).mpr
  exact Or.inl hRank

/-- A legal component ranking automatically gives the
successor-first condition on vertices. -/
theorem globalLexBefore_successor_first
    (r : O.ComponentRanking) (local : V → ℕ)
    (hr : O.IsLinearComponentRanking r)
    {x y : V} (hxy : O.StrictSuccessor x y) :
    O.GlobalLexBefore r local y x := by
  apply O.globalLexBefore_of_componentRank_lt r local
  exact hr
    ⟨O.component y, O.component_mem_components y⟩
    ⟨O.component x, O.component_mem_components x⟩
    ((O.componentPrecedes_iff_strictSuccessor x y).mpr hxy)

/-- The lexicographic construction cannot interleave SCCs:
if x and z are strongly connected and x < y < z, then y
belongs to their same strongly connected component. -/
theorem globalLexBefore_component_interval
    (r : O.ComponentRanking) (local : V → ℕ)
    {x y z : V}
    (hxz : O.StronglyConnected x z)
    (hxy : O.GlobalLexBefore r local x y)
    (hyz : O.GlobalLexBefore r local y z) :
    O.StronglyConnected x y := by
  have hXY : (O.vertexLexKey r local x).1 ≤
      (O.vertexLexKey r local y).1 :=
    Prod.Lex.monotone_fst _ _ hxy.le
  have hYZ : (O.vertexLexKey r local y).1 ≤
      (O.vertexLexKey r local z).1 :=
    Prod.Lex.monotone_fst _ _ hyz.le
  have hXZ : (O.vertexLexKey r local x).1 =
      (O.vertexLexKey r local z).1 := by
    have hcomp := O.component_eq_of_stronglyConnected hxz
    simp only [vertexLexKey, hcomp]
  have hXYeq : (O.vertexLexKey r local x).1 =
      (O.vertexLexKey r local y).1 := by omega
  have hr : r ⟨O.component x, O.component_mem_components x⟩ =
      r ⟨O.component y, O.component_mem_components y⟩ :=
    Fin.ext hXYeq
  have hObj : (⟨O.component x, O.component_mem_components x⟩ :
        O.ComponentObject) =
      ⟨O.component y, O.component_mem_components y⟩ :=
    r.injective hr
  have hComp : O.component x = O.component y :=
    congrArg Subtype.val hObj
  exact (O.stronglyConnected_iff_component_eq x y).mpr hComp

end FiniteOrientation
end BigHrushovski
