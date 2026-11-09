import BigHrushovski.N0GlobalLexReconstruction
import BigHrushovski.N0ComponentLowerPart
import Mathlib.Tactic

/-!
# The proper successor part is an initial segment of its component closure

For a component B, put C_B = scl(B) and P_B = C_B \ B.
The finite orientation's strict directed successor relation from any
x in B is *exactly* membership in P_B. Thus every legal component
ranking places every vertex of P_B before every vertex of B.

The lexicographic component-interval order consequently restricts to
C_B with P_B as an initial segment. This is the missing elementary
interface for applying a canonical local complete adjacency-matrix
code over the already ordered lower part. It does not yet identify
the local code minimizers with every globally permitted order, nor
establish any Ramsey degree.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Exactly the proper successors of a generator x form the strict
lower part P_B of the one-component successor closure C_B. -/
theorem strictSuccessor_iff_mem_lowerPart (x y : V) :
    O.StrictSuccessor x y ↔ y ∈ O.lowerPart x := by
  constructor
  · rintro ⟨hxy, hyx⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [O.componentClosure_eq_singleton x]
      exact (O.mem_successorClosure_singleton_iff x y).mpr hxy
    · intro hyB
      exact hyx ((O.mem_component_iff x y).mp hyB).2
  · intro hy
    obtain ⟨hyC, hyNotB⟩ := Finset.mem_sdiff.mp hy
    have hxy : O.Reaches x y := by
      apply (O.mem_successorClosure_singleton_iff x y).mp
      rw [← O.componentClosure_eq_singleton x]
      exact hyC
    refine ⟨hxy, ?_⟩
    intro hyx
    exact hyNotB ((O.mem_component_iff x y).mpr ⟨hxy, hyx⟩)

/-- The lower part P_B precedes the top SCC B in every legal
global component-interval lexicographic order. The statement is
on the actual fixed labelled vertex set, not on component names. -/
theorem globalLexBefore_lowerPart_before_component
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hr : O.IsLinearComponentRanking r) (x : V)
    {y z : V}
    (hy : y ∈ O.lowerPart x)
    (hz : z ∈ O.component x) :
    O.GlobalLexBefore r localRank y z := by
  have hxy : O.StrictSuccessor x y :=
    (O.strictSuccessor_iff_mem_lowerPart x y).mpr hy
  have hxz : O.StronglyConnected x z :=
    (O.mem_component_iff x z).mp hz
  have hzy : O.StrictSuccessor z y :=
    (O.strictSuccessor_transport
      hxz (O.stronglyConnected_refl y)).mp hxy
  exact O.globalLexBefore_successor_first r localRank hr hzy

/-- P_B is an initial segment *inside C_B*: if y belongs to P_B,
z belongs to C_B and z is earlier than y, then z also belongs to
P_B. The condition z ∈ C_B is necessary, since unrelated components
outside C_B may be ordered before its points. -/
theorem globalLexBefore_lowerPart_initial_in_closure
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hr : O.IsLinearComponentRanking r) (x : V)
    {y z : V}
    (hy : y ∈ O.lowerPart x)
    (hz : z ∈ O.componentClosure x)
    (hzy : O.GlobalLexBefore r localRank z y) :
    z ∈ O.lowerPart x := by
  by_cases hzP : z ∈ O.lowerPart x
  · exact hzP
  have hzUnion : z ∈ O.component x ∪ O.lowerPart x := by
    rw [O.component_union_lowerPart x]
    exact hz
  have hzB : z ∈ O.component x := by
    rcases Finset.mem_union.mp hzUnion with hB | hP
    · exact hB
    · exact (hzP hP).elim
  have hyz : O.GlobalLexBefore r localRank y z :=
    O.globalLexBefore_lowerPart_before_component
      r localRank hr x hy hzB
  have hyy : O.GlobalLexBefore r localRank y y :=
    O.globalLexBefore_trans r localRank hyz hzy
  exact (O.globalLexBefore_irrefl r localRank y hyy).elim

/-- Every vertex of C_B is either in the lower initial segment or
in the top SCC, with no interleaving between these two blocks. -/
theorem globalLexBefore_top_after_lower_or_top
    (r : O.ComponentRanking) (localRank : V → ℕ)
    (hr : O.IsLinearComponentRanking r) (x : V)
    {y z : V}
    (hy : y ∈ O.lowerPart x)
    (hz : z ∈ O.componentClosure x)
    (hzNotLower : z ∉ O.lowerPart x) :
    O.GlobalLexBefore r localRank y z := by
  have hzUnion : z ∈ O.component x ∪ O.lowerPart x := by
    rw [O.component_union_lowerPart x]
    exact hz
  have hzB : z ∈ O.component x := by
    rcases Finset.mem_union.mp hzUnion with hB | hP
    · exact hB
    · exact (hzNotLower hP).elim
  exact O.globalLexBefore_lowerPart_before_component r localRank hr x hy hzB

end FiniteOrientation
end BigHrushovski
