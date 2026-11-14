import BigHrushovski.C0CoordinateRawGeneratedStageWitness
import BigHrushovski.C0Sparsity

/-!
# Two-sparseness from a finite canonical C₀ stage witness

A complete finite C₀ stage/value witness allows empty stages.
Every nonempty stage is minimal strong. Starting with the empty
graph, use preservation of two-sparseness across a strong extension
at each stage; empty stages preserve it by equality.

This supplies the missing two-sparseness hypothesis for finite
presented factors in the two-sided functional amalgamation theorem.
No new graph counting argument or unverified predimension axiom
is introduced. The proof does not assert that arbitrary closed
unions in the raw host have finite presentations.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Every graph with a finite canonical C₀ stage witness (empty
steps allowed) is 2-sparse on its whole finite carrier. In
particular, this does not require an extra sparsity field in the
witness structure. -/
theorem hasCanonicalC0StageValues_twoSparse
    (G : GraphOn U) (C : U → Finset U)
    (h : HasCanonicalC0StageValues G C) :
    G.IsTwoSparse (Finset.univ : Finset U) := by
  classical
  obtain ⟨n,κ,hSteps,_hValues⟩ := h
  have hOldZero :
      FiniteC0.oldStage κ 0 = (∅ : Finset U) := by
    ext v
    simp [FiniteC0.mem_oldStage_iff]
  have hOldFinal :
      FiniteC0.oldStage κ n = (Finset.univ : Finset U) := by
    ext v
    simp [FiniteC0.mem_oldStage_iff, (κ v).isLt]
  have hEmptySparse :
      G.IsTwoSparse (∅ : Finset U) := by
    intro s hs
    have hEmpty : s = ∅ := Finset.subset_empty.mp hs
    subst s
    simp [GraphOn.predim, GraphOn.edgesWithin, GraphOn.IsEdge]
  have hStagesSparse :
      ∀ k : ℕ, k ≤ n →
        G.IsTwoSparse (FiniteC0.oldStage κ k) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [hOldZero] using hEmptySparse
    | succ k ih =>
        intro hk
        have hkn : k < n := Nat.lt_of_succ_le hk
        have hPrev : G.IsTwoSparse (FiniteC0.oldStage κ k) :=
          ih (Nat.le_of_lt hkn)
        have hStrong :
            G.toPredimension.IsStrong
              (FiniteC0.oldStage κ k)
              (FiniteC0.oldStage κ (k+1)) := by
          rcases hSteps k hkn with hEq | hMin
          · rw [hEq]
            exact G.toPredimension.strong_refl _
          · exact hMin.1
        exact G.twoSparse_of_strong_extension hPrev hStrong
  simpa only [hOldFinal] using hStagesSparse n (Nat.le_refl n)

/-- Every full raw one-generated C-value is 2-sparse in its
induced graph. This statement follows from an actual finite
canonical stage witness; it is NOT a claim that every arbitrary
finite raw-host subset is 2-sparse. -/
theorem RawC0CoordinateVertex.closedValue_twoSparse
    [DecidableEq RawC0CoordinateVertex]
    (q : RawC0CoordinateVertex) :
    (rawC0HostGraph.pullback
      (Subtype.val : q.closedValue → RawC0CoordinateVertex)).IsTwoSparse
        (Finset.univ : Finset q.closedValue) := by
  exact hasCanonicalC0StageValues_twoSparse
    (rawC0HostGraph.pullback
      (Subtype.val : q.closedValue → RawC0CoordinateVertex))
    (RawC0CoordinateVertex.valueOn q.closedValue)
    (q.closedValue_hasStageValuePresentation)

end FiniteUnaryCoordinates
end BigHrushovski
