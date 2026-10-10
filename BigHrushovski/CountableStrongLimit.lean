import BigHrushovski.CoherentNatGraph
import BigHrushovski.FiniteInducedAgreement
import BigHrushovski.C0Sparsity

/-!
# Strong finite stages remain strong in the countable graph union

For an explicitly given coherent Nat-stage graph system, assume
the finite stage n is strong in stage n+1, computed in the latter
finite graph. The direct-limit graph is induced on every finite
stage. Hence local finite strongness transfers to the limit graph,
and the existing StrongChain theorem makes every stage globally
strong and supplies finite strong covers.

If the finite stage graphs are all two-sparse, the limit graph has
nonnegative predimension on every finite set.

These are implications from a coherent stage system. Constructing
one that answers every scheduled request remains the outstanding task.
-/

namespace BigHrushovski
namespace CoherentNatGraphStages

variable (S : CoherentNatGraphStages)

/-- Strongness computed inside the successor finite graph. -/
def HasStrongSteps : Prop :=
  ∀ n, (S.graph (n + 1)).toPredimension.IsStrong
    (S.stage n) (S.stage (n + 1))

/-- Every finite stage is two-sparse on its own support. -/
def HasTwoSparseStages : Prop :=
  ∀ n, (S.graph n).IsTwoSparse (S.stage n)

/-- A coherent chain with relatively strong successor inclusions becomes
a strong chain in its direct-limit graph. This is the precise bridge
between the graph-union module and the existing abstract StrongChain API. -/
def asStrongChain (hStrong : S.HasStrongSteps) :
    Predimension.StrongChain S.limitGraph.toPredimension where
  stage := S.stage
  strong_step := by
    intro n
    have hAdj : ∀ x ∈ S.stage (n + 1), ∀ y ∈ S.stage (n + 1),
        S.limitGraph.adj x y ↔ (S.graph (n + 1)).adj x y := by
      intro x hx y hy
      exact S.limitGraph_induced (n + 1) hx hy
    exact (S.limitGraph.isStrong_iff_of_agreeOn
      (S.graph (n + 1)) (S.stage n) (S.stage (n + 1))
      (S.stage_step n) hAdj).mpr (hStrong n)
  covers := S.covers

/-- Each constructed finite stage is globally strong in the direct limit. -/
theorem stage_global_of_strong_steps
    (hStrong : S.HasStrongSteps) (n : ℕ) :
    S.limitGraph.toPredimension.IsGloballyStrong (S.stage n) :=
  (S.asStrongChain hStrong).stage_global n

/-- The limit inherits the finite strong-cover property. -/
theorem finiteStrongCover_of_strong_steps
    (hStrong : S.HasStrongSteps) :
    Predimension.FiniteStrongCover S.limitGraph.toPredimension :=
  (S.asStrongChain hStrong).toFiniteStrongCover

/-- If every stage is two-sparse, the union is two-sparse on every
finite vertex set. The conclusion cannot be expressed as a two-sparse
Finset.univ, since ℕ itself is infinite. -/
theorem limit_predim_nonneg_of_sparse_stages
    (hStrong : S.HasStrongSteps)
    (hSparse : S.HasTwoSparseStages) :
    ∀ s : Finset ℕ, 0 ≤ S.limitGraph.predim s := by
  intro s
  obtain ⟨n, hSubset⟩ := (S.asStrongChain hStrong).contains_finite s
  have hAdj : ∀ x ∈ s, ∀ y ∈ s,
      S.limitGraph.adj x y ↔ (S.graph n).adj x y := by
    intro x hx y hy
    exact S.limitGraph_induced n (hSubset hx) (hSubset hy)
  have hDelta :=
    S.limitGraph.predim_eq_of_agreeOn (S.graph n) s hAdj
  rw [hDelta]
  exact hSparse n s hSubset

end CoherentNatGraphStages
end BigHrushovski
