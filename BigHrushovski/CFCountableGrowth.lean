import BigHrushovski.CFCountableInduced
import BigHrushovski.CFGrowthClass

/-!
# Finite cover and growth inequality for the countable C_F graph

Every vertex of the birth-labelled universe occurs in a finite
stage. To transfer finite induced predimension, it is essential
that any *finite family* of vertices already lies in the image
of one common stage.

The canonical old embeddings show that stage images are
monotone. Finite induction therefore produces a common
stage containing an arbitrary finite set. Exact inducedness
of that stage in the countable graph permits transport of
the complete growth-function inequality.

The conclusion is conditional on growth membership of all
finite stages; the latter is itself conditional on the
restricted d-closed free-amalgamation hypothesis for C_F.
No strict global d-closure or generic extension property is
asserted here.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The image of the complete finite stage U_n in the canonical
countable birth-labelled vertex set. -/
noncomputable def stageImage (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) : Finset (Vertex F K) := by
  classical
  exact (Finset.univ : Finset (stage F K n).carrier).image
    (toVertex F K n)

/-- Every earlier finite-stage image lies in every later one.
No arbitrary finite graph isomorphism is used. -/
theorem stageImage_mono
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    {n m : ℕ} (hnm : n ≤ m) :
    stageImage F K n ⊆ stageImage F K m := by
  classical
  intro v hv
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr
    ⟨embedToLater F K n m hnm a,
      Finset.mem_univ _,
      (toVertex_embedToLater F K n m hnm a).symm⟩

/-- Each birth-labelled vertex belongs to its birth successor
stage, and hence to a finite stage image. -/
theorem vertex_in_some_stageImage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) :
    ∃ n : ℕ, v ∈ stageImage F K n := by
  classical
  obtain ⟨n, a, ha⟩ := everyVertex_in_stage F K v
  exact ⟨n, Finset.mem_image.mpr
    ⟨a, Finset.mem_univ _, ha⟩⟩

/-- Every finite set of vertices of the countable C_F graph
is contained in the image of one *common* finite stage. -/
theorem finiteSet_covered
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    ∃ n : ℕ, s ⊆ stageImage F K n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, Finset.empty_subset _⟩
  | @insert v s hnot ih =>
      obtain ⟨n, hSub⟩ := ih
      obtain ⟨m, hV⟩ := vertex_in_some_stageImage F K v
      refine ⟨max n m, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hEq | hMem
      · subst x
        exact stageImage_mono F K (Nat.le_max_right n m) hV
      · exact stageImage_mono F K (Nat.le_max_left n m)
          (hSub hMem)

/-- If every finite stage belongs to the growth-function
class C_F, then *every finite vertex set* of the countable
graph satisfies the same exact predimension inequality. -/
theorem countableGraph_growth_of_stages
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hStages : ∀ n,
      (stage F K n).graph.IsGrowthSparse F
        (Finset.univ : Finset (stage F K n).carrier)) :
    ∀ s : Finset (Vertex F K),
      F s.card ≤ ((countableGraph F K).predim s : ℝ) := by
  classical
  intro s
  obtain ⟨n, hs⟩ := finiteSet_covered F K s
  have hImage : (countableGraph F K).IsGrowthSparse F
      (stageImage F K n) := by
    exact ((stage F K n).graph.growthSparse_image_iff
      (countableGraph F K) F
      (toVertex F K n) (toVertex_injective F K n)
      (fun a b => (countableGraph_stage_induced F K n a b).symm)
      Finset.univ).mpr (hStages n)
  exact hImage s hs

/-- Combining the finite-stage induction with finite
coverage yields the C_F growth inequality in the countable
limit, *conditional on the exact class-level free-join
hypothesis*. -/
theorem countableGraph_growth_of_freeJoins
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hEmpty : emptyStage.graph.IsGrowthSparse F
      (Finset.univ : Finset emptyStage.carrier))
    (hFree : ∀ n,
      (stage F K (n + 1)).graph.GrowthClosedUnderDClosedFreeJoins F) :
    ∀ s : Finset (Vertex F K),
      F s.card ≤ ((countableGraph F K).predim s : ℝ) := by
  exact countableGraph_growth_of_stages F K
    (all_stages_growth F K hEmpty hFree)

end CFCoherentTower
end BigHrushovski
