import BigHrushovski.CFBatchLocalInduced

/-!
# The actual growth-function class C_F on finite induced graphs

For a real-valued growth bound F, an induced finite graph A belongs
to the growth-function class when every finite subset X of A has

    F(|X|) ≤ δ(X).

This matches the published C_F definition at integer arguments.
It is **not** equivalent to mere 2-sparsity.

We verify heredity and exact invariance under induced embeddings.
We also isolate, as an explicit assumption, closure under free
amalgamation over a common strictly d-closed substructure.

Neither monotonicity of F nor submodularity of predimension is
claimed to prove this free-amalgamation property. It is a
standing hypothesis of the published C_F construction.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Growth-function sparsity on an actual finite induced vertex
set. The real-valued F is evaluated only at cardinalities. -/
def IsGrowthSparse (F : ℕ → ℝ) (a : Finset V) : Prop :=
  ∀ s : Finset V, s ⊆ a → F s.card ≤ (G.predim s : ℝ)

/-- Membership in the growth class is hereditary for finite
induced vertex subsets. -/
theorem growthSparse_restrict
    (F : ℕ → ℝ) {a b : Finset V}
    (hGrowth : G.IsGrowthSparse F b) (hab : a ⊆ b) :
    G.IsGrowthSparse F a := by
  intro s hsa
  exact hGrowth s (hsa.trans hab)

/-- A nonnegative growth function forces ordinary 2-sparsity,
but the converse is not claimed. -/
theorem twoSparse_of_growthSparse
    (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (a : Finset V) (hGrowth : G.IsGrowthSparse F a) :
    G.IsTwoSparse a := by
  intro s hsa
  have hδ : (0 : ℝ) ≤ (G.predim s : ℝ) :=
    (hF s.card).trans (hGrowth s hsa)
  exact_mod_cast hδ

/-- Exact invariance of C_F membership under an injective
graph map preserving both edges and nonedges, *within the
image of the finite induced graph*. -/
theorem growthSparse_image_iff
    {W : Type*} [DecidableEq W]
    (H : GraphOn W)
    (F : ℕ → ℝ)
    (f : V → W) (hf : Function.Injective f)
    (hAdj : ∀ x y : V, G.adj x y ↔ H.adj (f x) (f y))
    (a : Finset V) :
    H.IsGrowthSparse F (a.image f) ↔ G.IsGrowthSparse F a := by
  classical
  constructor
  · intro hTarget
    intro s hsa
    have hBound := hTarget (s.image f) (Finset.image_mono f hsa)
    change F (s.image f).card ≤ (H.predim (s.image f) : ℝ) at hBound
    rw [Finset.card_image_of_injective s hf,
      G.predim_image H f hf hAdj s] at hBound
    exact hBound
  · intro hSource
    intro t hta
    let s : Finset V := a.filter (fun x => f x ∈ t)
    have hs : s ⊆ a := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    have ht : s.image f = t :=
      finite_image_preimage_within f a t hta
    change F t.card ≤ (H.predim t : ℝ)
    rw [← ht, Finset.card_image_of_injective s hf,
      G.predim_image H f hf hAdj s]
    exact hSource s hs

/-- The *independent* class-level free-amalgamation hypothesis.
Whenever two finite growth-class members overlap in a d-closed
subgraph and are joined with no crossing edges, their union
again belongs to the class. This is a hypothesis on the
restricted class, not a consequence of the graph definition. -/
def GrowthClosedUnderDClosedFreeJoins
    (F : ℕ → ℝ) : Prop :=
  ∀ a b : Finset V,
    G.NoCrossEdges a b →
    G.toPredimension.IsDClosed (a ∩ b) a →
    G.toPredimension.IsDClosed (a ∩ b) b →
    G.IsGrowthSparse F a →
    G.IsGrowthSparse F b →
    G.IsGrowthSparse F (a ∪ b)

/-- Apply the explicitly assumed free-amalgamation closure
property to two finite pieces over their exact common
d-closed support. -/
theorem growthSparse_free_join
    (F : ℕ → ℝ)
    (hFree : G.GrowthClosedUnderDClosedFreeJoins F)
    (P a b : Finset V)
    (hCap : a ∩ b = P)
    (hNo : G.NoCrossEdges a b)
    (hPA : G.toPredimension.IsDClosed P a)
    (hPB : G.toPredimension.IsDClosed P b)
    (hA : G.IsGrowthSparse F a)
    (hB : G.IsGrowthSparse F b) :
    G.IsGrowthSparse F (a ∪ b) := by
  have hInterA : G.toPredimension.IsDClosed (a ∩ b) a := by
    simpa only [hCap] using hPA
  have hInterB : G.toPredimension.IsDClosed (a ∩ b) b := by
    simpa only [hCap] using hPB
  exact hFree a b hNo hInterA hInterB hA hB

end GraphOn
end BigHrushovski
