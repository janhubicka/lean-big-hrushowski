import BigHrushovski.CFDClosedHullDelta
import BigHrushovski.CFGrowthClass
import BigHrushovski.CFDClosedGenerators

/-!
# A uniform size bound for minimal strict d-closed growth-class extensions

The finite hull inequality δ(clᵈ_C(S)) ≤ δ(S), together with
δ(S) ≤ 2|S| for graph predimension, yields the numerical estimate

  F(|clᵈ_C(S)|) ≤ 2|S|

whenever the ambient finite graph C satisfies the growth
lower bound F. For a minimal strict d-closed step A <ᵈ E,
every new x generates E over A, so

  F(|E|) ≤ 2(|A|+1).

We express the inverse-size hypothesis as a separate
property of the numerical functions F and K. This makes
the combinatorial part independent of any analytic
construction of the generalized inverse.

A stronger result using the canonical generalized inverse
of a monotone unbounded real function can be added after
its numerical properties have been formalized.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- For the two-sparse graph predimension δ(X)=2|X|-|E(X)|,
one always has δ(X) ≤ 2|X|, without a sparsity assumption. -/
theorem predim_le_twice_card (s : Finset V) :
    G.predim s ≤ 2 * (s.card : ℤ) := by
  unfold predim
  omega

/-- Exact growth upper bound on the size of any finite
strict d-closed hull. The only growth-class hypothesis is
the inequality for all induced subsets of the ambient C. -/
theorem growth_dClosedHull_le_twice_card
    (F : ℕ → ℝ) (s c : Finset V)
    (hsc : s ⊆ c) (hGrowth : G.IsGrowthSparse F c) :
    F (G.toPredimension.dClosedHull s c).card ≤
      2 * (s.card : ℝ) := by
  let h := G.toPredimension.dClosedHull s c
  have hhClosed : G.toPredimension.IsDClosed h c :=
    G.toPredimension.dClosedHull_dclosed s c
  have hGrowthH : F h.card ≤ (G.predim h : ℝ) :=
    hGrowth h hhClosed.1
  have hDelta : G.predim h ≤ 2 * (s.card : ℤ) := by
    calc
      G.predim h ≤ G.predim s :=
        G.toPredimension.delta_dClosedHull_le hsc
      _ ≤ 2 * (s.card : ℤ) := G.predim_le_twice_card s
  have hReal : (G.predim h : ℝ) ≤ 2 * (s.card : ℝ) := by
    exact_mod_cast hDelta
  exact hGrowthH.trans hReal

/-- A minimal strict d-closed extension in the growth class
has its *entire* endpoint bounded by K(|A|), provided
K dominates the generalized inverse at 2(|A|+1).
The inverse property is explicitly supplied as a
hypothesis on F and K. -/
theorem minimal_growth_extension_card_le
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hInverse : ∀ k n : ℕ,
      F n ≤ 2 * (((k + 1 : ℕ) : ℝ)) → n ≤ K k)
    (a b : Finset V)
    (hMin : G.toPredimension.IsMinimalDClosedStep a b)
    (hGrowth : G.IsGrowthSparse F b)
    (x : V) (hxb : x ∈ b) (hxna : x ∉ a) :
    b.card ≤ K a.card := by
  have hInsert : insert x a ⊆ b := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hya
    · exact hxb
    · exact hMin.1.1 hya
  have hGeneration :
      G.toPredimension.dClosedHull (insert x a) b = b :=
    G.toPredimension.minimalDClosedStep_every_generator
      hMin hxb hxna
  have hEstimate :=
    G.growth_dClosedHull_le_twice_card F
      (insert x a) b hInsert hGrowth
  rw [hGeneration] at hEstimate
  have hCard : (insert x a).card = a.card + 1 := by
    simp [hxna]
  rw [hCard] at hEstimate
  exact hInverse a.card b.card hEstimate

/-- The actual fresh block has no greater cardinality than
the entire minimal local extension. Consequently the
same conservative bound K(|A|) covers every request block. -/
theorem minimal_growth_fresh_card_le
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hInverse : ∀ k n : ℕ,
      F n ≤ 2 * (((k + 1 : ℕ) : ℝ)) → n ≤ K k)
    (a fresh : Finset V)
    (hDisj : Disjoint a fresh)
    (hMin : G.toPredimension.IsMinimalDClosedStep
      a (a ∪ fresh))
    (hGrowth : G.IsGrowthSparse F (a ∪ fresh))
    (x : V) (hx : x ∈ fresh) :
    fresh.card ≤ K a.card := by
  have hxna : x ∉ a := by
    intro hxa
    exact (Finset.disjoint_left.mp hDisj) hxa hx
  have hTotal : (a ∪ fresh).card ≤ K a.card :=
    G.minimal_growth_extension_card_le F K hInverse
      a (a ∪ fresh) hMin hGrowth x
      (Finset.mem_union_right a hx) hxna
  exact (Finset.card_le_card Finset.subset_union_right).trans hTotal

end GraphOn
end BigHrushovski
