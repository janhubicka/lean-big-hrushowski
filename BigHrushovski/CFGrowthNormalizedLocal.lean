import BigHrushovski.CFNormalizedLocalType
import BigHrushovski.CFGrowthClass

/-!
# Growth-class membership under ordered local normalization

An arbitrary finite ordered local extension on P ⊕ B is
represented in the C_F catalogue using the unique increasing
enumeration of B by Fin(card B). This changes neither the
graph nor its growth-function membership. In particular, the
complete adjacency relation, minimal strict d-closed step,
and exact old-neighbour support remain intact.

We isolate the precise numerical interface: a bound on the
*whole* finite local extension yields a bound on its fresh
block, hence an actual record in the bounded catalogue.
The published closure estimate is not reproved here.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {P B : Type*}
variable [Fintype P] [DecidableEq P]
variable [LinearOrder B] [Fintype B] [DecidableEq B]

/-- The unique increasing relabelling preserves membership
in the actual growth-function class, in both directions.
This includes all induced subgraphs and absent edges. -/
theorem growthSparse_orderedNormalize_iff
    (F : ℕ → ℝ) (G : GraphOn (Sum P B)) :
    (orderedNormalizeGraph G).IsGrowthSparse F Finset.univ ↔
      G.IsGrowthSparse F Finset.univ := by
  classical
  let f : Sum P (Fin (Fintype.card B)) ≃ Sum P B :=
    taggedIncreasingEquiv (P := P) (B := B)
  have hAdj : ∀ x y : Sum P (Fin (Fintype.card B)),
      (orderedNormalizeGraph G).adj x y ↔ G.adj (f x) (f y) := by
    intro x y
    exact orderedNormalizeGraph_adj_iff G x y
  have h :=
    (orderedNormalizeGraph G).growthSparse_image_iff
      G F f f.injective hAdj
      (Finset.univ : Finset (Sum P (Fin (Fintype.card B))))
  rw [Finset.image_univ_of_surjective f.surjective] at h
  exact h.symm

/-- A complete finite ordered local graph in C_F gives a
normalized, admissible ordered local-type record. The old
support is kept literally and the chosen fresh order is
transported increasingly. -/
noncomputable def growthLocalType_of_orderedGraph
    (F : ℕ → ℝ)
    (base : GraphOn P)
    (G : GraphOn (Sum P B))
    (hBase : ∀ p q : P,
      G.adj (Sum.inl p) (Sum.inl q) ↔ base.adj p q)
    (hGrowth : G.IsGrowthSparse F Finset.univ)
    (hMin : G.toPredimension.IsMinimalDClosedStep
      (actualOld P B) Finset.univ)
    (hSupport : G.toPredimension.dClosedHull
      (G.oldNeighbourSet (actualOld P B) (actualFresh P B))
      (actualOld P B) = actualOld P B) :
    OrderedLocalType P base
      (fun _ H => H.IsGrowthSparse F Finset.univ)
      (Fintype.card B) :=
  normalizeOrderedLocalType base
    (fun _ H => H.IsGrowthSparse F Finset.univ) G
    hBase
    ((growthSparse_orderedNormalize_iff F G).mpr hGrowth)
    hMin hSupport

/-- With the published whole-extension cardinality bound
provided as an explicit hypothesis, the normalized complete
ordered growth-class code belongs to the actual finite
bounded catalogue. The fresh block's size is not inflated
during normalization. -/
theorem bounded_growthLocalType_of_orderedGraph
    (F : ℕ → ℝ) (K : ℕ)
    (base : GraphOn P)
    (G : GraphOn (Sum P B))
    (hBase : ∀ p q : P,
      G.adj (Sum.inl p) (Sum.inl q) ↔ base.adj p q)
    (hGrowth : G.IsGrowthSparse F Finset.univ)
    (hMin : G.toPredimension.IsMinimalDClosedStep
      (actualOld P B) Finset.univ)
    (hSupport : G.toPredimension.dClosedHull
      (G.oldNeighbourSet (actualOld P B) (actualFresh P B))
      (actualOld P B) = actualOld P B)
    (hTotal : Fintype.card P + Fintype.card B ≤ K) :
    ∃ code : BoundedOrderedLocalType P base
        (fun _ H => H.IsGrowthSparse F Finset.univ) K,
      code.1.val = Fintype.card B ∧
      code.2.graph = orderedNormalizeGraph G ∧
      code ∈ catalogue base
        (fun _ H => H.IsGrowthSparse F Finset.univ) K := by
  let t := growthLocalType_of_orderedGraph F base G
    hBase hGrowth hMin hSupport
  have hFresh : Fintype.card B ≤ K := by omega
  let code : BoundedOrderedLocalType P base
      (fun _ H => H.IsGrowthSparse F Finset.univ) K :=
    toBounded base (fun _ H => H.IsGrowthSparse F Finset.univ)
      K (Fintype.card B) hFresh t
  refine ⟨code, rfl, rfl, ?_⟩
  exact mem_catalogue base
    (fun _ H => H.IsGrowthSparse F Finset.univ) K code

end CFLocalCatalogue
end BigHrushovski
