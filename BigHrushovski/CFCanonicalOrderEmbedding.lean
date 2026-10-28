import BigHrushovski.CFCanonicalStageOrder

/-!
# Exact C_F manuscript order and the two functional presentations

The previous theorem on closed-source embeddings assumed an arbitrary
strict order compatible with the literal finite order within every
birth block. The recursively constructed canonicalBirthLt is precisely
the lexicographic order prescribed in the manuscript, and its block
compatibility has now been proved without extra assumptions.

This module substitutes the *actual* manuscript order into the
closed-source embedding equivalence. Sources may be empty or infinite;
no artificial additional requirement on the internal block ordinal
of the embedding is introduced.

The theorem identifies the b- and (R,H)-embedding conditions under
the SAME adjacency, level, and canonical order requirements. It does
not prove the unique lifting of arbitrary finite level assignments
or the embedding monoid theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- For the actual recursively constructed C_F order, preservation
of the complete temporary unary b-values is equivalent to the
complete R- and partial H-values, including reflection of H's
domain. The source is an arbitrary literal b-closed subtype and
may be empty. There is no separate order compatibility assumption. -/
theorem literalClosedSource_bValues_iff_RHValues_of_canonicalOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (e : {v : Vertex F K // v ∈ X} → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ u v : {v : Vertex F K // v ∈ X},
      (countableGraph F K).adj u.val v.val ↔
        (countableGraph F K).adj (e u) (e v))
    (heLevel : ∀ u v : {v : Vertex F K // v ∈ X},
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (e u) (e v))
    (heOrder : ∀ u v : {v : Vertex F K // v ∈ X},
      canonicalBirthLt F K u.val v.val ↔
        canonicalBirthLt F K (e u) (e v)) :
    let f := extendClosedSourceMap F K X e
    (∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v)) ↔
      (∀ v ∈ X,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        (∀ r ∈ s, IsBirthRoot F K r) →
        (birthDClosedHull F K s).image f =
          birthDClosedHull F K (s.image f)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        ((∀ r ∈ s, IsBirthRoot F K r) ↔
          (∀ r ∈ s.image f, IsBirthRoot F K r))) := by
  exact literalClosedSource_bValues_iff_RHValues_of_chosenOrder
    F K X hX (canonicalBirthLt F K)
    (canonicalBirthLt_compatible F K)
    e heInj heAdj heLevel heOrder

end CFCoherentTower
end BigHrushovski
