import BigHrushovski.CFOneLevelTargetTagRigidity
import BigHrushovski.CFArbitraryFiniteEmbeddingRigidity

/-!
# The whole local request is contained in a b-closed finite source

A finite substructure of the C_F block presentation is closed
under each *complete* unary support-and-block value. Thus,
when one fresh vertex of a request is in the finite source,
every old support coordinate and every fresh coordinate of
that local request belongs to the same source.

An arbitrary induced map of the finite source therefore
restricts to a map of the *entire* actual local request
carrier, and this restriction preserves and reflects all
edges, including nonedges. No map of the full old stage,
or an artificially chosen isomorphic copy of the local
graph, is needed.

This is the inducedness premise of the pending complete
request-code comparison for arbitrary finite embeddings.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every coordinate of the complete literal local graph of
a source request belongs to a b-closed finite source as soon
as that source contains one fresh vertex of the request. -/
theorem birthRequestLocalVertex_mem_closed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s)
    (a : BirthRequestLocalCarrier F K n r) :
    birthRequestLocalVertex F K n r a ∈ s := by
  cases a with
  | inl u =>
      change toVertex F K n u.val ∈ s
      exact (hs n r i hi).2 u.val u.property
  | inr j =>
      change (⟨n, ⟨r, j⟩⟩ : Vertex F K) ∈ s
      exact (hs n r i hi).1 j

/-- Restrict any partial finite source map to the COMPLETE
old-support plus fresh-block coordinates of one source request.
The restriction is well defined without extending the map to
the complete old finite stage. -/
noncomputable def arbitraryFiniteEmbedding_localMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    BirthRequestLocalCarrier F K n r → Vertex F K :=
  fun a =>
    e ⟨birthRequestLocalVertex F K n r a,
      birthRequestLocalVertex_mem_closed F K s hs n r i hi a⟩

/-- The map just restricted to one complete local request is
induced on ALL pairs of old and fresh coordinates, provided
the original finite source map is induced. This explicitly
reflects every nonedge as well as preserving edges. -/
theorem arbitraryFiniteEmbedding_localMap_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s)
    (a b : BirthRequestLocalCarrier F K n r) :
    (countableGraph F K).adj
      (birthRequestLocalVertex F K n r a)
      (birthRequestLocalVertex F K n r b) ↔
    (countableGraph F K).adj
      (arbitraryFiniteEmbedding_localMap
        F K s hs e n r i hi a)
      (arbitraryFiniteEmbedding_localMap
        F K s hs e n r i hi b) := by
  exact heAdj
    ⟨birthRequestLocalVertex F K n r a,
      birthRequestLocalVertex_mem_closed F K s hs n r i hi a⟩
    ⟨birthRequestLocalVertex F K n r b,
      birthRequestLocalVertex_mem_closed F K s hs n r i hi b⟩

end CFCoherentTower
end BigHrushovski
