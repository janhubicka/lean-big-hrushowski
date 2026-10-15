import BigHrushovski.CFStageEmbeddings

/-!
# The countable graph of the C_F birth-labelled tower

An unordered edge between two birth-labelled vertices is declared
when it is already present between their representatives in some
finite stage. The definition is symmetric and irreflexive because
the finite-stage maps into birth labels are injective and every
finite-stage graph is symmetric and irreflexive.

Every edge in every finite stage is therefore present in the
countable graph. The converse (that no additional edge is
introduced between two vertices from a fixed earlier stage)
requires the iterated inducedness and common-stage comparison
argument. It is deliberately *not* asserted in this module.

The domain is countable, but the graph has not yet been proved to
be the strict d-closed C_F generic: this will require the
stage-inducedness converse, global strict d-closure and the
one-level extension response property.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Two vertices in the canonical countable carrier are adjacent
when a finite stage contains adjacent representatives of both.
No limit graph or edge-compatibility assumption is postulated. -/
def BornAdjacent (F : ℕ → ℝ) (K : ℕ → ℕ)
    (x y : Vertex F K) : Prop :=
  ∃ n : ℕ, ∃ a b : (stage F K n).carrier,
    toVertex F K n a = x ∧
    toVertex F K n b = y ∧
    (stage F K n).graph.adj a b

/-- The genuinely constructed graph on the countable
birth-labelled carrier. -/
noncomputable def countableGraph (F : ℕ → ℝ) (K : ℕ → ℕ) :
    GraphOn (Vertex F K) where
  adj := BornAdjacent F K
  symm := by
    intro x y h
    obtain ⟨n, a, b, hax, hby, hab⟩ := h
    exact ⟨n, b, a, hby, hax,
      (stage F K n).graph.symm a b hab⟩
  irrefl := by
    intro x h
    obtain ⟨n, a, b, hax, hbx, hab⟩ := h
    have habEq : a = b :=
      toVertex_injective F K n (hax.trans hbx.symm)
    subst b
    exact (stage F K n).graph.irrefl a hab

/-- Every finite-stage edge survives in the countable graph.
Reflection of nonedges needs a common-stage coherence proof. -/
theorem stage_edge_in_countableGraph
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (a b : (stage F K n).carrier)
    (hab : (stage F K n).graph.adj a b) :
    (countableGraph F K).adj
      (toVertex F K n a) (toVertex F K n b) := by
  exact ⟨n, a, b, rfl, rfl, hab⟩

/-- Each vertex of the countable graph already occurs in a
finite stage; this is carrier coverage, not yet the full
finite-set cover by one common stage. -/
theorem countableGraph_vertex_covered
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (x : Vertex F K) :
    ∃ n : ℕ, ∃ a : (stage F K n).carrier,
      toVertex F K n a = x :=
  everyVertex_in_stage F K x

end CFCoherentTower
end BigHrushovski
