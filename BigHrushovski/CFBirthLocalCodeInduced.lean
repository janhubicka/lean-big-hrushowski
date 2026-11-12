import BigHrushovski.CFBirthLocalRoots
import BigHrushovski.CFBatchLocalInduced

/-!
# Complete local request graph in the actual C_F birth carrier

The finite tagged level contains exactly the complete ordered
local graph of each request, including all nonedges. Every finite
stage is itself induced in the countable birth graph. Their
composition gives the direct code-reading interface needed for
the uniqueness of arbitrary finite functional level lifts.

The equations are literal: old support vertices retain their
birth names from the old stage, and fresh vertices retain the
actual request tag and ordinal. There is no choice of an
abstractly isomorphic graph or an arbitrary renumbering.

This does not by itself identify two target request records:
the next lemma must show that an arbitrary induced ordered
embedding maps the whole local coordinate system to the
one determined by the old support and the source block ordinals.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every edge and nonedge of an actual bounded local request is
exactly the corresponding edge or nonedge of the countable
birth graph, on the literal tagged image of its old support
and complete fresh block. -/
theorem birthRequest_localAdj_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (a b : Sum
      (SupportCarrier (stage F K n).carrier r.support)
      (Fin r.code.1.val)) :
    (countableGraph F K).adj
        (toVertex F K (n + 1)
          (localTag (stage F K n).graph
            (GrowthAllowedLocal F) (fun P => K P.card) r a))
        (toVertex F K (n + 1)
          (localTag (stage F K n).graph
            (GrowthAllowedLocal F) (fun P => K P.card) r b)) ↔
      r.code.2.graph.adj a b := by
  exact (countableGraph_stage_induced F K (n + 1)
    (localTag (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r a)
    (localTag (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r b)).trans
    (levelGraph_local_adj_iff
      (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r a b)

/-- The old–fresh part of the complete request matrix is
literally read from edges between the named old support and
the new request-tagged birth block in the countable graph. -/
theorem birthRequest_oldFreshAdj_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (u : SupportCarrier (stage F K n).carrier r.support)
    (i : Fin r.code.1.val) :
    (countableGraph F K).adj
        (toVertex F K n u.val)
        (⟨n, ⟨r, i⟩⟩ : Vertex F K) ↔
      r.code.2.graph.adj (Sum.inl u) (Sum.inr i) := by
  simpa only [localTag, toVertex_old, toVertex_new] using
    birthRequest_localAdj_iff F K n r (Sum.inl u) (Sum.inr i)

/-- The fresh–fresh entries of the same complete matrix are
also exactly the ambient countable graph edges and nonedges. -/
theorem birthRequest_freshFreshAdj_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (i j : Fin r.code.1.val) :
    (countableGraph F K).adj
        (⟨n, ⟨r, i⟩⟩ : Vertex F K)
        (⟨n, ⟨r, j⟩⟩ : Vertex F K) ↔
      r.code.2.graph.adj (Sum.inr i) (Sum.inr j) := by
  simpa only [localTag, toVertex_new] using
    birthRequest_localAdj_iff F K n r (Sum.inr i) (Sum.inr j)

/-- The old–old entries are precisely the induced graph of the
named support. This is included explicitly to avoid treating
a code as only old–fresh and fresh–fresh adjacency data. -/
theorem birthRequest_oldOldAdj_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (u v : SupportCarrier (stage F K n).carrier r.support) :
    (countableGraph F K).adj
        (toVertex F K n u.val)
        (toVertex F K n v.val) ↔
      r.code.2.graph.adj (Sum.inl u) (Sum.inl v) := by
  simpa only [localTag, toVertex_old] using
    birthRequest_localAdj_iff F K n r (Sum.inl u) (Sum.inl v)

end CFCoherentTower
end BigHrushovski
