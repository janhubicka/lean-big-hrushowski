import BigHrushovski.CFBatchLocalInduced

/-!
# Exact old-fresh boundary of one tagged C_F request

An edge between an old vertex u and a fresh vertex tagged by
request r exists if and only if u lies in the actual named
support of r and the complete local graph of r contains the
corresponding boundary edge.

The already certified finite batch graph construction proves
that any edge incident with a fresh r-vertex must originate
from the *same* request r. This gives the reverse implication,
including all absent boundary edges and the case where u
lies outside r's support. The forward implication is the
local-code edge insertion.

This is the precise missing ingredient for lifting a complete
minimal extension over a prescribed larger old source: the
fresh block has no old neighbours outside its named support.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Complete characterization of old-to-fresh adjacency in an
actual simultaneous tagged level, including the reflected
absence of edges outside the named support. -/
theorem tagged_old_fresh_adj_iff
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (u : U) (i : Fin r.code.1.val) :
    (levelGraph G Allowed bound).adj
      (Sum.inl u) (Sum.inr ⟨r, i⟩) ↔
      ∃ q : SupportCarrier U r.support,
        q.val = u ∧
        r.code.2.graph.adj (Sum.inl q) (Sum.inr i) := by
  constructor
  · intro h
    have hs : (levelGraph G Allowed bound).adj
        (Sum.inr ⟨r, i⟩) (Sum.inl u) :=
      (levelGraph G Allowed bound).symm _ _ h
    obtain ⟨a, b, ha, hb, hab⟩ :=
      levelGraph_edge_from_fresh G Allowed bound
        r i (Sum.inl u) hs
    have haEq : a = Sum.inr i := by
      apply localTag_injective G Allowed bound r
      change localTag G Allowed bound r a =
        localTag G Allowed bound r (Sum.inr i)
      exact ha
    subst a
    cases b with
    | inl q =>
        have hVal : q.val = u := by
          exact Sum.inl.inj hb
        refine ⟨q, hVal, ?_⟩
        exact r.code.2.graph.symm _ _ hab
    | inr j =>
        cases hb
  · rintro ⟨q, hq, hcode⟩
    have hEdge := levelGraph_local_edge G Allowed bound
      r (Sum.inl q) (Sum.inr i) hcode
    simpa only [localTag, hq] using hEdge

/-- No vertex outside the literal support of r is adjacent
to any of its fresh vertices. This is a theorem about the
constructed tagged level, not an auxiliary no-cross axiom. -/
theorem tagged_no_old_fresh_outside_support
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (u : U) (hu : u ∉ r.support)
    (i : Fin r.code.1.val) :
    ¬ (levelGraph G Allowed bound).adj
      (Sum.inl u) (Sum.inr ⟨r, i⟩) := by
  intro h
  obtain ⟨q, hq, _⟩ :=
    (tagged_old_fresh_adj_iff G Allowed bound r u i).mp h
  exact hu (hq ▸ q.property)

end CFStageCatalogue
end BigHrushovski
