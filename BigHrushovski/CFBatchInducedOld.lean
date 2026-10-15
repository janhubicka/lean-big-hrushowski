import BigHrushovski.CFSimultaneousGraph

/-!
# Induced old-stage graph and exact support boundary of a batch

The tagged finite batch graph has the old graph as an *induced*
subgraph. Edges contributed by other local request codes do not
change the old adjacency relation because every ordered local
type agrees with the graph on its actual named support.

Further, each fresh vertex can meet old vertices only in its
own prescribed support. This is a property of the actual
constructed graph, not a no-cross hypothesis on a later proof.

Induced equality of an entire local graph also requires
checking the within-block and fresh-to-old adjacencies
in both directions; that is the subsequent obligation.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The tagged simultaneous graph preserves and reflects
adjacency on every pair of old vertices, including nonedges. -/
theorem levelGraph_old_iff
    (G : GraphOn U)
    (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (u v : U) :
    (levelGraph G Allowed bound).adj
      (Sum.inl u) (Sum.inl v) ↔ G.adj u v := by
  constructor
  · intro h
    rcases h with ⟨a, b, ha, hb, hab⟩ |
      ⟨r, a, b, ha, hb, hab⟩
    · have hau : a = u := Sum.inl.inj ha
      have hbv : b = v := Sum.inl.inj hb
      simpa [hau, hbv] using hab
    · cases a with
      | inr i => cases ha
      | inl p =>
        cases b with
        | inr j => cases hb
        | inl q =>
          have hpu : p.val = u := Sum.inl.inj ha
          have hqv : q.val = v := Sum.inl.inj hb
          have hEdge := (r.code.2.base_agrees p q).mp hab
          change G.adj p.val q.val at hEdge
          simpa [hpu, hqv] using hEdge
  · exact levelGraph_old_edge G Allowed bound u v

/-- A fresh block cannot acquire an old neighbour outside
its *actual* prescribed support in the full batch graph.
In particular no code of another request can supply such
an edge, even when the requests have isomorphic supports. -/
theorem levelGraph_fresh_old_support
    (G : GraphOn U)
    (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (i : Fin r.code.1.val) (u : U)
    (h : (levelGraph G Allowed bound).adj
      (Sum.inr ⟨r, i⟩) (Sum.inl u)) :
    u ∈ r.support := by
  rcases h with ⟨a, b, ha, _, _⟩ |
    ⟨t, a, b, ha, hb, _⟩
  · cases ha
  · cases a with
    | inl p => cases ha
    | inr j =>
      cases b with
      | inr k => cases hb
      | inl p =>
        have htr : t = r :=
          congrArg Sigma.fst (Sum.inr.inj ha)
        subst t
        have hpu : p.val = u := Sum.inl.inj hb
        exact hpu ▸ p.property

/-- The same boundary condition with the old endpoint written
first, using symmetry of the constructed simple graph. -/
theorem levelGraph_old_fresh_support
    (G : GraphOn U)
    (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (i : Fin r.code.1.val) (u : U)
    (h : (levelGraph G Allowed bound).adj
      (Sum.inl u) (Sum.inr ⟨r, i⟩)) :
    u ∈ r.support := by
  have hSwap := (levelGraph G Allowed bound).symm
    (Sum.inl u) (Sum.inr ⟨r, i⟩) h
  exact levelGraph_fresh_old_support G Allowed bound r i u hSwap

end CFStageCatalogue
end BigHrushovski
