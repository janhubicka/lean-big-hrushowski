import BigHrushovski.CFBatchInducedOld
import BigHrushovski.CFDClosedTransport

/-!
# Every normalized local C_F type is induced in the finite tagged batch

The batch graph contains exactly the specified complete graph on
each named support together with that request's own fresh block.
This includes *reflection of nonedges*, not merely the presence
of positive local edges. The key observation is that any graph
edge incident to a fresh vertex of request r must be contributed
by the same request r, because only that local inclusion can
have an endpoint with the corresponding fresh tag.

Together with the previously proved induced equality on old
vertices, this establishes full inducedness of every local
code. It also transfers the minimal strict d-closed step into
the finite image interval of the batch graph.

This does not yet prove that the old stage is d-closed in
the *whole batch*, or membership in the growth-function class C_F.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A local code that contributes an edge to a fresh vertex
tagged by r must itself have request index r. -/
theorem localTag_fresh_forces_request
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : Requests G Allowed bound)
    (i : Fin r.code.1.val)
    (a : Sum (SupportCarrier U s.support) (Fin s.code.1.val))
    (h : localTag G Allowed bound s a =
      (Sum.inr ⟨r, i⟩ : LevelCarrier G Allowed bound)) :
    s = r := by
  cases a with
  | inl p => cases h
  | inr j =>
    exact congrArg Sigma.fst (Sum.inr.inj h)

/-- If one endpoint of an edge is a fresh vertex of request r,
the entire edge originates in the complete local graph of r.
The second endpoint may be old or fresh. -/
theorem levelGraph_edge_from_fresh
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (i : Fin r.code.1.val)
    (y : LevelCarrier G Allowed bound)
    (h : (levelGraph G Allowed bound).adj (Sum.inr ⟨r, i⟩) y) :
    ∃ (a b : Sum (SupportCarrier U r.support) (Fin r.code.1.val)),
      localTag G Allowed bound r a = (Sum.inr ⟨r,i⟩) ∧
      localTag G Allowed bound r b = y ∧
      r.code.2.graph.adj a b := by
  rcases h with ⟨a, b, ha, _, _⟩ |
    ⟨s, a, b, ha, hb, hab⟩
  · cases ha
  · have hsr : s = r :=
      localTag_fresh_forces_request G Allowed bound r s i a ha
    subst s
    exact ⟨a, b, ha, hb, hab⟩

/-- For each request, the copied local graph is an induced
subgraph of the actual tagged simultaneous batch graph,
on the *complete* set of local old and fresh vertices. -/
theorem levelGraph_local_adj_iff
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (a b : Sum (SupportCarrier U r.support) (Fin r.code.1.val)) :
    (levelGraph G Allowed bound).adj
        (localTag G Allowed bound r a)
        (localTag G Allowed bound r b) ↔
      r.code.2.graph.adj a b := by
  constructor
  · intro h
    cases a with
    | inl p =>
      cases b with
      | inl q =>
        have hOld : G.adj p.val q.val :=
          (levelGraph_old_iff G Allowed bound p.val q.val).mp h
        exact (r.code.2.base_agrees p q).mpr hOld
      | inr j =>
        have hSwap : (levelGraph G Allowed bound).adj
            (localTag G Allowed bound r (Sum.inr j))
            (localTag G Allowed bound r (Sum.inl p)) :=
          (levelGraph G Allowed bound).symm _ _ h
        obtain ⟨u, v, hu, hv, hCode⟩ :=
          levelGraph_edge_from_fresh G Allowed bound r j
            (localTag G Allowed bound r (Sum.inl p)) hSwap
        have huEq : u = Sum.inr j :=
          (localTag_injective G Allowed bound r) hu
        have hvEq : v = Sum.inl p :=
          (localTag_injective G Allowed bound r) hv
        have hCode' : r.code.2.graph.adj (Sum.inr j) (Sum.inl p) := by
          simpa only [huEq, hvEq] using hCode
        exact r.code.2.graph.symm _ _ hCode'
    | inr i =>
      obtain ⟨u, v, hu, hv, hCode⟩ :=
        levelGraph_edge_from_fresh G Allowed bound r i
          (localTag G Allowed bound r b) h
      have huEq : u = Sum.inr i :=
        (localTag_injective G Allowed bound r) hu
      have hvEq : v = b :=
        (localTag_injective G Allowed bound r) hv
      simpa only [huEq, hvEq] using hCode
  · exact levelGraph_local_edge G Allowed bound r a b

/-- Every local code's minimal strict d-closed inclusion is
preserved in its induced copy inside the batch. This is a
*relative finite* statement; the base is not thereby shown
d-closed in the entire simultaneous carrier. -/
theorem levelGraph_local_minimal_image
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    (levelGraph G Allowed bound).toPredimension.IsMinimalDClosedStep
      ((CFLocalCatalogue.oldVertices
          (SupportCarrier U r.support) r.code.1.val).image
        (localTag G Allowed bound r))
      ((Finset.univ : Finset
          (Sum (SupportCarrier U r.support) (Fin r.code.1.val))).image
        (localTag G Allowed bound r)) := by
  classical
  exact (r.code.2.graph.minimalDClosedStep_image_iff
    (levelGraph G Allowed bound)
    (localTag G Allowed bound r)
    (localTag_injective G Allowed bound r)
    (fun u v => (levelGraph_local_adj_iff G Allowed bound r u v).symm)
    (CFLocalCatalogue.oldVertices
      (SupportCarrier U r.support) r.code.1.val)
    Finset.univ (Finset.subset_univ _)).mpr r.code.2.minimal

end CFStageCatalogue
end BigHrushovski
