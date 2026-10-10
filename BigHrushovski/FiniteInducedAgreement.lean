import BigHrushovski.InfiniteGraph

/-!
# Predimension and strongness depend only on the induced finite graph

Two ambient graph predicates may disagree outside a finite vertex set.
Exact agreement of edges and nonedges on that set nevertheless gives the
same induced edge set, predimension, and relative self-sufficiency.

This is the finite-view transfer needed to prove that a coherent
countable union has the expected strong successor steps.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V]
variable (G H : GraphOn V)

/-- Exact adjacency agreement on a finite set preserves every unordered
edge, independently of graph behavior outside that set. -/
theorem edgesWithin_eq_of_agreeOn
    (s : Finset V)
    (hAgree : ∀ x ∈ s, ∀ y ∈ s, G.adj x y ↔ H.adj x y) :
    G.edgesWithin s = H.edgesWithin s := by
  ext e
  constructor
  · intro he
    obtain ⟨hsub, ⟨hc, x, hx, y, hy, hxy⟩⟩ :=
      (G.mem_edgesWithin_iff s e).mp he
    have hH : H.adj x y :=
      (hAgree x (hsub hx) y (hsub hy)).mp hxy
    exact (H.mem_edgesWithin_iff s e).mpr
      ⟨hsub, ⟨hc, x, hx, y, hy, hH⟩⟩
  · intro he
    obtain ⟨hsub, ⟨hc, x, hx, y, hy, hxy⟩⟩ :=
      (H.mem_edgesWithin_iff s e).mp he
    have hG : G.adj x y :=
      (hAgree x (hsub hx) y (hsub hy)).mpr hxy
    exact (G.mem_edgesWithin_iff s e).mpr
      ⟨hsub, ⟨hc, x, hx, y, hy, hG⟩⟩

/-- Graph predimension on a finite set is independent of all edges
outside that set. -/
theorem predim_eq_of_agreeOn
    (s : Finset V)
    (hAgree : ∀ x ∈ s, ∀ y ∈ s, G.adj x y ↔ H.adj x y) :
    G.predim s = H.predim s := by
  unfold predim
  rw [G.edgesWithin_eq_of_agreeOn H s hAgree]

/-- Relative strongness of A inside B is invariant under exact induced
adjacency agreement on B. No graph equality outside B is assumed. -/
theorem isStrong_iff_of_agreeOn
    (a b : Finset V) (hab : a ⊆ b)
    (hAgree : ∀ x ∈ b, ∀ y ∈ b, G.adj x y ↔ H.adj x y) :
    G.toPredimension.IsStrong a b ↔
      H.toPredimension.IsStrong a b := by
  have hDelta : ∀ s : Finset V, s ⊆ b →
      G.predim s = H.predim s := by
    intro s hs
    exact G.predim_eq_of_agreeOn H s
      (by
        intro x hx y hy
        exact hAgree x (hs hx) y (hs hy))
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro c hac hcb
    have hh := h.2 c hac hcb
    change G.predim a ≤ G.predim c at hh
    change H.predim a ≤ H.predim c
    rw [← hDelta a hab, ← hDelta c hcb]
    exact hh
  · intro h
    refine ⟨h.1, ?_⟩
    intro c hac hcb
    have hh := h.2 c hac hcb
    change H.predim a ≤ H.predim c at hh
    change G.predim a ≤ G.predim c
    rw [hDelta a hab, hDelta c hcb]
    exact hh

end GraphOn
end BigHrushovski
