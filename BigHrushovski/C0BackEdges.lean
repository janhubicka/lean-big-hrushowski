import BigHrushovski.GlobalClosure

/-!
# Back edges in one closure component of the 2-sparse graph

Manuscript: Proposition twoedges in Section 3.1.

The edges are unordered two-element sets. The incident-edge count is
exactly the number of edges from a fresh vertex to a finite old prefix.
No orientation or ordering of vertices is used.

The formal assertions require only that the prefix is globally strong;
the proof of the 2-edge bound does not need the full C0 sparsity
restriction on every induced subgraph.
-/

namespace BigHrushovski
namespace FiniteGraph

variable {V : Type*} [DecidableEq V] (G : FiniteGraph V)

/-- Edges from a fresh vertex x into the old set a. -/
def backEdges (a : Finset V) (x : V) : Finset (Finset V) :=
  (G.edgesWithin (insert x a)).filter (fun edge => x ∈ edge)

/-- The old and incident edges partition the edges within a ∪ {x}. -/
theorem edgesWithin_insert_split (a : Finset V) (x : V) :
    G.edgesWithin (insert x a) =
      G.edgesWithin a ∪ G.backEdges a x := by
  ext edge
  simp only [edgesWithin, backEdges, Finset.mem_filter, Finset.mem_union]
  constructor
  · intro h
    by_cases hx : x ∈ edge
    · exact Or.inr ⟨h, hx⟩
    · left
      refine ⟨h.1, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp (h.2 hv) with heq | hmem
      · subst v
        exact (hx hv).elim
      · exact hmem
  · rintro (h | h)
    · refine ⟨h.1, ?_⟩
      intro v hv
      exact Finset.mem_insert_of_mem (h.2 hv)
    · exact h.1

theorem backEdges_disjoint (a : Finset V) (x : V) (hx : x ∉ a) :
    Disjoint (G.edgesWithin a) (G.backEdges a x) := by
  apply Finset.disjoint_left.mpr
  intro edge hOld hBack
  have hsub : edge ⊆ a := (Finset.mem_filter.mp hOld).2
  have hmem : x ∈ edge := (Finset.mem_filter.mp hBack).2
  exact hx (hsub hmem)

/-- The exact edge-count increment when x is not in a. -/
theorem edge_count_insert (a : Finset V) (x : V) (hx : x ∉ a) :
    (G.edgesWithin (insert x a)).card =
      (G.edgesWithin a).card + (G.backEdges a x).card := by
  have hcard :=
    Finset.card_union_add_card_inter (G.edgesWithin a) (G.backEdges a x)
  have hzero : G.edgesWithin a ∩ G.backEdges a x = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (G.backEdges_disjoint a x hx)
  rw [hzero] at hcard
  simp only [Finset.card_empty, add_zero] at hcard
  rw [G.edgesWithin_insert_split a x]
  omega

/-- The exact change of predimension after adjoining a fresh vertex. -/
theorem predim_insert (a : Finset V) (x : V) (hx : x ∉ a) :
    G.predim (insert x a) + ((G.backEdges a x).card : ℤ)
      = G.predim a + 2 := by
  have hverts : (insert x a).card = a.card + 1 := by simp [hx]
  have hedges := G.edge_count_insert a x hx
  unfold predim
  omega

/-- At most two edges go back from a fresh vertex to a strong old set. -/
theorem backEdges_card_le_two
    {a b : Finset V} {x : V}
    (hab : G.toPredimension.IsStrong a b)
    (hxB : x ∈ b) (hxA : x ∉ a) :
    (G.backEdges a x).card ≤ 2 := by
  have hAinsert : a ⊆ insert x a := by
    intro v hv
    exact Finset.mem_insert_of_mem hv
  have hInsertB : insert x a ⊆ b := by
    intro v hv
    rcases Finset.mem_insert.mp hv with heq | ha
    · subst v
      exact hxB
    · exact hab.1 ha
  have hdelta : G.predim a ≤ G.predim (insert x a) :=
    hab.2 (insert x a) hAinsert hInsertB
  have hformula := G.predim_insert a x hxA
  omega

/-- If the new vertex has exactly two old edges, adjoining it already
gives a strong substructure of the finite extension. -/
theorem strong_insert_of_two_backEdges
    {a b : Finset V} {x : V}
    (hab : G.toPredimension.IsStrong a b)
    (hxB : x ∈ b) (hxA : x ∉ a)
    (hTwo : (G.backEdges a x).card = 2) :
    G.toPredimension.IsStrong (insert x a) b := by
  have hDelta : G.predim (insert x a) = G.predim a := by
    have h := G.predim_insert a x hxA
    omega
  refine ⟨?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with heq | ha
    · subst v
      exact hxB
    · exact hab.1 ha
  · intro c hInsertC hCB
    change G.predim (insert x a) ≤ G.predim c
    rw [hDelta]
    apply hab.2 c
    · intro v hv
      exact hInsertC (Finset.mem_insert_of_mem hv)
    · exact hCB

/-- In a strong exhaustion, a vertex with two old edges generates no
additional vertices over the globally strong old prefix. -/
theorem closure_insert_of_two_backEdges
    (e : Predimension.StrongExhaustion G.toPredimension)
    {a : Finset V} {x : V}
    (ha : G.toPredimension.IsGloballyStrong a)
    (hxA : x ∉ a)
    (hTwo : (G.backEdges a x).card = 2) :
    e.closure (insert x a) = insert x a := by
  let b := e.closure (insert x a)
  have hXb : x ∈ b :=
    e.subset_closure (insert x a) (Finset.mem_insert_self x a)
  have hAb : a ⊆ b := by
    intro v hv
    exact e.subset_closure (insert x a) (Finset.mem_insert_of_mem hv)
  have hStrong : G.toPredimension.IsStrong a b := ha b hAb
  have hOne : G.toPredimension.IsStrong (insert x a) b :=
    G.strong_insert_of_two_backEdges hStrong hXb hxA hTwo
  have hGlobal : G.toPredimension.IsGloballyStrong (insert x a) :=
    G.toPredimension.globallyStrong_of_strong_in_global hOne
      (e.closure_global (insert x a))
  exact e.closure_eq_self_of_global hGlobal

end FiniteGraph
end BigHrushovski
