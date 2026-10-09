import BigHrushovski.C0Sparsity

/-!
# The free join of finite induced graph pieces on a common vertex carrier

Two graphs may have a shared finite base.  When their adjacency relations
agree on that base, the free join retains both induced pieces and introduces
no edge between the two disjoint tails. This is an *actual graph construction*
on a common ambient vertex type, not merely an analysis of an existing union.

The later extension to arbitrary embeddings (renaming disjoint tails and
identifying the base) is recorded as a separate interface obligation.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Two graphs agree on the edges of a fixed induced vertex set. -/
def AgreeOn (H : GraphOn V) (p : Finset V) : Prop :=
  ∀ x ∈ p, ∀ y ∈ p, G.adj x y ↔ H.adj x y

/-- Free join of the induced graph on a with the induced graph on b.
All edges outside the union are discarded. -/
def freeJoin (H : GraphOn V) (a b : Finset V) : GraphOn V where
  adj x y :=
    (x ∈ a ∧ y ∈ a ∧ G.adj x y) ∨
    (x ∈ b ∧ y ∈ b ∧ H.adj x y)
  symm := by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨h.2.1, h.1, G.symm x y h.2.2⟩
    · exact Or.inr ⟨h.2.1, h.1, H.symm x y h.2.2⟩
  irrefl := by
    intro x h
    rcases h with h | h
    · exact G.irrefl x h.2.2
    · exact H.irrefl x h.2.2

/-- Restriction of the free join to the left factor is exactly G. -/
theorem freeJoin_adj_left (H : GraphOn V) (a b : Finset V)
    (hAgree : G.AgreeOn H (a ∩ b))
    {x y : V} (hx : x ∈ a) (hy : y ∈ a) :
    (G.freeJoin H a b).adj x y ↔ G.adj x y := by
  constructor
  · intro h
    change (x ∈ a ∧ y ∈ a ∧ G.adj x y) ∨
      (x ∈ b ∧ y ∈ b ∧ H.adj x y) at h
    rcases h with h | h
    · exact h.2.2
    · exact (hAgree x (Finset.mem_inter.mpr ⟨hx, h.1⟩)
        y (Finset.mem_inter.mpr ⟨hy, h.2.1⟩)).mpr h.2.2
  · intro h
    exact Or.inl ⟨hx, hy, h⟩

/-- Restriction of the free join to the right factor is exactly H. -/
theorem freeJoin_adj_right (H : GraphOn V) (a b : Finset V)
    (hAgree : G.AgreeOn H (a ∩ b))
    {x y : V} (hx : x ∈ b) (hy : y ∈ b) :
    (G.freeJoin H a b).adj x y ↔ H.adj x y := by
  constructor
  · intro h
    change (x ∈ a ∧ y ∈ a ∧ G.adj x y) ∨
      (x ∈ b ∧ y ∈ b ∧ H.adj x y) at h
    rcases h with h | h
    · exact (hAgree x (Finset.mem_inter.mpr ⟨h.1, hx⟩)
        y (Finset.mem_inter.mpr ⟨h.2.1, hy⟩)).mp h.2.2
    · exact h.2.2
  · intro h
    exact Or.inr ⟨hx, hy, h⟩

/-- Every induced edge of the join on a subset of the left factor
is exactly an induced edge of G. -/
theorem freeJoin_edgesWithin_left (H : GraphOn V) (a b s : Finset V)
    (hAgree : G.AgreeOn H (a ∩ b)) (hs : s ⊆ a) :
    (G.freeJoin H a b).edgesWithin s = G.edgesWithin s := by
  ext e
  rw [(G.freeJoin H a b).mem_edgesWithin_iff,
      G.mem_edgesWithin_iff]
  constructor
  · rintro ⟨heSub, hCard, x, hx, y, hy, hAdj⟩
    refine ⟨heSub, hCard, x, hx, y, hy, ?_⟩
    exact (G.freeJoin_adj_left H a b hAgree (hs (heSub hx))
      (hs (heSub hy))).mp hAdj
  · rintro ⟨heSub, hCard, x, hx, y, hy, hAdj⟩
    refine ⟨heSub, hCard, x, hx, y, hy, ?_⟩
    exact (G.freeJoin_adj_left H a b hAgree (hs (heSub hx))
      (hs (heSub hy))).mpr hAdj

/-- Right induced edge counts are preserved exactly as well. -/
theorem freeJoin_edgesWithin_right (H : GraphOn V) (a b s : Finset V)
    (hAgree : G.AgreeOn H (a ∩ b)) (hs : s ⊆ b) :
    (G.freeJoin H a b).edgesWithin s = H.edgesWithin s := by
  ext e
  rw [(G.freeJoin H a b).mem_edgesWithin_iff,
      H.mem_edgesWithin_iff]
  constructor
  · rintro ⟨heSub, hCard, x, hx, y, hy, hAdj⟩
    refine ⟨heSub, hCard, x, hx, y, hy, ?_⟩
    exact (G.freeJoin_adj_right H a b hAgree (hs (heSub hx))
      (hs (heSub hy))).mp hAdj
  · rintro ⟨heSub, hCard, x, hx, y, hy, hAdj⟩
    refine ⟨heSub, hCard, x, hx, y, hy, ?_⟩
    exact (G.freeJoin_adj_right H a b hAgree (hs (heSub hx))
      (hs (heSub hy))).mpr hAdj

/-- The free join introduces no edge between the disjoint tails. -/
theorem freeJoin_noCross (H : GraphOn V) (a b : Finset V) :
    (G.freeJoin H a b).NoCrossEdges a b := by
  intro e he
  obtain ⟨_, hCard, x, hx, y, hy, hAdj⟩ :=
    ((G.freeJoin H a b).mem_edgesWithin_iff (a ∪ b) e).mp he
  have hAdjSave := hAdj
  have hxy : x ≠ y := by
    intro hEq
    subst y
    exact (G.freeJoin H a b).irrefl x hAdj
  have hPairCard : (insert x ({y} : Finset V)).card = 2 := by
    simp [hxy]
  have hPairSub : insert x ({y} : Finset V) ⊆ e := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hVX | hVY
    · subst v
      exact hx
    · have hEq : v = y := Finset.mem_singleton.mp hVY
      subst v
      exact hy
  have hPairEq : e = insert x ({y} : Finset V) := by
    have hEq := Finset.eq_of_subset_of_card_le hPairSub (by omega)
    exact hEq.symm
  change (x ∈ a ∧ y ∈ a ∧ G.adj x y) ∨
    (x ∈ b ∧ y ∈ b ∧ H.adj x y) at hAdj
  rcases hAdj with hLeft | hRight
  · have heA : e ⊆ a := by
      rw [hPairEq]
      intro v hv
      rcases Finset.mem_insert.mp hv with hvX | hvY
      · subst v
        exact hLeft.1
      · have hvEq : v = y := Finset.mem_singleton.mp hvY
        subst v
        exact hLeft.2.1
    exact Finset.mem_union.mpr (Or.inl
      ((G.freeJoin H a b).mem_edgesWithin_iff a e).mpr
        ⟨heA, hCard, x, hx, y, hy, hAdjSave⟩)
  · have heB : e ⊆ b := by
      rw [hPairEq]
      intro v hv
      rcases Finset.mem_insert.mp hv with hvX | hvY
      · subst v
        exact hRight.1
      · have hvEq : v = y := Finset.mem_singleton.mp hvY
        subst v
        exact hRight.2.1
    exact Finset.mem_union.mpr (Or.inr
      ((G.freeJoin H a b).mem_edgesWithin_iff b e).mpr
        ⟨heB, hCard, x, hx, y, hy, hAdjSave⟩)

/-- Predimension of an induced left part is preserved by the free join. -/
theorem freeJoin_predim_left (H : GraphOn V) (a b s : Finset V)
    (hAgree : G.AgreeOn H (a ∩ b)) (hs : s ⊆ a) :
    (G.freeJoin H a b).predim s = G.predim s := by
  unfold predim
  rw [G.freeJoin_edgesWithin_left H a b s hAgree hs]

/-- Predimension of an induced right part is preserved by the free join. -/
theorem freeJoin_predim_right (H : GraphOn V) (a b s : Finset V)
    (hAgree : G.AgreeOn H (a ∩ b)) (hs : s ⊆ b) :
    (G.freeJoin H a b).predim s = H.predim s := by
  unfold predim
  rw [G.freeJoin_edgesWithin_right H a b s hAgree hs]

end GraphOn
end BigHrushovski
