import BigHrushovski.C0BackEdges

/-!
# Predimension for graphs with potentially infinitely many edges

A graph on a possibly infinite domain is given by a symmetric irreflexive
adjacency predicate. For each finite set, its induced edge set is finite;
there is no global finiteness assumption on the edge relation.

The induced predimension is submodular and agrees, on every finite induced
subgraph, with the previously checked FiniteGraph predimension.
-/

namespace BigHrushovski

structure GraphOn (V : Type*) where
  adj : V → V → Prop
  symm : ∀ x y : V, adj x y → adj y x
  irrefl : ∀ x : V, ¬ adj x x

namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- An unordered finite pair of adjacent vertices. -/
def IsEdge (e : Finset V) : Prop :=
  e.card = 2 ∧ ∃ x ∈ e, ∃ y ∈ e, G.adj x y

/-- The finite set of edges contained in a finite vertex set. -/
noncomputable def edgesWithin (s : Finset V) : Finset (Finset V) := by
  classical
  exact s.powerset.filter G.IsEdge

theorem mem_edgesWithin_iff (s e : Finset V) :
    e ∈ G.edgesWithin s ↔ e ⊆ s ∧ G.IsEdge e := by
  classical
  constructor
  · intro he
    obtain ⟨hs, hEdge⟩ := Finset.mem_filter.mp he
    exact ⟨Finset.mem_powerset.mp hs, hEdge⟩
  · rintro ⟨hs, hEdge⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs, hEdge⟩

theorem edgesWithin_union_subset (a b : Finset V) :
    G.edgesWithin a ∪ G.edgesWithin b ⊆ G.edgesWithin (a ∪ b) := by
  intro e he
  rcases Finset.mem_union.mp he with ha | hb
  · rcases (G.mem_edgesWithin_iff a e).mp ha with ⟨hes, hEdge⟩
    exact (G.mem_edgesWithin_iff (a ∪ b) e).mpr
      ⟨hes.trans Finset.subset_union_left, hEdge⟩
  · rcases (G.mem_edgesWithin_iff b e).mp hb with ⟨hes, hEdge⟩
    exact (G.mem_edgesWithin_iff (a ∪ b) e).mpr
      ⟨hes.trans Finset.subset_union_right, hEdge⟩

theorem edgesWithin_inter (a b : Finset V) :
    G.edgesWithin (a ∩ b) =
      G.edgesWithin a ∩ G.edgesWithin b := by
  ext e
  constructor
  · intro he
    rcases (G.mem_edgesWithin_iff (a ∩ b) e).mp he with ⟨hes, hEdge⟩
    apply Finset.mem_inter.mpr
    constructor
    · exact (G.mem_edgesWithin_iff a e).mpr
        ⟨hes.trans Finset.inter_subset_left, hEdge⟩
    · exact (G.mem_edgesWithin_iff b e).mpr
        ⟨hes.trans Finset.inter_subset_right, hEdge⟩
  · intro he
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp he
    rcases (G.mem_edgesWithin_iff a e).mp ha with ⟨haS, hEdge⟩
    rcases (G.mem_edgesWithin_iff b e).mp hb with ⟨hbS, _⟩
    refine (G.mem_edgesWithin_iff (a ∩ b) e).mpr ⟨?_, hEdge⟩
    intro v hv
    exact Finset.mem_inter.mpr ⟨haS hv, hbS hv⟩

/-- Edge counts are supermodular, including crossing edges. -/
theorem edgeCount_supermodular (a b : Finset V) :
    (G.edgesWithin a).card + (G.edgesWithin b).card ≤
      (G.edgesWithin (a ∪ b)).card +
        (G.edgesWithin (a ∩ b)).card := by
  have hcard := Finset.card_le_card (G.edgesWithin_union_subset a b)
  have hIE :=
    Finset.card_union_add_card_inter (G.edgesWithin a) (G.edgesWithin b)
  rw [G.edgesWithin_inter a b]
  omega

/-- The predimension of a finite set in an arbitrary graph. -/
noncomputable def predim (s : Finset V) : ℤ :=
  2 * (s.card : ℤ) - ((G.edgesWithin s).card : ℤ)

theorem predim_submodular (a b : Finset V) :
    G.predim (a ∪ b) + G.predim (a ∩ b) ≤
      G.predim a + G.predim b := by
  have hverts := Finset.card_union_add_card_inter a b
  have hedges := G.edgeCount_supermodular a b
  unfold predim
  omega

/-- The predimension structure defined on all finite subsets of the domain. -/
noncomputable def toPredimension : Predimension V where
  delta := G.predim
  submodular := G.predim_submodular

/-- A finite induced graph, represented in the earlier finite-edge format. -/
noncomputable def finiteView (s : Finset V) : FiniteGraph V where
  edges := G.edgesWithin s
  edges_pair := by
    intro e he
    exact ((G.mem_edgesWithin_iff s e).mp he).2.1

/-- The finite view has precisely the same edges on any subset of its
chosen finite vertex container. -/
theorem finiteView_edgesWithin (s t : Finset V) (ht : t ⊆ s) :
    (G.finiteView s).edgesWithin t = G.edgesWithin t := by
  ext e
  change e ∈ (G.edgesWithin s).filter (fun edge => edge ⊆ t) ↔
    e ∈ G.edgesWithin t
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨he, heT⟩
    exact (G.mem_edgesWithin_iff t e).mpr
      ⟨heT, ((G.mem_edgesWithin_iff s e).mp he).2⟩
  · intro he
    rcases (G.mem_edgesWithin_iff t e).mp he with ⟨heT, hEdge⟩
    exact ⟨(G.mem_edgesWithin_iff s e).mpr
      ⟨heT.trans ht, hEdge⟩, heT⟩

/-- Predimension agrees exactly between an arbitrary graph and its
finite induced view. -/
theorem predim_finiteView (s t : Finset V) (ht : t ⊆ s) :
    (G.finiteView s).predim t = G.predim t := by
  unfold FiniteGraph.predim predim
  rw [G.finiteView_edgesWithin s t ht]


/-- Finite strong embeddings are unchanged by taking a finite induced
view of the larger graph. -/
theorem isStrong_finiteView_iff (a b : Finset V) (hab : a ⊆ b) :
    (G.finiteView b).toPredimension.IsStrong a b ↔
      G.toPredimension.IsStrong a b := by
  constructor
  · intro h
    refine ⟨hab, ?_⟩
    intro c hac hcb
    have hh := h.2 c hac hcb
    change (G.finiteView b).predim a ≤ (G.finiteView b).predim c at hh
    rw [G.predim_finiteView b a hab, G.predim_finiteView b c hcb] at hh
    exact hh
  · intro h
    refine ⟨hab, ?_⟩
    intro c hac hcb
    have hh := h.2 c hac hcb
    change (G.finiteView b).predim a ≤ (G.finiteView b).predim c
    rw [G.predim_finiteView b a hab, G.predim_finiteView b c hcb]
    exact hh

/-- Edges incident to x inside the old set plus x, in a possibly infinite
ambient graph. -/
noncomputable def backEdges (a : Finset V) (x : V) :
    Finset (Finset V) :=
  (G.edgesWithin (insert x a)).filter (fun edge => x ∈ edge)

theorem finiteView_backEdges (s a : Finset V) (x : V)
    (hsub : insert x a ⊆ s) :
    (G.finiteView s).backEdges a x = G.backEdges a x := by
  unfold backEdges FiniteGraph.backEdges
  rw [G.finiteView_edgesWithin s (insert x a) hsub]

/-- At most two old incident edges in an arbitrary graph, not only in
a graph whose entire edge set is finite. -/
theorem backEdges_card_le_two {a b : Finset V} {x : V}
    (hab : G.toPredimension.IsStrong a b)
    (hxB : x ∈ b) (hxA : x ∉ a) :
    (G.backEdges a x).card ≤ 2 := by
  have hFinite : (G.finiteView b).toPredimension.IsStrong a b :=
    (G.isStrong_finiteView_iff a b hab.1).mpr hab
  have hInsertB : insert x a ⊆ b := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hEq | hA
    · subst v
      exact hxB
    · exact hab.1 hA
  have hBound :=
    (G.finiteView b).backEdges_card_le_two hFinite hxB hxA
  rw [G.finiteView_backEdges b a x hInsertB] at hBound
  exact hBound

/-- Two old incident edges make the added vertex already strongly closed,
even if the entire ambient graph has infinitely many edges. -/
theorem closure_insert_of_two_backEdges
    (e : Predimension.StrongExhaustion G.toPredimension)
    {a : Finset V} {x : V}
    (ha : G.toPredimension.IsGloballyStrong a)
    (hxA : x ∉ a)
    (hTwo : (G.backEdges a x).card = 2) :
    e.closure (insert x a) = insert x a := by
  let b := e.closure (insert x a)
  have hInsB : insert x a ⊆ b := e.subset_closure (insert x a)
  have hab : a ⊆ b := by
    intro v hv
    exact hInsB (Finset.mem_insert_of_mem hv)
  have hxB : x ∈ b :=
    hInsB (Finset.mem_insert_self x a)
  have hStrongA : G.toPredimension.IsStrong a b := ha b hab
  have hFiniteA : (G.finiteView b).toPredimension.IsStrong a b :=
    (G.isStrong_finiteView_iff a b hab).mpr hStrongA
  have hFiniteTwo : ((G.finiteView b).backEdges a x).card = 2 := by
    rw [G.finiteView_backEdges b a x hInsB]
    exact hTwo
  have hFiniteInsert : (G.finiteView b).toPredimension.IsStrong
      (insert x a) b :=
    (G.finiteView b).strong_insert_of_two_backEdges
      hFiniteA hxB hxA hFiniteTwo
  have hStrongInsert : G.toPredimension.IsStrong (insert x a) b :=
    (G.isStrong_finiteView_iff (insert x a) b hInsB).mp hFiniteInsert
  have hGlob : G.toPredimension.IsGloballyStrong (insert x a) :=
    G.toPredimension.globallyStrong_of_strong_in_global
      hStrongInsert (e.closure_global (insert x a))
  exact e.closure_eq_self_of_global hGlob

end GraphOn
end BigHrushovski
