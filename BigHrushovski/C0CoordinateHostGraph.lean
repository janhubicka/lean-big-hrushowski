import BigHrushovski.C0UnaryEmbeddings

/-!
# Recovering the C₀ graph from one-generated unary data

Section 4 replaces the graph edge relation by the unary set value
J(v) = N(v) ∩ C(v). The crucial hypothesis is that every edge has
at least one endpoint in the other's unary closure.

This is a concrete part of the coordinate-host proof. It does not
construct the host, the return map, or any Ramsey statement.
Complete images of both values are required; inclusion is insufficient.
-/

namespace BigHrushovski

namespace GraphOn

variable {U : Type*} [DecidableEq U]

/-- The neighbours of a vertex in its full unary closure. -/
noncomputable def backAdjacencyValue (G : GraphOn U)
    (C : U → Finset U) (u : U) : Finset U := by
  classical
  exact (C u).filter (fun v => G.adj u v)

theorem mem_backAdjacencyValue_iff (G : GraphOn U)
    (C : U → Finset U) (u v : U) :
    v ∈ G.backAdjacencyValue C u ↔
      v ∈ C u ∧ G.adj u v := by
  classical
  simp [backAdjacencyValue]

/-- The exact graph-recovery identity; edge covering is necessary. -/
theorem adj_iff_backAdjacencyValue (G : GraphOn U)
    (C : U → Finset U)
    (hCover : ∀ u v : U, G.adj u v → v ∈ C u ∨ u ∈ C v)
    (u v : U) :
    G.adj u v ↔
      v ∈ G.backAdjacencyValue C u ∨
      u ∈ G.backAdjacencyValue C v := by
  constructor
  · intro hadj
    rcases hCover u v hadj with hCl | hCl
    · exact Or.inl ((G.mem_backAdjacencyValue_iff C u v).2 ⟨hCl, hadj⟩)
    · exact Or.inr ((G.mem_backAdjacencyValue_iff C v u).2
        ⟨hCl, G.symm u v hadj⟩)
  · rintro (h | h)
    · exact ((G.mem_backAdjacencyValue_iff C u v).1 h).2
    · exact G.symm v u ((G.mem_backAdjacencyValue_iff C v u).1 h).2

variable {V : Type*} [DecidableEq V]

/-- Induced graph maps preserving the full closure values also preserve
the entire J values. The resulting identity is not just an inclusion. -/
theorem backAdjacencyValue_image
    (G : GraphOn U) (H : GraphOn V)
    (C : U → Finset U) (D : V → Finset V)
    (f : U → V)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (f x) (f y))
    (hC : ∀ x : U, (C x).image f = D (f x))
    (u : U) :
    (G.backAdjacencyValue C u).image f =
      H.backAdjacencyValue D (f u) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hvC, hvAdj⟩ := (G.mem_backAdjacencyValue_iff C u v).mp hv
    exact (H.mem_backAdjacencyValue_iff D (f u) (f v)).mpr
      ⟨by rw [← hC u]; exact Finset.mem_image.mpr ⟨v, hvC, rfl⟩,
        (hAdj u v).mp hvAdj⟩
  · intro hz
    obtain ⟨hzC, hzAdj⟩ := (H.mem_backAdjacencyValue_iff D (f u) z).mp hz
    rw [← hC u] at hzC
    obtain ⟨v, hvC, hfv⟩ := Finset.mem_image.mp hzC
    refine Finset.mem_image.mpr ⟨v, ?_, hfv⟩
    apply (G.mem_backAdjacencyValue_iff C u v).mpr
    refine ⟨hvC, ?_⟩
    apply (hAdj u v).mpr
    simpa only [hfv] using hzAdj

/-- Full image preservation of J, plus injectivity and edge coverage
on both sides, recovers the induced graph relation. -/
theorem induced_of_backAdjacencyValue
    (G : GraphOn U) (H : GraphOn V)
    (C : U → Finset U) (D : V → Finset V)
    (f : U → V)
    (hf : Function.Injective f)
    (hCoverG : ∀ x y, G.adj x y → y ∈ C x ∨ x ∈ C y)
    (hCoverH : ∀ x y, H.adj x y → y ∈ D x ∨ x ∈ D y)
    (hJ : ∀ x : U,
      (G.backAdjacencyValue C x).image f =
        H.backAdjacencyValue D (f x)) :
    ∀ u v : U, G.adj u v ↔ H.adj (f u) (f v) := by
  have hMem (u v : U) :
      v ∈ G.backAdjacencyValue C u ↔
        f v ∈ H.backAdjacencyValue D (f u) := by
    constructor
    · intro h
      rw [← hJ u]
      exact Finset.mem_image.mpr ⟨v, h, rfl⟩
    · intro h
      rw [← hJ u] at h
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
      have hwv : w = v := hf heq
      simpa only [hwv] using hw
  intro u v
  rw [G.adj_iff_backAdjacencyValue C hCoverG u v,
      H.adj_iff_backAdjacencyValue D hCoverH (f u) (f v)]
  exact or_congr (hMem u v) (hMem v u)


/-- If two vertex sets are closed under complete unary values, there
are no graph edges between their exclusive parts. In particular their
induced graph union is the free amalgam over their intersection. -/
theorem noCrossEdges_of_closed
    (G : GraphOn U) (C : U → Finset U)
    (hCover : ∀ u v, G.adj u v → v ∈ C u ∨ u ∈ C v)
    (s t : Finset U)
    (hs : ∀ u ∈ s, C u ⊆ s)
    (ht : ∀ v ∈ t, C v ⊆ t)
    {u v : U}
    (hus : u ∈ s) (hut : u ∉ t)
    (hvt : v ∈ t) (hvs : v ∉ s) :
    ¬ G.adj u v := by
  intro hadj
  rcases hCover u v hadj with hCl | hCl
  · exact hvs (hs u hus hCl)
  · exact hut (ht v hvt hCl)

end GraphOn

namespace FiniteCatalogue

/-- For the actual C₀ minimal-strong enumeration, every edge is
covered by at least one complete unary value, including edges
inside a single component. -/
theorem genericC0_edge_covered (u v : ℕ)
    (hadj : genericTwoSparseGraph.adj u v) :
    v ∈ genericC0UnaryClosure u ∨
      u ∈ genericC0UnaryClosure v := by
  rcases lt_trichotomy (genericC0ComponentIndex u)
      (genericC0ComponentIndex v) with huv | heq | hvu
  · right
    have huOld :
        u ∈ genericC0MinimalStage (genericC0ComponentIndex v) :=
      (genericC0ComponentIndex_lt_iff_stage u
        (genericC0ComponentIndex v)).mp huv
    have hback :
        u ∈ genericTwoSparseGraph.oldNeighbours
          (genericC0MinimalStage (genericC0ComponentIndex v)) v :=
      (genericTwoSparseGraph.mem_oldNeighbours_iff _ v u).mpr
        ⟨huOld, genericTwoSparseGraph.symm u v hadj⟩
    exact genericC0UnaryClosure_oldNeighbour
      (genericC0UnaryClosure_self v) hback
  · left
    exact (mem_genericC0UnaryClosure_iff u v).mpr (by
      rw [← heq]
      exact GenericC0Ancestor.root)
  · left
    have hvOld :
        v ∈ genericC0MinimalStage (genericC0ComponentIndex u) :=
      (genericC0ComponentIndex_lt_iff_stage v
        (genericC0ComponentIndex u)).mp hvu
    have hback :
        v ∈ genericTwoSparseGraph.oldNeighbours
          (genericC0MinimalStage (genericC0ComponentIndex u)) u :=
      (genericTwoSparseGraph.mem_oldNeighbours_iff _ u v).mpr
        ⟨hvOld, hadj⟩
    exact genericC0UnaryClosure_oldNeighbour
      (genericC0UnaryClosure_self u) hback

/-- The full J value used at the beginning of manuscript §4. -/
noncomputable def genericC0BackAdjacency (u : ℕ) : Finset ℕ :=
  genericTwoSparseGraph.backAdjacencyValue genericC0UnaryClosure u

theorem mem_genericC0BackAdjacency_iff (u v : ℕ) :
    v ∈ genericC0BackAdjacency u ↔
      v ∈ genericC0UnaryClosure u ∧
        genericTwoSparseGraph.adj u v :=
  genericTwoSparseGraph.mem_backAdjacencyValue_iff
    genericC0UnaryClosure u v

/-- Exact concrete verification of E(u,v) iff v in J(u) or u in J(v). -/
theorem genericC0Graph_iff_backAdjacency (u v : ℕ) :
    genericTwoSparseGraph.adj u v ↔
      v ∈ genericC0BackAdjacency u ∨
      u ∈ genericC0BackAdjacency v :=
  genericTwoSparseGraph.adj_iff_backAdjacencyValue
    genericC0UnaryClosure genericC0_edge_covered u v

/-- An embedding expressed exclusively in the two unary values C,J. -/
def IsGenericC0CJEmbedding (f : ℕ → ℕ) : Prop :=
  Function.Injective f ∧
  (∀ u, (genericC0UnaryClosure u).image f =
    genericC0UnaryClosure (f u)) ∧
  (∀ u, (genericC0BackAdjacency u).image f =
    genericC0BackAdjacency (f u))

/-- The binary edge relation is eliminable without changing the
embeddings, provided C and J are preserved as complete set values. -/
theorem genericC0CJEmbedding_iff_unaryEmbedding (f : ℕ → ℕ) :
    IsGenericC0CJEmbedding f ↔ IsGenericC0UnaryEmbedding f := by
  constructor
  · rintro ⟨hf, hC, hJ⟩
    refine ⟨hf, ?_, hC⟩
    exact genericTwoSparseGraph.induced_of_backAdjacencyValue
      genericTwoSparseGraph genericC0UnaryClosure
      genericC0UnaryClosure f hf genericC0_edge_covered
      genericC0_edge_covered hJ
  · rintro ⟨hf, hAdj, hC⟩
    refine ⟨hf, hC, ?_⟩
    intro u
    exact genericTwoSparseGraph.backAdjacencyValue_image
      genericTwoSparseGraph genericC0UnaryClosure
      genericC0UnaryClosure f hAdj hC u


/-- The canonical C₀ unary presentation has no crossing edges
between the exclusive parts of two finite unary-closed sets.
This is the free-union observation used in the coordinate host. -/
theorem genericC0UnaryClosed_noCross
    (s t : Finset ℕ)
    (hs : IsGenericC0UnaryClosed s)
    (ht : IsGenericC0UnaryClosed t)
    {u v : ℕ}
    (hus : u ∈ s) (hut : u ∉ t)
    (hvt : v ∈ t) (hvs : v ∉ s) :
    ¬ genericTwoSparseGraph.adj u v :=
  genericTwoSparseGraph.noCrossEdges_of_closed
    genericC0UnaryClosure genericC0_edge_covered s t
    hs ht hus hut hvt hvs

end FiniteCatalogue
end BigHrushovski
