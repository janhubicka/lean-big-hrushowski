import BigHrushovski.InfiniteGraph

/-!
# Back edges and old neighbours in a simple graph

For a fresh vertex x and a finite old prefix A, the back edges incident
to x correspond bijectively to vertices of A adjacent to x. This closes
the numerical interface between the manuscript's d_i(x) and the
unordered-edge count in C0BackEdges/InfiniteGraph.

The ambient graph may have infinitely many vertices and edges.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- The set of old neighbours of x within the finite vertex set a. -/
noncomputable def oldNeighbours (a : Finset V) (x : V) : Finset V := by
  classical
  exact a.filter (fun y => G.adj x y)

theorem mem_oldNeighbours_iff (a : Finset V) (x y : V) :
    y ∈ G.oldNeighbours a x ↔ y ∈ a ∧ G.adj x y := by
  classical
  simp [oldNeighbours]

/-- One old neighbour gives the corresponding unordered incident edge. -/
theorem pair_mem_backEdges
    (a : Finset V) (x : V) (hx : x ∉ a)
    {y : V} (hy : y ∈ G.oldNeighbours a x) :
    (insert x ({y} : Finset V)) ∈ G.backEdges a x := by
  classical
  have hya : y ∈ a := (G.mem_oldNeighbours_iff a x y).mp hy |>.1
  have hadj : G.adj x y := (G.mem_oldNeighbours_iff a x y).mp hy |>.2
  have hne : x ≠ y := by
    intro h
    subst y
    exact hx hya
  have hpair : (insert x ({y} : Finset V)).card = 2 := by
    simp [hne]
  have hsub : (insert x ({y} : Finset V)) ⊆ insert x a := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzx | hzy
    · subst z
      exact Finset.mem_insert_self x a
    · have heq : z = y := Finset.mem_singleton.mp hzy
      subst z
      exact Finset.mem_insert_of_mem hya
  have he : G.IsEdge (insert x ({y} : Finset V)) := by
    refine ⟨hpair, x, Finset.mem_insert_self x _, y, ?_, hadj⟩
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  have hwithin :
      insert x ({y} : Finset V) ∈ G.edgesWithin (insert x a) :=
    (G.mem_edgesWithin_iff _ _).mpr ⟨hsub, he⟩
  exact Finset.mem_filter.mpr ⟨hwithin, Finset.mem_insert_self x _⟩

/-- An unordered edge incident to x has a unique other endpoint,
which is an old neighbour when the edge lies in a ∪ {x}. -/
theorem backEdge_exists_oldNeighbour
    (a : Finset V) (x : V) (hx : x ∉ a)
    {edge : Finset V} (he : edge ∈ G.backEdges a x) :
    ∃ y : V, y ∈ G.oldNeighbours a x ∧
      edge = insert x ({y} : Finset V) := by
  classical
  rcases Finset.mem_filter.mp he with ⟨hWithin, hxEdge⟩
  rcases (G.mem_edgesWithin_iff (insert x a) edge).mp hWithin with
    ⟨hsub, hEdge⟩
  rcases hEdge with ⟨hcard, p, hp, q, hq, hpqAdj⟩
  have hpneq : p ≠ q := by
    intro hpq
    subst q
    exact (G.irrefl p) hpqAdj
  have hPairSub : (insert p ({q} : Finset V)) ⊆ edge := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzp | hzq
    · subst z
      exact hp
    · have hzEq : z = q := Finset.mem_singleton.mp hzq
      subst z
      exact hq
  have hPairCard : (insert p ({q} : Finset V)).card = 2 := by
    simp [hpneq]
  have hPairEq : edge = insert p ({q} : Finset V) := by
    have hh : (insert p ({q} : Finset V)) = edge :=
      Finset.eq_of_subset_of_card_le hPairSub (by omega)
    exact hh.symm
  have hxChoice : x = p ∨ x = q := by
    have hxPair : x ∈ insert p ({q} : Finset V) := by
      rw [← hPairEq]
      exact hxEdge
    rcases Finset.mem_insert.mp hxPair with hxp | hxq
    · exact Or.inl hxp
    · exact Or.inr (Finset.mem_singleton.mp hxq)
  rcases hxChoice with hxp | hxq
  · subst p
    have hqOld : q ∈ a := by
      rcases Finset.mem_insert.mp (hsub hq) with hqx | hqa
      · exact (hpneq hqx.symm).elim
      · exact hqa
    refine ⟨q, (G.mem_oldNeighbours_iff a x q).mpr
      ⟨hqOld, hpqAdj⟩, hPairEq⟩
  · subst q
    have hpOld : p ∈ a := by
      rcases Finset.mem_insert.mp (hsub hp) with hpx | hpa
      · exact (hpneq hpx).elim
      · exact hpa
    refine ⟨p, (G.mem_oldNeighbours_iff a x p).mpr
      ⟨hpOld, G.symm p x hpqAdj⟩, ?_⟩
    ext z
    simp only [hPairEq, Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Every incident back edge is the image of its old neighbour. -/
theorem backEdges_eq_neighbour_image
    (a : Finset V) (x : V) (hx : x ∉ a) :
    G.backEdges a x =
      (G.oldNeighbours a x).image
        (fun y => insert x ({y} : Finset V)) := by
  classical
  ext edge
  constructor
  · intro he
    obtain ⟨y, hy, heq⟩ :=
      G.backEdge_exists_oldNeighbour a x hx he
    exact Finset.mem_image.mpr ⟨y, hy, heq.symm⟩
  · intro he
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp he
    rw [← heq]
    exact G.pair_mem_backEdges a x hx hy

/-- The neighbour-to-edge map is injective on old neighbours. -/
theorem neighbour_pair_injOn
    (a : Finset V) (x : V) (hx : x ∉ a) :
    Set.InjOn
      (fun y => insert x ({y} : Finset V))
      (G.oldNeighbours a x) := by
  classical
  intro u hu v hv heq
  have huA : u ∈ a := (G.mem_oldNeighbours_iff a x u).mp hu |>.1
  have hux : u ≠ x := by
    intro h
    subst u
    exact hx huA
  have heq' : insert x ({u} : Finset V) =
      insert x ({v} : Finset V) := heq
  have huSelf : u ∈ insert x ({u} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self u)
  have huIn : u ∈ insert x ({v} : Finset V) := heq' ▸ huSelf
  rcases Finset.mem_insert.mp huIn with hux' | huv
  · exact (hux hux').elim
  · exact Finset.mem_singleton.mp huv

/-- The manuscript's d_i(x) equals the unordered incident-edge count. -/
theorem backEdges_card_eq_oldNeighbours_card
    (a : Finset V) (x : V) (hx : x ∉ a) :
    (G.backEdges a x).card = (G.oldNeighbours a x).card := by
  classical
  rw [G.backEdges_eq_neighbour_image a x hx]
  exact Finset.card_image_of_injOn (G.neighbour_pair_injOn a x hx)

/-- At most two distinct old neighbours of a vertex outside a strong
finite prefix in any (possibly infinite) simple graph. -/
theorem oldNeighbours_card_le_two
    {a b : Finset V} {x : V}
    (hab : G.toPredimension.IsStrong a b)
    (hxB : x ∈ b) (hxA : x ∉ a) :
    (G.oldNeighbours a x).card ≤ 2 := by
  have hbound := G.backEdges_card_le_two hab hxB hxA
  rw [G.backEdges_card_eq_oldNeighbours_card a x hxA] at hbound
  exact hbound

/-- Exactly two old neighbours force a singleton generated increment. -/
theorem closure_insert_of_two_oldNeighbours
    (ex : Predimension.StrongExhaustion G.toPredimension)
    {a : Finset V} {x : V}
    (ha : G.toPredimension.IsGloballyStrong a)
    (hxA : x ∉ a)
    (hTwo : (G.oldNeighbours a x).card = 2) :
    ex.closure (insert x a) = insert x a := by
  apply G.closure_insert_of_two_backEdges ex ha hxA
  rw [G.backEdges_card_eq_oldNeighbours_card a x hxA]
  exact hTwo

end GraphOn
end BigHrushovski
