import BigHrushovski.C0CoordinateIntrinsicLocalOrder

/-!
# Choosing and transporting the internal order of a one-generated C₀ closure

The manuscript selects one ordered representative for each *local type
with its already ordered lower part*. This is a CHOICE of order, not a
consequence of chronology, nor a requirement that every automorphism
of the underlying unordered local structure preserve the chosen order.

Here a local representative has a complete graph, a complete finite
unary function C, reflexive and nested complete values, edge coverage,
a closed lower part P, and an order with P before
the whole top component B. Every member of B generates the full local
carrier. No top vertex or temporary construction generator is singled
out.

A bijection transports the selected order, graph, complete unary
values, and lower part to an occurrence. Two occurrences transported
from the SAME representative are canonically ordered-isomorphic,
independently of whether a particular automorphism of the raw
unordered representative preserves the chosen order.

The existence/coverage of a catalogue containing one representative
for every manuscript local type is a separate obligation. This file
does not construct the countable coordinate host W.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- One chosen ordered representative of a finite one-generated
closure type, with its already ordered lower part. A generator is
not part of the record; all vertices of the top component generate
the entire one-generated structure. -/
structure LocalOrderedRepresentative (U : Type*)
    [Fintype U] [DecidableEq U] [LinearOrder U] where
  graph : GraphOn U
  value : U → Finset U
  lower : Finset U
  value_reflexive : ∀ u : U, u ∈ value u
  value_nested : ∀ u v : U, v ∈ value u → value v ⊆ value u
  graph_edge_covered : ∀ u v : U, graph.adj u v →
    v ∈ value u ∨ u ∈ value v
  lower_closed : ClosedUnder value lower
  lower_before_top : ∀ p ∈ lower, ∀ b ∉ lower, p < b
  top_generates : ∀ b : U, b ∉ lower → value b = Finset.univ
  top_nonempty : (Finset.univ \ lower).Nonempty

variable {U V W : Type*}
variable [Fintype U] [DecidableEq U] [LinearOrder U]
variable [Fintype V] [DecidableEq V]
variable [Fintype W] [DecidableEq W]

/-- An occurrence of a fixed ordered local representative receives
the order transported by its chosen underlying finite bijection. -/
def LocalOrderedRepresentative.transportedLess
    (r : LocalOrderedRepresentative U) (e : U ≃ V) (v w : V) : Prop :=
  e.symm v < e.symm w

/-- The complete graph transported to the occurrence. -/
def LocalOrderedRepresentative.transportedGraph
    (r : LocalOrderedRepresentative U) (e : U ≃ V) : GraphOn V where
  adj v w := r.graph.adj (e.symm v) (e.symm w)
  symm v w h := r.graph.symm _ _ h
  irrefl v := r.graph.irrefl _

/-- The complete finite unary value transported to the occurrence. -/
noncomputable def LocalOrderedRepresentative.transportedValue
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (v : V) : Finset V :=
  (r.value (e.symm v)).image e

/-- The lower part is transported as a complete subset, not merely
as a set of cardinality equal to the old lower part. -/
noncomputable def LocalOrderedRepresentative.transportedLower
    (r : LocalOrderedRepresentative U) (e : U ≃ V) : Finset V :=
  r.lower.image e

/-- An equivalence transports finite-set membership exactly. -/
theorem equiv_image_mem_iff (e : U ≃ V) (s : Finset U) (v : V) :
    v ∈ s.image e ↔ e.symm v ∈ s := by
  classical
  constructor
  · intro h
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp h
    have hu' : u = e.symm v := by
      apply e.injective
      simpa only [e.apply_symm_apply] using heq
    simpa only [hu'] using hu
  · intro h
    exact Finset.mem_image.mpr
      ⟨e.symm v, h, e.apply_symm_apply v⟩

/-- The selected order is exactly reflected on each transported
occurrence. In particular it is a strict linear order. -/
@[simp] theorem LocalOrderedRepresentative.transportedLess_apply
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (u v : U) :
    r.transportedLess e (e u) (e v) ↔ u < v := by
  simp only [transportedLess, e.symm_apply_apply]

theorem LocalOrderedRepresentative.transportedLess_trans
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    {u v w : V}
    (huv : r.transportedLess e u v)
    (hvw : r.transportedLess e v w) :
    r.transportedLess e u w :=
  lt_trans huv hvw

theorem LocalOrderedRepresentative.transportedLess_total
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (v w : V) (hne : v ≠ w) :
    r.transportedLess e v w ∨ r.transportedLess e w v := by
  have hne' : e.symm v ≠ e.symm w := by
    intro h
    apply hne
    exact e.symm.injective h
  rcases lt_or_gt_of_ne hne' with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem LocalOrderedRepresentative.transportedGraph_iff
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (u v : U) :
    (r.transportedGraph e).adj (e u) (e v) ↔ r.graph.adj u v := by
  simp [transportedGraph]

theorem LocalOrderedRepresentative.transportedValue_mem_iff
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (v w : V) :
    w ∈ r.transportedValue e v ↔
      e.symm w ∈ r.value (e.symm v) := by
  classical
  exact equiv_image_mem_iff e (r.value (e.symm v)) w

theorem LocalOrderedRepresentative.transportedLower_mem_iff
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (v : V) :
    v ∈ r.transportedLower e ↔ e.symm v ∈ r.lower :=
  equiv_image_mem_iff e r.lower v

/-- Transport preserves reflexivity of the COMPLETE named unary value. -/
theorem LocalOrderedRepresentative.transportedValue_reflexive
    (r : LocalOrderedRepresentative U) (e : U ≃ V) (v : V) :
    v ∈ r.transportedValue e v := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨e.symm v, r.value_reflexive (e.symm v),
    e.apply_symm_apply v⟩

/-- Transport preserves transitivity (nestedness) of the complete
finite unary values, not just inclusion of individual neighbours. -/
theorem LocalOrderedRepresentative.transportedValue_nested
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (v w : V) (hvw : w ∈ r.transportedValue e v) :
    r.transportedValue e w ⊆ r.transportedValue e v := by
  intro z hwz
  apply (r.transportedValue_mem_iff e v z).mpr
  exact r.value_nested (e.symm v) (e.symm w)
    ((r.transportedValue_mem_iff e v w).mp hvw)
    ((r.transportedValue_mem_iff e w z).mp hwz)

/-- Transport preserves the edge-cover hypothesis needed to recover
the entire graph from the two unary values C,J. -/
theorem LocalOrderedRepresentative.transportedGraph_edge_covered
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (v w : V) (hvw : (r.transportedGraph e).adj v w) :
    w ∈ r.transportedValue e v ∨
      v ∈ r.transportedValue e w := by
  have hOld : r.graph.adj (e.symm v) (e.symm w) := hvw
  rcases r.graph_edge_covered (e.symm v) (e.symm w) hOld with
    h | h
  · exact Or.inl ((r.transportedValue_mem_iff e v w).mpr h)
  · exact Or.inr ((r.transportedValue_mem_iff e w v).mpr h)

/-- The full transported graph can therefore be recovered by the
unary back-adjacency operation J(x)=N(x)∩C(x), exactly as in §4. -/
theorem LocalOrderedRepresentative.transportedGraph_from_J
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (v w : V) :
    (r.transportedGraph e).adj v w ↔
      w ∈ (r.transportedGraph e).backAdjacencyValue
        (r.transportedValue e) v ∨
      v ∈ (r.transportedGraph e).backAdjacencyValue
        (r.transportedValue e) w := by
  exact (r.transportedGraph e).adj_iff_backAdjacencyValue
    (r.transportedValue e)
    (r.transportedGraph_edge_covered e) v w

/-- The selected order in an occurrence puts the full lower part
before ALL of the top vertices, with no distinguished generator. -/
theorem LocalOrderedRepresentative.transportedLower_before_top
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    {p b : V}
    (hp : p ∈ r.transportedLower e)
    (hb : b ∉ r.transportedLower e) :
    r.transportedLess e p b := by
  exact r.lower_before_top (e.symm p)
    ((r.transportedLower_mem_iff e p).mp hp)
    (e.symm b)
    (fun h => hb ((r.transportedLower_mem_iff e b).mpr h))

/-- The transported lower part is closed under the COMPLETE named
unary value. This is not just edge-closedness. -/
theorem LocalOrderedRepresentative.transportedLower_closed
    (r : LocalOrderedRepresentative U) (e : U ≃ V) :
    ClosedUnder (r.transportedValue e) (r.transportedLower e) := by
  intro p hp b hb
  have hp' : e.symm p ∈ r.lower :=
    (r.transportedLower_mem_iff e p).mp hp
  have hb' : e.symm b ∈ r.value (e.symm p) :=
    (r.transportedValue_mem_iff e p b).mp hb
  exact (r.transportedLower_mem_iff e b).mpr
    (r.lower_closed (e.symm p) hp' hb')

/-- Every transported top vertex generates the WHOLE transported
local diagram. The complete image equality uses bijectivity. -/
theorem LocalOrderedRepresentative.transportedTop_generates
    (r : LocalOrderedRepresentative U) (e : U ≃ V)
    (b : V) (hb : b ∉ r.transportedLower e) :
    r.transportedValue e b = Finset.univ := by
  classical
  have hb' : e.symm b ∉ r.lower :=
    fun h => hb ((r.transportedLower_mem_iff e b).mpr h)
  change (r.value (e.symm b)).image e = Finset.univ
  rw [r.top_generates (e.symm b) hb']
  ext v
  constructor
  · intro _
    exact Finset.mem_univ v
  · intro _
    exact Finset.mem_image.mpr
      ⟨e.symm v, Finset.mem_univ _, e.apply_symm_apply v⟩

/-- If two occurrences have the same chosen representative, there
is a canonical comparison bijection between their underlying
carriers. No invariance of a chosen order under arbitrary unordered
automorphisms is required. -/
def localComparison (e : U ≃ V) (f : U ≃ W) : V ≃ W :=
  e.symm.trans f

@[simp] theorem localComparison_apply (e : U ≃ V) (f : U ≃ W)
    (u : U) : localComparison e f (e u) = f u := by
  simp [localComparison]

theorem LocalOrderedRepresentative.localComparison_order
    (r : LocalOrderedRepresentative U)
    (e : U ≃ V) (f : U ≃ W) (v w : V) :
    r.transportedLess e v w ↔
      r.transportedLess f (localComparison e f v)
        (localComparison e f w) := by
  simp [transportedLess, localComparison]

theorem LocalOrderedRepresentative.localComparison_graph
    (r : LocalOrderedRepresentative U)
    (e : U ≃ V) (f : U ≃ W) (v w : V) :
    (r.transportedGraph e).adj v w ↔
      (r.transportedGraph f).adj (localComparison e f v)
        (localComparison e f w) := by
  simp [transportedGraph, localComparison]

theorem LocalOrderedRepresentative.localComparison_lower
    (r : LocalOrderedRepresentative U)
    (e : U ≃ V) (f : U ≃ W) (v : V) :
    v ∈ r.transportedLower e ↔
      localComparison e f v ∈ r.transportedLower f := by
  rw [r.transportedLower_mem_iff e v,
    r.transportedLower_mem_iff f (localComparison e f v)]
  simp [localComparison]

theorem LocalOrderedRepresentative.localComparison_value
    (r : LocalOrderedRepresentative U)
    (e : U ≃ V) (f : U ≃ W) (v w : V) :
    w ∈ r.transportedValue e v ↔
      localComparison e f w ∈
        r.transportedValue f (localComparison e f v) := by
  rw [r.transportedValue_mem_iff e v w,
    r.transportedValue_mem_iff f (localComparison e f v)
      (localComparison e f w)]
  simp [localComparison]

/-- A choice of ONE ordered representative for each declared local
type. The index set must later be shown to describe precisely the
one-generated types of the finite functional C₀ age, including the
already ordered lower part. No representative has a named generator. -/
structure ChosenLocalOrders (I : Type*) where
  size : I → ℕ
  representative : (i : I) →
    LocalOrderedRepresentative (Fin (size i))

end FiniteUnaryCoordinates
end BigHrushovski
