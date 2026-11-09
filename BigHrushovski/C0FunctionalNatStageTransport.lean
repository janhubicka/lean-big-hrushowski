import BigHrushovski.C0FunctionalFairRecursion
import BigHrushovski.CoherentNatC0Stages
import BigHrushovski.NatGraphStage

/-!
# Exact Nat transport of finite canonical functional C₀ stages

The chosen fair finite stages are graphs on finite ordinal carriers.
To construct a countable graph and unary operation we transport each
finite graph to a Nat-supported graph and each complete canonical
unary value to a finite set of Nat labels. Old numerical coordinates
are fixed by each certified successor.

These lemmas prove exact old-old graph agreement (including nonedges)
and equality of whole old unary values across one successor. They
do not infer any countable extension property from graph coherence.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- The canonical inclusion of a finite ordinal into ℕ is injective. -/
theorem fin_val_injective (n : ℕ) :
    Function.Injective (fun u : Fin n => u.val) := by
  intro x y hxy
  exact Fin.ext hxy

/-- Extend a finite canonical graph to a graph on ℕ supported
exactly on its finite initial interval. -/
noncomputable def natGraph (s : FiniteFunctionalNatStage) :
    GraphOn ℕ :=
  s.model.graph.transportedToNat
    (fun u : Fin s.size => u.val) (fin_val_injective s.size)

/-- Each complete canonical unary value has a literal finite image
in ℕ on the stage and is empty off that finite support. -/
noncomputable def natValue (s : FiniteFunctionalNatStage)
    (x : ℕ) : Finset ℕ :=
  if h : x < s.size then
    (s.model.unaryValue ⟨x, h⟩).image (fun z : Fin s.size => z.val)
  else ∅

theorem natValue_inside (s : FiniteFunctionalNatStage)
    (x : ℕ) (hx : x < s.size) :
    s.natValue x =
      (s.model.unaryValue ⟨x, hx⟩).image
        (fun z : Fin s.size => z.val) := by
  simp only [natValue, dif_pos hx]

/-- Both graph edges and nonedges on old finite vertices
are reflected exactly after the Nat transport. -/
theorem natGraph_induced (s : FiniteFunctionalNatStage)
    (x y : Fin s.size) :
    s.model.graph.adj x y ↔ s.natGraph.adj x.val y.val :=
  s.model.graph.transportedToNat_induced
    (fun z : Fin s.size => z.val)
    (fin_val_injective s.size) x y

/-- No edge in a finite transported graph can leave
its actual finite numerical support. -/
theorem natGraph_edge_support (s : FiniteFunctionalNatStage)
    {x y : ℕ} (h : s.natGraph.adj x y) :
    x ∈ Finset.range s.size ∧ y ∈ Finset.range s.size := by
  change ∃ u v : Fin s.size,
    u.val = x ∧ v.val = y ∧ s.model.graph.adj u v at h
  obtain ⟨u, v, hu, hv, _⟩ := h
  exact ⟨Finset.mem_range.mpr (by rw [← hu]; exact u.isLt),
    Finset.mem_range.mpr (by rw [← hv]; exact v.isLt)⟩

/-- Finite canonical unary values always remain in their
own finite stage, including the full backward-reachable blocks. -/
theorem natValue_supported (s : FiniteFunctionalNatStage)
    (x : ℕ) (hx : x < s.size) :
    s.natValue x ⊆ Finset.range s.size := by
  rw [s.natValue_inside x hx]
  intro y hy
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hy
  rw [← hv]
  exact Finset.mem_range.mpr v.isLt

/-- The finite successor preserves both directions of adjacency
on the *same* old Nat labels; no accidental new old-old edge appears. -/
theorem natGraph_agree_of_successor
    {step : ℕ} {s t : FiniteFunctionalNatStage}
    (h : IsFairFunctionalSuccessor step s t)
    (x y : ℕ) (hx : x < s.size) (hy : y < s.size) :
    s.natGraph.adj x y ↔ t.natGraph.adj x y := by
  let u : Fin s.size := ⟨x, hx⟩
  let v : Fin s.size := ⟨y, hy⟩
  have hux : (h.old u).val = x := h.old_labels u
  have hvy : (h.old v).val = y := h.old_labels v
  calc
    s.natGraph.adj x y ↔ s.model.graph.adj u v :=
      (s.natGraph_induced u v).symm
    _ ↔ t.model.graph.adj (h.old u) (h.old v) :=
      h.old_graph u v
    _ ↔ t.natGraph.adj x y := by
      have hh := t.natGraph_induced (h.old u) (h.old v)
      rw [hux, hvy] at hh
      exact hh

/-- The *entire* old finite unary value is unchanged on
the common Nat coordinate when passing to a new finite stage. -/
theorem natValue_agree_of_successor
    {step : ℕ} {s t : FiniteFunctionalNatStage}
    (h : IsFairFunctionalSuccessor step s t)
    (x : ℕ) (hx : x < s.size) :
    t.natValue x = s.natValue x := by
  let u : Fin s.size := ⟨x, hx⟩
  have hxT : x < t.size := lt_trans hx h.grows
  have hOldEq : h.old u = (⟨x, hxT⟩ : Fin t.size) :=
    Fin.ext (h.old_labels u)
  calc
    t.natValue x =
      (t.model.unaryValue (h.old u)).image
        (fun z : Fin t.size => z.val) := by
      rw [t.natValue_inside x hxT, hOldEq]
    _ = ((s.model.unaryValue u).image h.old).image
        (fun z : Fin t.size => z.val) := by
      rw [h.old_values u]
    _ = (s.model.unaryValue u).image
        (fun z : Fin s.size => z.val) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro z hz
      exact h.old_labels z
    _ = s.natValue x := (s.natValue_inside x hx).symm

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
