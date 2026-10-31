import BigHrushovski.C0CoordinateClosedRestriction
import Mathlib.Order.Hom.Basic

/-!
# Canonical coordinate-labelled finite closure diagrams

In the manuscript the host W is introduced by quotienting triples
(D, a, e) by pointed ordered isomorphisms commuting with e.

For a finite ordered D and strictly increasing e : D ↪o ℕ,
the quotient has a literal representative: use the finite coordinate
set e[D] as the carrier and transport the entire graph and both
unary set values along the equivalence D ≃ e[D].

This module checks the graph/function transport and provides the
finite-coordinate normal form. It does NOT yet define W itself,
restrict its vertex codes to their one-generated subclosures, or
prove that each normal-form code belongs to the functional age.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]

/-- The literal finite set of coordinates used by a pointed finite
ordered closure. Its order is inherited from the natural numbers. -/
noncomputable def labelSupport (e : U ↪o ℕ) : Finset ℕ :=
  Finset.univ.image e

/-- The strictly increasing labelling is a bijection onto its literal
image. No choices of abstract finite numberings are needed. -/
noncomputable def labelEquiv (e : U ↪o ℕ) :
    U ≃ labelSupport e := by
  classical
  let toLabel : U → labelSupport e :=
    fun u => ⟨e u,
      Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩⟩
  apply Equiv.ofBijective toLabel
  constructor
  · intro u v huv
    apply e.injective
    exact congrArg Subtype.val huv
  · intro v
    obtain ⟨u, _, huv⟩ := Finset.mem_image.mp v.property
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact huv

theorem labelEquiv_val (e : U ↪o ℕ) (u : U) :
    (labelEquiv e u).val = e u := rfl

/-- Transport a complete finite unary function to the canonical
coordinate carrier, without discarding any of its output vertices. -/
noncomputable def labelValue (C : U → Finset U)
    (e : U ↪o ℕ) (u : labelSupport e) :
    Finset (labelSupport e) :=
  (C ((labelEquiv e).symm u)).image (labelEquiv e)

theorem labelValue_at
    (C : U → Finset U) (e : U ↪o ℕ) (u : U) :
    labelValue C e (labelEquiv e u) =
      (C u).image (labelEquiv e) := by
  simp [labelValue]

theorem labelValue_mem_iff
    (C : U → Finset U) (e : U ↪o ℕ) (u v : U) :
    labelEquiv e v ∈ labelValue C e (labelEquiv e u) ↔
      v ∈ C u := by
  classical
  rw [labelValue_at]
  constructor
  · intro hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hv
    have hwv : w = v := (labelEquiv e).injective heq
    simpa only [hwv] using hw
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Transport the entire induced graph to the literal coordinate
carrier. Both adjacency and non-adjacency are reflected. -/
noncomputable def labelGraph (G : GraphOn U)
    (e : U ↪o ℕ) : GraphOn (labelSupport e) where
  adj x y := G.adj ((labelEquiv e).symm x)
    ((labelEquiv e).symm y)
  symm x y h := G.symm _ _ h
  irrefl x := G.irrefl _

theorem labelGraph_adj_iff
    (G : GraphOn U) (e : U ↪o ℕ) (u v : U) :
    (labelGraph G e).adj (labelEquiv e u) (labelEquiv e v) ↔
      G.adj u v := by
  simp [labelGraph]

/-- In particular, the graph-derived unary operation J commutes
with passing to literal coordinates. This reuses the complete
function-image transport in C0CoordinateHostGraph rather than
a second proof about edges and nonedges. -/
theorem labelBackAdjacencyValue
    (G : GraphOn U) (C : U → Finset U)
    (e : U ↪o ℕ) (u : U) :
    (labelGraph G e).backAdjacencyValue (labelValue C e)
      (labelEquiv e u) =
    labelValue (G.backAdjacencyValue C) e (labelEquiv e u) := by
  have hAdj : ∀ x y : U,
      G.adj x y ↔
        (labelGraph G e).adj (labelEquiv e x) (labelEquiv e y) := by
    intro x y
    exact (labelGraph_adj_iff G e x y).symm
  have hC : ∀ x : U,
      (C x).image (labelEquiv e) =
        labelValue C e (labelEquiv e x) := by
    intro x
    exact (labelValue_at C e x).symm
  calc
    (labelGraph G e).backAdjacencyValue (labelValue C e)
        (labelEquiv e u) =
      (G.backAdjacencyValue C u).image (labelEquiv e) :=
        (G.backAdjacencyValue_image (labelGraph G e)
          C (labelValue C e) (labelEquiv e) hAdj hC u).symm
    _ = labelValue (G.backAdjacencyValue C) e
        (labelEquiv e u) :=
          (labelValue_at (G.backAdjacencyValue C) e u).symm

end FiniteUnaryCoordinates
end BigHrushovski
