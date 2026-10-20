import BigHrushovski.GlobalDClosedHull
import BigHrushovski.CFBirthGeneratedClosure
import BigHrushovski.CFDClosedTransport

/-!
# Naturality of finite globally d-closed hulls in the C_F birth graph

The global H-operation is computed inside any finite globally
strictly d-closed container. This is true for all finite closed
containers, not merely the particular stages in the exhaustion.

If f is an induced injection of the countable birth graph,
T is a finite b-closed set, and f[T] is also b-closed, then
finite d-closed hulls commute exactly with f on all subsets S
of T. The proof uses the already verified finite induced-image
hull theorem and the two global closed containers.

This is the finite H-value transport needed for the b-to-(R,H)
embedding implication. Whether f maps b-closed sets to b-closed
sets is deliberately an explicit hypothesis; that follows from
the separate complete b-value preservation condition.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- Any finite globally strictly d-closed container computes the
same d-hull as the countable globally closed exhaustion.
No requirement that this container equals a stage image. -/
theorem globalDClosedHull_eq_closedContainer
    (d : Predimension V) (e : DClosedChain d)
    (s t : Finset V)
    (hst : s ⊆ t)
    (ht : d.IsGloballyDClosed t) :
    d.globalDClosedHull e s = d.dClosedHull s t := by
  have hFinite : d.IsDClosed (d.dClosedHull s t) t :=
    d.dClosedHull_dclosed s t
  have hFiniteGlobal : d.IsGloballyDClosed (d.dClosedHull s t) :=
    d.globallyDClosed_of_dClosed_in_global hFinite ht
  have hHsubFinite : d.globalDClosedHull e s ⊆ d.dClosedHull s t :=
    d.globalDClosedHull_least e (d.subset_dClosedHull hst) hFiniteGlobal
  have hHsubT : d.globalDClosedHull e s ⊆ t :=
    d.globalDClosedHull_least e hst ht
  have hHrel : d.IsDClosed (d.globalDClosedHull e s) t :=
    IsGloballyDClosed.restrict d (d.globalDClosedHull_global e s) hHsubT
  have hFiniteSubH : d.dClosedHull s t ⊆ d.globalDClosedHull e s :=
    d.dClosedHull_least (d.subset_globalDClosedHull e s) hHrel
  exact le_antisymm hHsubFinite hFiniteSubH

end Predimension

namespace CFCoherentTower

/-- Transport complete H-values across an induced injection when
both the chosen finite container and its image are b-closed.
The conclusion is exact image equality, not merely an inclusion. -/
theorem birthDClosedHull_image_of_closedContainer
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hAdj : ∀ u v : Vertex F K,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (s t : Finset (Vertex F K))
    (hst : s ⊆ t)
    (htClosed : IsBirthBlockClosed F K t)
    (htImageClosed : IsBirthBlockClosed F K (t.image f)) :
    (birthDClosedHull F K s).image f =
      birthDClosedHull F K (s.image f) := by
  classical
  let G := countableGraph F K
  let d := G.toPredimension
  have hTGlobal : d.IsGloballyDClosed t :=
    birthBlockClosed_global_dClosed F K t htClosed
  have hImageGlobal : d.IsGloballyDClosed (t.image f) :=
    birthBlockClosed_global_dClosed F K (t.image f) htImageClosed
  have hFinite :
      birthDClosedHull F K s = d.dClosedHull s t :=
    d.globalDClosedHull_eq_closedContainer
      (birthDClosedChain F K) s t hst hTGlobal
  have hTarget :
      birthDClosedHull F K (s.image f) =
        d.dClosedHull (s.image f) (t.image f) :=
    d.globalDClosedHull_eq_closedContainer
      (birthDClosedChain F K) (s.image f) (t.image f)
      (Finset.image_mono f hst) hImageGlobal
  calc
    (birthDClosedHull F K s).image f =
        (d.dClosedHull s t).image f := congrArg (Finset.image f) hFinite
    _ = d.dClosedHull (s.image f) (t.image f) :=
      G.dClosedHull_image G f hf hAdj s t hst
    _ = birthDClosedHull F K (s.image f) := hTarget.symm

end CFCoherentTower
end BigHrushovski
