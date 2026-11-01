import BigHrushovski.OrientationReachability
import Mathlib.Tactic

/-!
# Minimal successor-closed extensions

A minimal proper extension between finite successor-closed vertex
sets adds exactly one strongly connected component. The argument
uses the *least* successor closure and avoids any assumption that
the orientation is acyclic.

In the orientation class D₀, the strong embeddings are exactly
the successor-closed embeddings. This finite statement is the
component-decomposition ingredient for the exact N₀ degrees.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [DecidableEq V] (O : FiniteOrientation V)

/-- A proper successor-closed extension with no intermediate
successor-closed set. -/
def IsMinimalSuccessorStep (s t : Finset V) : Prop :=
  s ⊂ t ∧
  O.IsSuccessorClosed s ∧
  O.IsSuccessorClosed t ∧
  ∀ u : Finset V, s ⊆ u → u ⊆ t →
    O.IsSuccessorClosed u → u = s ∨ u = t

theorem mem_successorClosure_singleton_iff [Fintype V]
    (x y : V) :
    y ∈ O.successorClosure ({x} : Finset V) ↔ O.Reaches x y := by
  rw [O.mem_successorClosure_iff ({x} : Finset V) y]
  constructor
  · rintro ⟨u, hu, huy⟩
    have hux : u = x := Finset.mem_singleton.mp hu
    subst u
    exact huy
  · intro hxy
    exact ⟨x, Finset.mem_singleton.mpr rfl, hxy⟩

/-- If s ⊂ t is a minimal successor-closed extension, each new
vertex reaches every other new vertex. The proof uses s ∪ scl(x)
as an intermediate closed set, forced to equal t. -/
theorem minimalSuccessorStep_reaches_new [Fintype V]
    {s t : Finset V}
    (hmin : O.IsMinimalSuccessorStep s t)
    {x y : V} (hx : x ∈ t \ s) (hy : y ∈ t \ s) :
    O.Reaches x y := by
  obtain ⟨hProper, hs, ht, hNoMiddle⟩ := hmin
  have hst : s ⊆ t :=
    (Finset.ssubset_iff_subset_ne.mp hProper).1
  obtain ⟨hxT, hxNotS⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyT, hyNotS⟩ := Finset.mem_sdiff.mp hy
  have hSingleton : ({x} : Finset V) ⊆ t := by
    intro v hv
    have hvx : v = x := Finset.mem_singleton.mp hv
    subst v
    exact hxT
  have hClT : O.successorClosure ({x} : Finset V) ⊆ t :=
    O.successorClosure_minimal hSingleton ht
  let u : Finset V := s ∪ O.successorClosure ({x} : Finset V)
  have hUC : O.IsSuccessorClosed u := by
    dsimp [u]
    exact O.successorClosed_union hs
      (O.successorClosure_isClosed ({x} : Finset V))
  have hSU : s ⊆ u := by
    dsimp [u]
    exact Finset.subset_union_left
  have hUT : u ⊆ t := by
    dsimp [u]
    exact Finset.union_subset hst hClT
  have hxU : x ∈ u := by
    change x ∈ s ∪ O.successorClosure ({x} : Finset V)
    exact Finset.mem_union_right s
      (O.subset_successorClosure ({x} : Finset V)
        (Finset.mem_singleton.mpr rfl))
  have hUne : u ≠ s := by
    intro hEq
    have hxS : x ∈ s := by
      rw [← hEq]
      exact hxU
    exact hxNotS hxS
  have hUTeq : u = t :=
    (hNoMiddle u hSU hUT hUC).resolve_left hUne
  have hyU : y ∈ u := by
    rw [hUTeq]
    exact hyT
  change y ∈ s ∪ O.successorClosure ({x} : Finset V) at hyU
  rcases Finset.mem_union.mp hyU with hyS | hyCl
  · exact (hyNotS hyS).elim
  · exact (O.mem_successorClosure_singleton_iff x y).mp hyCl

/-- The fresh points of a minimal successor-closed step
are pairwise mutually reachable. -/
theorem minimalSuccessorStep_new_stronglyConnected [Fintype V]
    {s t : Finset V}
    (hmin : O.IsMinimalSuccessorStep s t)
    {x y : V} (hx : x ∈ t \ s) (hy : y ∈ t \ s) :
    O.StronglyConnected x y :=
  ⟨O.minimalSuccessorStep_reaches_new hmin hx hy,
   O.minimalSuccessorStep_reaches_new hmin hy hx⟩

/-- The new part of a minimal successor-closed step is exactly
one whole SCC. This is the finite source of the component
intervals in the N₀ degree formula. -/
theorem minimalSuccessorStep_sdiff_eq_component [Fintype V]
    {s t : Finset V}
    (hmin : O.IsMinimalSuccessorStep s t)
    {x : V} (hx : x ∈ t \ s) :
    t \ s = O.component x := by
  have hs : O.IsSuccessorClosed s := hmin.2.1
  have ht : O.IsSuccessorClosed t := hmin.2.2.1
  obtain ⟨hxT, hxNotS⟩ := Finset.mem_sdiff.mp hx
  apply Finset.Subset.antisymm
  · intro y hy
    exact (O.mem_component_iff x y).mpr
      (O.minimalSuccessorStep_new_stronglyConnected hmin hx hy)
  · intro y hy
    have hxy : O.StronglyConnected x y :=
      (O.mem_component_iff x y).mp hy
    have hyT : y ∈ t :=
      O.successorClosed_of_reaches ht hxT hxy.1
    have hyNotS : y ∉ s := by
      intro hyS
      exact hxNotS (O.successorClosed_of_reaches hs hyS hxy.2)
    exact Finset.mem_sdiff.mpr ⟨hyT, hyNotS⟩

end FiniteOrientation
end BigHrushovski
