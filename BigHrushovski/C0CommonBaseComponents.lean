import BigHrushovski.C0IntrinsicComponents

/-!
# Closed C0 component ideals and coherence on a common functional base

The component partition of a finite canonical C0 structure is intrinsic
to its complete set-valued unary function. The next necessary facts for
two-sided functional free amalgamation are:

1. Every unary-closed subset is downward closed under complete
   component dependency reachability: if it meets a component, it
   contains all vertices in every predecessor component.
2. When two finite canonical presentations contain the same finite
   named functional base through arbitrary injective maps, the two
   presentations identify exactly the same pairs of base vertices as
   belonging to one component, even if their chronological orders
   and finite index types differ.

These statements avoid choosing a common chronological ordering.
Aligning two resulting orders by swaps of incomparable components
remains a separate next step.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- A set closed under the complete C0 unary function is a union of
whole components, downward closed under every backward dependency
path from each component it meets. -/
theorem closed_contains_ancestor_component
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    {i j : Fin n}
    (hMeet : ∃ u : V, u ∈ s ∧ κ u = i)
    (hReach : TaggedAmalgam.DependencyAncestor
      (backDependency G κ) i j) :
    component κ j.val ⊆ s := by
  obtain ⟨u, huS, huI⟩ := hMeet
  intro v hv
  have hvJ : κ v = j := Fin.ext
    ((mem_component_iff κ j.val v).mp hv)
  have hPath : TaggedAmalgam.DependencyAncestor
      (backDependency G κ) (κ u) (κ v) := by
    simpa [huI, hvJ] using hReach
  exact hClosed u huS
    ((mem_canonicalValue_iff G κ u v).mpr hPath)

/-- In particular, every direct predecessor component of a component
met by a closed set is contained entirely in that closed set. -/
theorem closed_contains_direct_predecessor
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    {i j : Fin n}
    (hMeet : ∃ u : V, u ∈ s ∧ κ u = i)
    (hDep : backDependency G κ i j) :
    component κ j.val ⊆ s := by
  exact closed_contains_ancestor_component G κ s hClosed
    hMeet (TaggedAmalgam.DependencyAncestor.step
      TaggedAmalgam.DependencyAncestor.root hDep)

end FiniteC0

namespace FiniteC0

variable {P U W : Type*}
variable [Fintype P] [DecidableEq P]
variable [Fintype U] [DecidableEq U]
variable [Fintype W] [DecidableEq W]
variable {n m : ℕ}

/-- The component partition on a common functional base is the same
when it is embedded into two different canonical finite C0 structures.

The common named unary function F:P→Finset P is assumed to be
preserved exactly by both injected embeddings, including all
vertices of every reached component. No common witnessing
enumeration or index relabelling is assumed. -/
theorem common_component_partition_of_shared_unary_values
    (G : GraphOn U) (H : GraphOn W)
    (κG : U → Fin n) (κH : W → Fin m)
    (i : P → U) (j : P → W)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (F : P → Finset P)
    (hG : ∀ p : P,
      canonicalValue G κG (i p) = (F p).image i)
    (hH : ∀ p : P,
      canonicalValue H κH (j p) = (F p).image j)
    (p q : P) :
    κG (i p) = κG (i q) ↔ κH (j p) = κH (j q) := by
  constructor
  · intro hEqG
    have hValsG : canonicalValue G κG (i p) =
        canonicalValue G κG (i q) :=
      (canonicalValue_eq_iff_index_eq G κG (i p) (i q)).mpr hEqG
    rw [hG p, hG q] at hValsG
    have hF : F p = F q :=
      Finset.image_injective hi hValsG
    have hValsH : canonicalValue H κH (j p) =
        canonicalValue H κH (j q) := by
      rw [hH p, hH q, hF]
    exact (canonicalValue_eq_iff_index_eq H κH (j p) (j q)).mp hValsH
  · intro hEqH
    have hValsH : canonicalValue H κH (j p) =
        canonicalValue H κH (j q) :=
      (canonicalValue_eq_iff_index_eq H κH (j p) (j q)).mpr hEqH
    rw [hH p, hH q] at hValsH
    have hF : F p = F q :=
      Finset.image_injective hj hValsH
    have hValsG : canonicalValue G κG (i p) =
        canonicalValue G κG (i q) := by
      rw [hG p, hG q, hF]
    exact (canonicalValue_eq_iff_index_eq G κG (i p) (i q)).mp hValsG

end FiniteC0
end BigHrushovski
