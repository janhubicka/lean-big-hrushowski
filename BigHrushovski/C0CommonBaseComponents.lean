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
There is no need to align the witnessing orders. A closed common
base can be frontloaded in the second factor while the first
factor's component order is kept fixed.
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


/-- For adjacent vertices in different components, the direction
of their component order is determined by membership in the
complete unary value. The later component depends on the earlier
one through their graph edge. -/
theorem adjacent_order_iff_unary_membership
    {X : Type*} [Fintype X] [DecidableEq X] {t : ℕ}
    (G : GraphOn X) (κ : X → Fin t)
    (u v : X) (hAdj : G.adj u v)
    (hDifferent : κ u ≠ κ v) :
    (κ u).val < (κ v).val ↔
      u ∈ canonicalValue G κ v := by
  constructor
  · intro hLess
    have hDep : backDependency G κ (κ v) (κ u) :=
      ⟨hLess, v, u, rfl, rfl, G.symm u v hAdj⟩
    exact (mem_canonicalValue_iff G κ v u).mpr
      (TaggedAmalgam.DependencyAncestor.step
        TaggedAmalgam.DependencyAncestor.root hDep)
  · intro hValue
    have hLe : (κ u).val ≤ (κ v).val :=
      canonicalAncestor_index_le G κ
        ((mem_canonicalValue_iff G κ v u).mp hValue)
    have hNe : (κ u).val ≠ (κ v).val := by
      intro hEq
      exact hDifferent (Fin.ext hEq)
    omega

/-- Two presentations with the same complete named unary function
orient every graph edge between distinct components in the same
chronological direction. Their orders can differ only on pairs
not forced by the dependency relation. -/
theorem adjacent_orientation_of_equal_canonicalValues
    {X : Type*} [Fintype X] [DecidableEq X] {t₁ t₂ : ℕ}
    (G : GraphOn X) (κ : X → Fin t₁)
    (indexH : X → Fin t₂)
    (hValues : ∀ w : X,
      canonicalValue G κ w = canonicalValue G indexH w)
    (u v : X) (hAdj : G.adj u v)
    (hDifferent : κ u ≠ κ v) :
    ((κ u).val < (κ v).val) ↔
      ((indexH u).val < (indexH v).val) := by
  have hDiffH : indexH u ≠ indexH v := by
    intro hEq
    exact hDifferent
      ((same_components_of_equal_canonicalValues
        G κ indexH hValues u v).mpr hEq)
  constructor
  · intro hLess
    have hMem : u ∈ canonicalValue G κ v :=
      (adjacent_order_iff_unary_membership
        G κ u v hAdj hDifferent).mp hLess
    have hMemH : u ∈ canonicalValue G indexH v := by
      rw [← hValues v]
      exact hMem
    exact (adjacent_order_iff_unary_membership
      G indexH u v hAdj hDiffH).mpr hMemH
  · intro hLess
    have hMem : u ∈ canonicalValue G indexH v :=
      (adjacent_order_iff_unary_membership
        G indexH u v hAdj hDiffH).mp hLess
    have hMemG : u ∈ canonicalValue G κ v := by
      rw [hValues v]
      exact hMem
    exact (adjacent_order_iff_unary_membership
      G κ u v hAdj hDifferent).mpr hMemG


end FiniteC0
end BigHrushovski
