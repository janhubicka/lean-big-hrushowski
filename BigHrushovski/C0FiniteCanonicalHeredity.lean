import BigHrushovski.C0FiniteCanonicalValues
import BigHrushovski.C0ClosedHereditary

/-!
# Heredity of finite canonical C0 component presentations

The canonical one-generated closure contains every vertex in the
generator's component and every old graph neighbour of that component.
Consequently a finite set closed under the canonical function either
omits each component altogether or retains it as a minimal strong step
over the previously selected components.

This is now an abstract theorem for every finite graph presented by
minimal strong blocks. It no longer depends on the chosen countable
enumeration of the generic graph M0.

The graph minimal-step chain is completely verified here. Equality
of inherited unary values after reindexing and deleting skipped
component slots is a distinct finite transport assertion.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- The restriction of a canonical finite minimal strong enumeration
to a unary-closed set is, at each index, either unchanged or a
minimal strong extension. -/
theorem canonicalValue_closed_cut_step
    (G : GraphOn V) (κ : V → Fin n)
    (hMin : ∀ k : ℕ, k < n →
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k + 1)))
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (k : ℕ) (hk : k < n) :
    (s ∩ oldStage κ (k+1) = s ∩ oldStage κ k) ∨
    G.toPredimension.IsMinimalStrongStep
      (s ∩ oldStage κ k) (s ∩ oldStage κ (k+1)) := by
  classical
  let A := oldStage κ k
  let B := component κ k
  have hWhole : ∀ u ∈ B, B ⊆ canonicalValue G κ u := by
    intro u hu
    exact canonicalValue_contains_component G κ k hu
  have hBack : ∀ u ∈ B, ∀ v ∈ A,
      G.adj u v → v ∈ canonicalValue G κ u := by
    intro u hu v hv hAdj
    exact canonicalValue_oldNeighbour G κ k hu hv hAdj
  have hCase : B ⊆ s ∨ Disjoint s B :=
    G.closedUnderValues_block_dichotomy
      (canonicalValue G κ) s B hClosed hWhole
  rcases hCase with hAll | hNone
  · right
    have hEq : s ∩ (A ∪ B) = (s ∩ A) ∪ B := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvS, hvAB⟩ := Finset.mem_inter.mp hv
        rcases Finset.mem_union.mp hvAB with hvA | hvB
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_inter.mpr ⟨hvS, hvA⟩))
        · exact Finset.mem_union.mpr (Or.inr hvB)
      · intro hv
        rcases Finset.mem_union.mp hv with hvOld | hvB
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hvOld).1,
              Finset.mem_union.mpr
                (Or.inl (Finset.mem_inter.mp hvOld).2)⟩
        · exact Finset.mem_inter.mpr
            ⟨hAll hvB, Finset.mem_union.mpr (Or.inr hvB)⟩
    have hMinOld : G.toPredimension.IsMinimalStrongStep A (A ∪ B) := by
      change G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ k ∪ component κ k)
      rw [← oldStage_succ κ k]
      exact hMin k hk
    have hNo : G.NoCrossEdges A ((s ∩ A) ∪ B) :=
      G.closedUnderValues_block_noCross
        (canonicalValue G κ) s A B hClosed hBack hAll
    have hMinCut : G.toPredimension.IsMinimalStrongStep
        (s ∩ A) ((s ∩ A) ∪ B) :=
      G.minimalStrongStep_local_of_noCross
        (s ∩ A) A B Finset.inter_subset_right
        (oldStage_disjoint_component κ k)
        hNo hMinOld
    rw [oldStage_succ κ k, hEq]
    exact hMinCut
  · left
    rw [oldStage_succ κ k]
    ext v
    constructor
    · intro hv
      obtain ⟨hvS, hvAB⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp hvAB with hvA | hvB
      · exact Finset.mem_inter.mpr ⟨hvS, hvA⟩
      · exact ((Finset.disjoint_left.mp hNone) hvS hvB).elim
    · intro hv
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).1,
          Finset.mem_union.mpr
            (Or.inl (Finset.mem_inter.mp hv).2)⟩

/-- The complete finite graph of every canonical unary-closed set
has a minimal strong chain from the empty structure: retain exactly
the nonempty cuts of the ambient minimal strong presentation. -/
theorem canonicalValue_closed_minimalPresentation
    (G : GraphOn V) (κ : V → Fin n)
    (hMin : ∀ k : ℕ, k < n →
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1)))
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s) :
    Predimension.MinimalStrongChain G.toPredimension ∅ s := by
  classical
  have hInd : ∀ k : ℕ, k ≤ n →
      Predimension.MinimalStrongChain G.toPredimension
        ∅ (s ∩ oldStage κ k) := by
    intro k
    induction k with
    | zero =>
        intro _
        rw [oldStage_zero κ]
        simp only [Finset.inter_empty]
        exact Predimension.MinimalStrongChain.refl ∅
    | succ k ih =>
        intro hk
        rcases canonicalValue_closed_cut_step
          G κ hMin s hClosed k (by omega) with hEq | hStep
        · rw [hEq]
          exact ih (by omega)
        · exact (ih (by omega)).append
            (Predimension.MinimalStrongChain.step hStep
              (Predimension.MinimalStrongChain.refl _))
  have hFinal := hInd n (by omega)
  rw [oldStage_final κ] at hFinal
  simpa only [Finset.inter_univ] using hFinal

end FiniteC0
end BigHrushovski
