import BigHrushovski.C0LocalComponents

/-!
# Restricting the C0 enumeration to a finite unary-closed substructure

An f_Cl-closed set cannot contain only part of a closure-component:
at each stage it either omits the block or contains it whole,
including all its old neighbours. The no-cross predimension lemma
then transfers the original minimal strong increment to the
restricted enumeration.

This verifies the hereditary minimal-component argument in the
manuscript. It does not establish the free-amalgamation functional
age or its countable extension property.
-/

namespace BigHrushovski

namespace Predimension

/-- Concatenating two finite chains of minimal strong extensions. -/
theorem MinimalStrongChain.append
    {V : Type*} [DecidableEq V] {d : Predimension V}
    {a b : Finset V} (h : MinimalStrongChain d a b) :
    ∀ {c : Finset V}, MinimalStrongChain d b c →
      MinimalStrongChain d a c := by
  induction h with
  | refl a =>
      intro c hTail
      exact hTail
  | @step a b c hStep hRest ih =>
      intro z hTail
      exact MinimalStrongChain.step hStep (ih hTail)

end Predimension

namespace FiniteCatalogue

/-- When a unary-closed finite set meets a component B_n, its
restriction to the enumerated prefix gains precisely B_n, and the
result is still a minimal strong extension over the restricted prefix. -/
theorem genericC0UnaryClosed_cut_minimal
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) (n : ℕ)
    (hMeet : (s ∩ genericC0Component n).Nonempty) :
    genericTwoSparseGraph.toPredimension.IsMinimalStrongStep
      (s ∩ genericC0MinimalStage n)
      (s ∩ genericC0MinimalStage (n + 1)) := by
  obtain ⟨v, hv⟩ := hMeet
  have hvS : v ∈ s := (Finset.mem_inter.mp hv).1
  have hvB : v ∈ genericC0Component n :=
    (Finset.mem_inter.mp hv).2
  have hB : genericC0Component n ⊆ s :=
    genericC0UnaryClosed_component s hs n v hvB hvS
  have hStageEq :=
    genericC0UnaryClosed_cut_succ_of_meeting s hs n ⟨v, hv⟩
  have hOriginal :
      genericTwoSparseGraph.toPredimension.IsMinimalStrongStep
        (genericC0MinimalStage n)
        (genericC0MinimalStage n ∪ genericC0Component n) := by
    rw [← genericC0Stage_succ_eq_union n]
    exact genericC0MinimalStage_minimal_step n
  rw [hStageEq]
  exact genericTwoSparseGraph.minimalStrongStep_local_of_noCross
    (s ∩ genericC0MinimalStage n)
    (genericC0MinimalStage n)
    (genericC0Component n)
    Finset.inter_subset_right
    (genericC0Component_disjoint_old n)
    (genericC0UnaryClosed_noCross s hs n hB)
    hOriginal

/-- Every stage of the induced enumeration is either unchanged or
a minimal strong extension. The old enumeration may contain extra
components, so an unchanged step is essential rather than erroneous. -/
theorem genericC0UnaryClosed_cut_step
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) (n : ℕ) :
    s ∩ genericC0MinimalStage (n + 1) =
      s ∩ genericC0MinimalStage n ∨
    genericTwoSparseGraph.toPredimension.IsMinimalStrongStep
      (s ∩ genericC0MinimalStage n)
      (s ∩ genericC0MinimalStage (n + 1)) := by
  by_cases hMeet : (s ∩ genericC0Component n).Nonempty
  · exact Or.inr (genericC0UnaryClosed_cut_minimal s hs n hMeet)
  · exact Or.inl (genericC0_cut_succ_of_omitted s n hMeet)

/-- The nontrivial cuts of the concrete minimal enumeration give
a finite minimal strong chain up to every restricted prefix. -/
theorem genericC0UnaryClosed_minimalChain_to_stage
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) (n : ℕ) :
    Predimension.MinimalStrongChain
      genericTwoSparseGraph.toPredimension
      ∅ (s ∩ genericC0MinimalStage n) := by
  induction n with
  | zero =>
      rw [genericC0MinimalStage_zero]
      have hEmpty : s ∩ (∅ : Finset ℕ) = ∅ := Finset.inter_empty s
      rw [hEmpty]
      exact Predimension.MinimalStrongChain.refl ∅
  | succ n ih =>
      rcases genericC0UnaryClosed_cut_step s hs n with hEq | hMin
      · rw [hEq]
        exact ih
      · exact ih.append
          (Predimension.MinimalStrongChain.step hMin
            (Predimension.MinimalStrongChain.refl _))

/-- Every finite unary-closed substructure is built from the empty
graph by finitely many minimal strong steps obtained by retaining
the nonempty cuts of the original C0 enumeration. -/
theorem genericC0UnaryClosed_minimalPresentation
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) :
    Predimension.MinimalStrongChain
      genericTwoSparseGraph.toPredimension ∅ s := by
  obtain ⟨n, hn⟩ :=
    genericC0MinimalStrongChain.contains_finite s
  have hEq : s ∩ genericC0MinimalStage n = s := by
    ext v
    constructor
    · intro hv
      exact (Finset.mem_inter.mp hv).1
    · intro hv
      exact Finset.mem_inter.mpr ⟨hv, hn hv⟩
  have hChain :=
    genericC0UnaryClosed_minimalChain_to_stage s hs n
  rw [hEq] at hChain
  exact hChain

end FiniteCatalogue
end BigHrushovski
