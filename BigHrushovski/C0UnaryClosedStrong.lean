import BigHrushovski.C0NoCrossCriterion
import BigHrushovski.C0UnaryClosureAlgebra

/-!
# Every finite unary-closed C0 set is globally strong

This is the structural assertion of the manuscript's
C0-functional-closure lemma for the actual countable M0.

The proof cuts a finite unary-closed set S by the finite
minimal strong prefixes A_n. When the next whole component
B_n is omitted, strength extends by transitivity. When it
is included, the unary function forces every old neighbour
of B_n into the selected old part S ∩ A_n, making the union
no-cross; the certified finite closed-block lemma then
proves the next strongness step.

A strong exhaustion allows passage from the finite prefix
statement to global strength in M0.

The theorem does not assert the functional Fraisse extension
property or equivalence of all embedding notions.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- The finite component B_n is disjoint from the old prefix A_n. -/
theorem genericC0Component_disjoint_old (n : ℕ) :
    Disjoint (genericC0MinimalStage n) (genericC0Component n) := by
  apply Finset.disjoint_left.mpr
  intro v hvOld hvB
  exact (Finset.mem_sdiff.mp hvB).2 hvOld

/-- The next strong prefix is exactly the preceding prefix together
with its new finite closure-component. -/
theorem genericC0Stage_succ_eq_union (n : ℕ) :
    genericC0MinimalStage (n + 1) =
      genericC0MinimalStage n ∪ genericC0Component n := by
  ext v
  constructor
  · intro hv
    by_cases hvOld : v ∈ genericC0MinimalStage n
    · exact Finset.mem_union.mpr (Or.inl hvOld)
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_sdiff.mpr ⟨hv, hvOld⟩))
  · intro hv
    rcases Finset.mem_union.mp hv with hvOld | hvB
    · exact (genericC0MinimalStage_minimal_step n).1.1 hvOld
    · exact (Finset.mem_sdiff.mp hvB).1

/-- When a finite unary-closed set contains one vertex of a
component, it contains every vertex of that component. -/
theorem genericC0UnaryClosed_component
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s)
    (n v : ℕ)
    (hvB : v ∈ genericC0Component n) (hvS : v ∈ s) :
    genericC0Component n ⊆ s := by
  have hIndex : genericC0ComponentIndex v = n :=
    (genericC0ComponentIndex_eq_iff v n).mpr hvB
  intro w hw
  have hw' : w ∈ genericC0Component (genericC0ComponentIndex v) := by
    simpa only [hIndex] using hw
  exact (hs v hvS) (genericC0UnaryClosure_contains_component v hw')

/-- A unary-closed set containing a whole new component also
contains every old graph neighbour of that component. -/
theorem genericC0UnaryClosed_backNeighbour
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s)
    (n u v : ℕ)
    (huB : u ∈ genericC0Component n) (huS : u ∈ s)
    (hvOld : v ∈ genericC0MinimalStage n)
    (hAdj : genericTwoSparseGraph.adj u v) : v ∈ s := by
  have hIndex : genericC0ComponentIndex u = n :=
    (genericC0ComponentIndex_eq_iff u n).mpr huB
  have hvBack : v ∈ genericTwoSparseGraph.oldNeighbours
      (genericC0MinimalStage (genericC0ComponentIndex u)) u := by
    rw [hIndex]
    exact (genericTwoSparseGraph.mem_oldNeighbours_iff
      (genericC0MinimalStage n) u v).mpr ⟨hvOld, hAdj⟩
  have hInClosure : v ∈ genericC0UnaryClosure u :=
    genericC0UnaryClosure_oldNeighbour
      (genericC0UnaryClosure_self u) hvBack
  exact (hs u huS) hInClosure

/-- Closure under all old back neighbours implies the exact
no-cross hypothesis needed for the finite strength induction. -/
theorem genericC0UnaryClosed_noCross
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) (n : ℕ)
    (hB : genericC0Component n ⊆ s) :
    genericTwoSparseGraph.NoCrossEdges
      (genericC0MinimalStage n)
      ((s ∩ genericC0MinimalStage n) ∪ genericC0Component n) := by
  apply genericTwoSparseGraph.noCross_of_backNeighbours
    (genericC0MinimalStage n) (s ∩ genericC0MinimalStage n)
      (genericC0Component n) Finset.inter_subset_right
  intro u hu v hv hAdj
  exact Finset.mem_inter.mpr
    ⟨genericC0UnaryClosed_backNeighbour s hs n u v hu
       (hB hu) hv hAdj, hv⟩

/-- An f_Cl-closed set meeting the next component contains it whole;
its stage cut grows by precisely that component. -/
theorem genericC0UnaryClosed_cut_succ_of_meeting
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) (n : ℕ)
    (hMeet : (s ∩ genericC0Component n).Nonempty) :
    s ∩ genericC0MinimalStage (n + 1) =
      (s ∩ genericC0MinimalStage n) ∪ genericC0Component n := by
  obtain ⟨v, hv⟩ := hMeet
  have hvS : v ∈ s := (Finset.mem_inter.mp hv).1
  have hvB : v ∈ genericC0Component n :=
    (Finset.mem_inter.mp hv).2
  have hB : genericC0Component n ⊆ s :=
    genericC0UnaryClosed_component s hs n v hvB hvS
  have hStageEq : s ∩ genericC0MinimalStage (n + 1) =
      (s ∩ genericC0MinimalStage n) ∪ genericC0Component n := by
    ext w
    constructor
    · intro hw
      have hwS : w ∈ s := (Finset.mem_inter.mp hw).1
      have hwNew : w ∈ genericC0MinimalStage (n + 1) :=
        (Finset.mem_inter.mp hw).2
      have hwUnion : w ∈ genericC0MinimalStage n ∪
          genericC0Component n := by
        rw [← genericC0Stage_succ_eq_union n]
        exact hwNew
      rcases Finset.mem_union.mp hwUnion with hwOld | hwB
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_inter.mpr ⟨hwS, hwOld⟩))
      · exact Finset.mem_union.mpr (Or.inr hwB)
    · intro hw
      rcases Finset.mem_union.mp hw with hwOld | hwB
      · exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hwOld).1,
           (genericC0MinimalStage_minimal_step n).1.1
             (Finset.mem_inter.mp hwOld).2⟩
      · exact Finset.mem_inter.mpr
          ⟨hB hwB, (Finset.mem_sdiff.mp hwB).1⟩
  exact hStageEq

/-- If a set omits the next component, its stage cut is unchanged.
No closure assumption is necessary in this case. -/
theorem genericC0_cut_succ_of_omitted
    (s : Finset ℕ) (n : ℕ)
    (hOmit : ¬ (s ∩ genericC0Component n).Nonempty) :
    s ∩ genericC0MinimalStage (n + 1) =
      s ∩ genericC0MinimalStage n := by
  have hStageEq : s ∩ genericC0MinimalStage (n + 1) =
      s ∩ genericC0MinimalStage n := by
    ext w
    constructor
    · intro hw
      have hwS : w ∈ s := (Finset.mem_inter.mp hw).1
      have hwNext : w ∈ genericC0MinimalStage (n + 1) :=
        (Finset.mem_inter.mp hw).2
      have hwUnion : w ∈ genericC0MinimalStage n ∪
          genericC0Component n := by
        rw [← genericC0Stage_succ_eq_union n]
        exact hwNext
      rcases Finset.mem_union.mp hwUnion with hwOld | hwB
      · exact Finset.mem_inter.mpr ⟨hwS, hwOld⟩
      · have hbad : (s ∩ genericC0Component n).Nonempty :=
          ⟨w, Finset.mem_inter.mpr ⟨hwS, hwB⟩⟩
        exact (hOmit hbad).elim
    · intro hw
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hw).1,
         (genericC0MinimalStage_minimal_step n).1.1
           (Finset.mem_inter.mp hw).2⟩
  exact hStageEq

/-- The intersection of a finite unary-closed set with every
finite enumeration prefix is strong inside that prefix. -/
theorem genericC0UnaryClosed_stageStrong
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) (n : ℕ) :
    genericTwoSparseGraph.toPredimension.IsStrong
      (s ∩ genericC0MinimalStage n) (genericC0MinimalStage n) := by
  induction n with
  | zero =>
      rw [genericC0MinimalStage_zero]
      simpa using
        (genericTwoSparseGraph.toPredimension.strong_refl (∅ : Finset ℕ))
  | succ n ih =>
      by_cases hMeet : (s ∩ genericC0Component n).Nonempty
      · obtain ⟨v, hv⟩ := hMeet
        have hvS : v ∈ s := (Finset.mem_inter.mp hv).1
        have hvB : v ∈ genericC0Component n :=
          (Finset.mem_inter.mp hv).2
        have hB : genericC0Component n ⊆ s :=
          genericC0UnaryClosed_component s hs n v hvB hvS
        have hStageEq :=
          genericC0UnaryClosed_cut_succ_of_meeting s hs n ⟨v, hv⟩
        have hStrong : genericTwoSparseGraph.toPredimension.IsStrong
            ((s ∩ genericC0MinimalStage n) ∪ genericC0Component n)
            (genericC0MinimalStage n ∪ genericC0Component n) :=
          genericTwoSparseGraph.closedBlock_strong_of_noCross
            (genericC0MinimalStage n) (s ∩ genericC0MinimalStage n)
            (genericC0Component n) ih
            (genericC0Component_disjoint_old n)
            (genericC0UnaryClosed_noCross s hs n hB)
        rw [hStageEq, genericC0Stage_succ_eq_union n]
        exact hStrong
      · have hStageEq := genericC0_cut_succ_of_omitted s n hMeet
        rw [hStageEq]
        exact genericTwoSparseGraph.toPredimension.strong_trans ih
          (genericC0MinimalStage_minimal_step n).1

/-- Every finite unary-closed subset is globally strong in the
countable generic graph M0. -/
theorem genericC0UnaryClosed_global
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) :
    genericTwoSparseGraph.toPredimension.IsGloballyStrong s := by
  intro b hsb
  obtain ⟨n, hn⟩ := genericC0MinimalStrongChain.contains_finite b
  have hsStage : s ⊆ genericC0MinimalStage n := hsb.trans hn
  have hEq : s ∩ genericC0MinimalStage n = s := by
    ext v
    constructor
    · intro hv
      exact (Finset.mem_inter.mp hv).1
    · intro hv
      exact Finset.mem_inter.mpr ⟨hv, hsStage hv⟩
  have hStrong := genericC0UnaryClosed_stageStrong s hs n
  rw [hEq] at hStrong
  exact genericTwoSparseGraph.toPredimension.strong_restrict
    hStrong hsb hn

/-- The closure generated by any finite set, being finite and
unary-closed, is globally strong in M0. -/
theorem genericC0GeneratedClosure_global (s : Finset ℕ) :
    genericTwoSparseGraph.toPredimension.IsGloballyStrong
      (genericC0GeneratedClosure s) :=
  genericC0UnaryClosed_global
    (genericC0GeneratedClosure s)
    (genericC0GeneratedClosure_isClosed s)

/-- In particular every one-generated unary closure is globally strong. -/
theorem genericC0UnaryClosure_global (v : ℕ) :
    genericTwoSparseGraph.toPredimension.IsGloballyStrong
      (genericC0UnaryClosure v) := by
  rw [← genericC0GeneratedClosure_singleton v]
  exact genericC0GeneratedClosure_global ({v} : Finset ℕ)

end FiniteCatalogue
end BigHrushovski
