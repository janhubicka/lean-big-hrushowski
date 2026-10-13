import BigHrushovski.C0LocalFreeConverse

/-!
# The exact local lower closure of a C0 component

For a vertex v in the fixed countable minimal strong enumeration, write
B(v) for its complete closure-component and C(v) for its finite unary
closure. The lower closure is P(v)=C(v)\B(v).

The lower closure is contained in the old prefix and is closed under
the complete unary function, hence globally strong. Its union with
B(v) is C(v). All old neighbours of B(v) belong to P(v), so the
no-cross relative-predimension calculation applies to the original
minimal increment A_i ⊂ A_(i+1).

It follows that P(v) ⊂ P(v)∪B(v) is a minimal strong step and every
new vertex x in B(v) generates P(v)∪B(v) under the intrinsic graph
strong closure. This is the local minimality assertion in the paper.

Free-amalgamation *persistence* of the local minimal step is a separate
reverse-transfer obligation.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- All predecessor components reached by back-edge dependencies. -/
noncomputable def genericC0LowerClosure (v : ℕ) : Finset ℕ :=
  genericC0UnaryClosure v \
    genericC0Component (genericC0ComponentIndex v)

theorem genericC0LowerClosure_subset_old (v : ℕ) :
    genericC0LowerClosure v ⊆
      genericC0MinimalStage (genericC0ComponentIndex v) := by
  intro w hw
  obtain ⟨hwC, hwNotB⟩ := Finset.mem_sdiff.mp hw
  have hLe : genericC0ComponentIndex w ≤ genericC0ComponentIndex v :=
    ((mem_genericC0UnaryClosure_iff v w).mp hwC).le
  have hNe : genericC0ComponentIndex w ≠
      genericC0ComponentIndex v := by
    intro hEq
    have hB : w ∈ genericC0Component
        (genericC0ComponentIndex v) :=
      (genericC0ComponentIndex_eq_iff w
        (genericC0ComponentIndex v)).mp hEq
    exact hwNotB hB
  have hLt : genericC0ComponentIndex w <
      genericC0ComponentIndex v := by omega
  exact (genericC0ComponentIndex_lt_iff_stage w
    (genericC0ComponentIndex v)).mp hLt

/-- The generated one-point closure is exactly its own component
together with the finite lower closure. -/
theorem genericC0LowerClosure_union_component (v : ℕ) :
    genericC0UnaryClosure v =
      genericC0LowerClosure v ∪
        genericC0Component (genericC0ComponentIndex v) := by
  have hBsub :
      genericC0Component (genericC0ComponentIndex v) ⊆
        genericC0UnaryClosure v :=
    genericC0UnaryClosure_contains_component v
  ext w
  constructor
  · intro hw
    by_cases hB : w ∈ genericC0Component
        (genericC0ComponentIndex v)
    · exact Finset.mem_union.mpr (Or.inr hB)
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_sdiff.mpr ⟨hw, hB⟩))
  · intro hw
    rcases Finset.mem_union.mp hw with hP | hB
    · exact (Finset.mem_sdiff.mp hP).1
    · exact hBsub hB

/-- The lower closure does not need a further strong-closure
operation: it is already closed under every unary function value. -/
theorem genericC0LowerClosure_isClosed (v : ℕ) :
    IsGenericC0UnaryClosed (genericC0LowerClosure v) := by
  intro w hw z hz
  have hwC : w ∈ genericC0UnaryClosure v :=
    (Finset.mem_sdiff.mp hw).1
  have hzC : z ∈ genericC0UnaryClosure v :=
    genericC0UnaryClosure_trans hwC hz
  have hwOld : w ∈ genericC0MinimalStage
      (genericC0ComponentIndex v) :=
    genericC0LowerClosure_subset_old v hw
  have hLt : genericC0ComponentIndex w <
      genericC0ComponentIndex v :=
    (genericC0ComponentIndex_lt_iff_stage w
      (genericC0ComponentIndex v)).mpr hwOld
  have hLe : genericC0ComponentIndex z ≤ genericC0ComponentIndex w :=
    ((mem_genericC0UnaryClosure_iff w z).mp hz).le
  have hzNotB : z ∉ genericC0Component
      (genericC0ComponentIndex v) := by
    intro hzB
    have hEq : genericC0ComponentIndex z =
        genericC0ComponentIndex v :=
      (genericC0ComponentIndex_eq_iff z
        (genericC0ComponentIndex v)).mpr hzB
    omega
  exact Finset.mem_sdiff.mpr ⟨hzC, hzNotB⟩

theorem genericC0LowerClosure_global (v : ℕ) :
    genericTwoSparseGraph.toPredimension.IsGloballyStrong
      (genericC0LowerClosure v) :=
  genericC0UnaryClosed_global _
    (genericC0LowerClosure_isClosed v)

/-- The old part of the unary closure is exactly its lower closure. -/
theorem genericC0UnaryClosure_inter_old (v : ℕ) :
    genericC0UnaryClosure v ∩
        genericC0MinimalStage (genericC0ComponentIndex v) =
      genericC0LowerClosure v := by
  ext w
  constructor
  · intro hw
    obtain ⟨hwC, hwOld⟩ := Finset.mem_inter.mp hw
    have hwNotB : w ∉ genericC0Component
        (genericC0ComponentIndex v) := by
      intro hwB
      exact (Finset.disjoint_left.mp
        (genericC0Component_disjoint_old
          (genericC0ComponentIndex v))) hwOld hwB
    exact Finset.mem_sdiff.mpr ⟨hwC, hwNotB⟩
  · intro hw
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hw).1,
        genericC0LowerClosure_subset_old v hw⟩

/-- The lower closure and the old prefix satisfy the no-cross
hypothesis, as each old neighbour of the new block lies in C(v). -/
theorem genericC0Local_noCross (v : ℕ) :
    genericTwoSparseGraph.NoCrossEdges
      (genericC0MinimalStage (genericC0ComponentIndex v))
      (genericC0LowerClosure v ∪
        genericC0Component (genericC0ComponentIndex v)) := by
  have hClosed : IsGenericC0UnaryClosed (genericC0UnaryClosure v) := by
    rw [← genericC0GeneratedClosure_singleton v]
    exact genericC0GeneratedClosure_isClosed ({v} : Finset ℕ)
  have hB : genericC0Component (genericC0ComponentIndex v) ⊆
      genericC0UnaryClosure v :=
    genericC0UnaryClosure_contains_component v
  have h := genericC0UnaryClosed_noCross
    (genericC0UnaryClosure v) hClosed (genericC0ComponentIndex v) hB
  rw [genericC0UnaryClosure_inter_old v] at h
  exact h

/-- Every C0 block remains a minimal strong increment over precisely
its own lower closure, with no reference to the temporary generator. -/
theorem genericC0Local_minimal (v : ℕ) :
    genericTwoSparseGraph.toPredimension.IsMinimalStrongStep
      (genericC0LowerClosure v)
      (genericC0LowerClosure v ∪
        genericC0Component (genericC0ComponentIndex v)) := by
  let i := genericC0ComponentIndex v
  have hMin :
      genericTwoSparseGraph.toPredimension.IsMinimalStrongStep
        (genericC0MinimalStage i)
        (genericC0MinimalStage i ∪ genericC0Component i) := by
    rw [← genericC0Stage_succ_eq_union i]
    exact genericC0MinimalStage_minimal_step i
  exact genericTwoSparseGraph.minimalStrongStep_local_of_noCross
    (genericC0LowerClosure v) (genericC0MinimalStage i)
    (genericC0Component i)
    (genericC0LowerClosure_subset_old v)
    (genericC0Component_disjoint_old i)
    (genericC0Local_noCross v)
    hMin

/-- Every vertex in B(v) generates the whole C(v) over the
lower closure P(v) in the intrinsic strong graph closure. -/
theorem genericC0Local_every_vertex_generates
    (v x : ℕ)
    (hx : x ∈ genericC0Component (genericC0ComponentIndex v)) :
    genericStrongClosure (insert x (genericC0LowerClosure v)) =
      genericC0UnaryClosure v := by
  have hMin := genericC0Local_minimal v
  have hGlobal :
      genericTwoSparseGraph.toPredimension.IsGloballyStrong
        (genericC0LowerClosure v ∪
          genericC0Component (genericC0ComponentIndex v)) := by
    rw [← genericC0LowerClosure_union_component v]
    exact genericC0UnaryClosure_global v
  have hxPB : x ∈ genericC0LowerClosure v ∪
      genericC0Component (genericC0ComponentIndex v) :=
    Finset.mem_union.mpr (Or.inr hx)
  have hxNotP : x ∉ genericC0LowerClosure v := by
    intro hxP
    exact (Finset.mem_sdiff.mp hxP).2 hx
  have hEq := genericStrongExhaustion.minimal_step_generated_by_every_new_vertex
    hMin hGlobal hxPB hxNotP
  change genericStrongExhaustion.closure
    (insert x (genericC0LowerClosure v)) = genericC0UnaryClosure v
  rw [genericC0LowerClosure_union_component v]
  exact hEq

/-- The local C0 component remains a minimal strong increment when
freely attached over its lower closure to any larger old finite graph
that is disjoint from the block and has no crossing edges to it. -/
theorem genericC0Local_free_amalgam_minimal
    (v : ℕ) (A : Finset ℕ)
    (hP : genericC0LowerClosure v ⊆ A)
    (hDisj : Disjoint A
      (genericC0Component (genericC0ComponentIndex v)))
    (hNo : genericTwoSparseGraph.NoCrossEdges A
      (genericC0LowerClosure v ∪
        genericC0Component (genericC0ComponentIndex v))) :
    genericTwoSparseGraph.toPredimension.IsMinimalStrongStep
      A (A ∪ genericC0Component (genericC0ComponentIndex v)) :=
  genericTwoSparseGraph.minimalStrongStep_enlarged_of_local
    (genericC0LowerClosure v) A
    (genericC0Component (genericC0ComponentIndex v))
    hP hDisj hNo (genericC0Local_minimal v)

end FiniteCatalogue
end BigHrushovski
