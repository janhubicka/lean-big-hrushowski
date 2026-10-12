import BigHrushovski.C0CountableMinimal
import BigHrushovski.C0StrongAge

/-!
# The countable C0 minimal enumeration starts at the empty graph

The strong closure of the empty vertex set is empty because all
finite induced subgraphs of the uncollapsed two-sparse generic have
nonnegative predimension. This pins the actual initial stage of
the certified countable minimal enumeration to the initial
condition A₀ = ∅ in the manuscript's construction.

The countable strong-chain construction and every minimal
successor step are already certified in C0CountableMinimal.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- Empty is globally self-sufficient in the concrete generic,
not just in a selected finite strong container. -/
theorem genericTwoSparseGraph_empty_global :
    genericTwoSparseGraph.toPredimension.IsGloballyStrong
      (∅ : Finset ℕ) := by
  intro b _
  refine ⟨Finset.empty_subset _, ?_⟩
  intro c _ _
  change genericTwoSparseGraph.predim ∅ ≤ genericTwoSparseGraph.predim c
  rw [genericTwoSparseGraph.predim_empty]
  exact genericTwoSparseGraph_sparse c

/-- The first stage of the certified countable minimal-increment
enumeration is the empty set, as required by the manuscript. -/
theorem genericC0MinimalStage_zero :
    genericC0MinimalStage 0 = (∅ : Finset ℕ) := by
  have hFirst :
      genericC0MinimalStage 0 =
        genericC0StrongSkeleton.stage 0 := by
    simpa [Predimension.C0Offsets.offset] using
      (genericC0MinimalStage_at_offset 0)
  rw [hFirst]
  change genericStrongExhaustion.closure ∅ = ∅
  exact genericStrongExhaustion.closure_eq_self_of_global
    genericTwoSparseGraph_empty_global

/-- The union of the finite minimal-step stages is all of ℕ:
each graph vertex appears in a finite strong prefix. -/
theorem genericC0MinimalStage_exhaustive (x : ℕ) :
    ∃ n : ℕ, x ∈ genericC0MinimalStage n :=
  genericC0MinimalStrongChain.covers x

end FiniteCatalogue
end BigHrushovski
