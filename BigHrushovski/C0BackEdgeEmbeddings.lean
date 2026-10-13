import BigHrushovski.C0UnaryEmbeddings
import BigHrushovski.C0Neighbours

/-!
# Directed back edges under C0 unary functional embeddings

The undirected graph has no intrinsically oriented edges. Relative
to the fixed enumeration, an edge v--w is a back edge at v when
the component of w is earlier than that of v. Such an edge can be
recognized by three conditions: adjacency, membership of w in
the unary closure C(v), and distinct component indices.

This characterization shows that a genuine unary-functional
embedding maps every old-neighbour set exactly onto the
corresponding target old-neighbour set. It is the forward
direction of the component/back-edge description of embeddings.

The reverse implication, recovering the complete unary
closure from component and back-neighbour images, remains
a separate induction over decreasing component indices.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- A genuine earlier back edge is exactly an adjacent closure
point in a component distinct from the source's component. -/
theorem genericC0BackNeighbour_iff (v w : ℕ) :
    w ∈ genericTwoSparseGraph.oldNeighbours
      (genericC0MinimalStage (genericC0ComponentIndex v)) v ↔
      genericTwoSparseGraph.adj v w ∧
      w ∈ genericC0UnaryClosure v ∧
      genericC0ComponentIndex w ≠ genericC0ComponentIndex v := by
  constructor
  · intro hw
    have hpair := (genericTwoSparseGraph.mem_oldNeighbours_iff
      (genericC0MinimalStage (genericC0ComponentIndex v)) v w).mp hw
    have hlt := (genericC0ComponentIndex_lt_iff_stage w
      (genericC0ComponentIndex v)).mpr hpair.1
    refine ⟨hpair.2, ?_, by omega⟩
    exact genericC0UnaryClosure_oldNeighbour
      (genericC0UnaryClosure_self v) hw
  · rintro ⟨hadj, hcl, hne⟩
    have hle : genericC0ComponentIndex w ≤
        genericC0ComponentIndex v :=
      ((mem_genericC0UnaryClosure_iff v w).mp hcl).le
    have hlt : genericC0ComponentIndex w <
        genericC0ComponentIndex v := by omega
    have hstage : w ∈
        genericC0MinimalStage (genericC0ComponentIndex v) :=
      (genericC0ComponentIndex_lt_iff_stage w
        (genericC0ComponentIndex v)).mp hlt
    exact (genericTwoSparseGraph.mem_oldNeighbours_iff
      (genericC0MinimalStage (genericC0ComponentIndex v)) v w).mpr
      ⟨hstage, hadj⟩

/-- Directed back-edge incidence is preserved and reflected. -/
theorem genericC0UnaryEmbedding_backNeighbour_iff
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (v w : ℕ) :
    w ∈ genericTwoSparseGraph.oldNeighbours
      (genericC0MinimalStage (genericC0ComponentIndex v)) v ↔
    f w ∈ genericTwoSparseGraph.oldNeighbours
      (genericC0MinimalStage (genericC0ComponentIndex (f v))) (f v) := by
  constructor
  · intro hw
    obtain ⟨hadj, hcl, hne⟩ :=
      (genericC0BackNeighbour_iff v w).mp hw
    have hne' :
        genericC0ComponentIndex (f w) ≠
          genericC0ComponentIndex (f v) := by
      intro heq
      have heq' : genericC0ComponentIndex v =
          genericC0ComponentIndex w :=
        (genericC0UnaryEmbedding_component_eq_iff hf v w).mpr heq.symm
      exact hne heq'.symm
    exact (genericC0BackNeighbour_iff (f v) (f w)).mpr
      ⟨(hf.2.1 v w).mp hadj,
       (genericC0UnaryEmbedding_mem_iff hf v w).mp hcl,
       hne'⟩
  · intro hw
    obtain ⟨hadj, hcl, hne⟩ :=
      (genericC0BackNeighbour_iff (f v) (f w)).mp hw
    have hne' :
        genericC0ComponentIndex w ≠
          genericC0ComponentIndex v := by
      intro heq
      have heq' : genericC0ComponentIndex (f w) =
          genericC0ComponentIndex (f v) :=
        (genericC0UnaryEmbedding_component_eq_iff hf w v).mp heq
      exact hne heq'
    exact (genericC0BackNeighbour_iff v w).mpr
      ⟨(hf.2.1 v w).mpr hadj,
       (genericC0UnaryEmbedding_mem_iff hf v w).mpr hcl,
       hne'⟩

/-- The image of the complete old-neighbour set is precisely the
target old-neighbour set, including its vertices outside the
source's original component. -/
theorem genericC0UnaryEmbedding_oldNeighbours_image
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (v : ℕ) :
    (genericTwoSparseGraph.oldNeighbours
      (genericC0MinimalStage (genericC0ComponentIndex v)) v).image f =
    genericTwoSparseGraph.oldNeighbours
      (genericC0MinimalStage (genericC0ComponentIndex (f v))) (f v) := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hy
    have hTarget :=
      (genericC0UnaryEmbedding_backNeighbour_iff hf v w).mp hw
    rw [hfw] at hTarget
    exact hTarget
  · intro hy
    have hCl : y ∈ genericC0UnaryClosure (f v) :=
      genericC0UnaryClosure_oldNeighbour
        (genericC0UnaryClosure_self (f v)) hy
    have hVal := hf.2.2 v
    have hImage : y ∈ (genericC0UnaryClosure v).image f := by
      rw [hVal]
      exact hCl
    obtain ⟨w, _, hfw⟩ := Finset.mem_image.mp hImage
    have hTarget : f w ∈ genericTwoSparseGraph.oldNeighbours
        (genericC0MinimalStage (genericC0ComponentIndex (f v)))
        (f v) := by
      rw [hfw]
      exact hy
    have hSource :=
      (genericC0UnaryEmbedding_backNeighbour_iff hf v w).mpr hTarget
    exact Finset.mem_image.mpr ⟨w, hSource, hfw⟩

end FiniteCatalogue
end BigHrushovski
