import BigHrushovski.C0BackEdgeEmbeddings

/-!
# Component and directed back-edge description of unary embeddings

For the fixed countable C0 closure-component presentation, consider
an injective induced graph embedding f. The unary function is
preserved exactly if and only if:

* f maps the whole component of each v **onto** the whole
  component of f(v);
* f maps the entire set of old back neighbours of each v
  **onto** the old back neighbours of f(v).

The difficult direction is from those two conditions to the
full unary closure equation f[C(v)] = C(f(v)). We prove it by
induction on back-edge ancestor paths in both directions.
At each step a directed back edge lifts through the
old-neighbour image equation, and the whole-component
equation supplies all vertices of the reached block.

This is the exact embedding equivalence in the manuscript's
C0-functional-closure lemma, for embeddings of the concrete
countable presentation. It does not identify arbitrary strong
graph embeddings with functional embeddings and does not
yet prove the functional Fraisse extension property.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- Component/back-edge data required of an induced graph embedding.
Both image equalities are ONTO, not just inclusions. -/
def IsGenericC0ComponentBackEmbedding (f : ℕ → ℕ) : Prop :=
  Function.Injective f ∧
  (∀ u v : ℕ,
    genericTwoSparseGraph.adj u v ↔
      genericTwoSparseGraph.adj (f u) (f v)) ∧
  (∀ v : ℕ,
    (genericC0Component (genericC0ComponentIndex v)).image f =
      genericC0Component (genericC0ComponentIndex (f v))) ∧
  (∀ v : ℕ,
    (genericTwoSparseGraph.oldNeighbours
      (genericC0MinimalStage (genericC0ComponentIndex v)) v).image f =
      genericTwoSparseGraph.oldNeighbours
        (genericC0MinimalStage (genericC0ComponentIndex (f v))) (f v))

/-- Following a source back-edge ancestor path gives target
closure membership for every vertex of the reached component. -/
private theorem genericC0Ancestor_image_forward
    (f : ℕ → ℕ)
    (hComp : ∀ x : ℕ,
      (genericC0Component (genericC0ComponentIndex x)).image f =
        genericC0Component (genericC0ComponentIndex (f x)))
    (hBack : ∀ x : ℕ,
      (genericTwoSparseGraph.oldNeighbours
        (genericC0MinimalStage (genericC0ComponentIndex x)) x).image f =
        genericTwoSparseGraph.oldNeighbours
          (genericC0MinimalStage (genericC0ComponentIndex (f x))) (f x))
    (v : ℕ) {j : ℕ}
    (hAnc : GenericC0Ancestor (genericC0ComponentIndex v) j) :
    ∀ w ∈ genericC0Component j, f w ∈ genericC0UnaryClosure (f v) := by
  induction hAnc with
  | root =>
      intro w hw
      have hImage :
          f w ∈ (genericC0Component (genericC0ComponentIndex v)).image f :=
        Finset.mem_image.mpr ⟨w, hw, rfl⟩
      rw [hComp v] at hImage
      exact (genericC0UnaryClosure_contains_component (f v)) hImage
  | @step j k hPrev hStep ih =>
      obtain ⟨y, hy, hyIdx⟩ := Finset.mem_image.mp hStep
      obtain ⟨x, hxB, hyBack⟩ := Finset.mem_biUnion.mp hy
      have hxCl : f x ∈ genericC0UnaryClosure (f v) :=
        ih x hxB
      have hyTarget : f y ∈ genericTwoSparseGraph.oldNeighbours
          (genericC0MinimalStage (genericC0ComponentIndex (f x)))
          (f x) := by
        rw [← hBack x]
        exact Finset.mem_image.mpr ⟨y, hyBack, rfl⟩
      have hyCl : f y ∈ genericC0UnaryClosure (f v) :=
        genericC0UnaryClosure_oldNeighbour hxCl hyTarget
      intro w hw
      have hwB :
          w ∈ genericC0Component (genericC0ComponentIndex y) := by
        rw [hyIdx]
        exact hw
      have hfwB :
          f w ∈ genericC0Component (genericC0ComponentIndex (f y)) := by
        rw [← hComp y]
        exact Finset.mem_image.mpr ⟨w, hwB, rfl⟩
      have hfwCl : f w ∈ genericC0UnaryClosure (f y) :=
        (genericC0UnaryClosure_contains_component (f y)) hfwB
      exact genericC0UnaryClosure_trans hyCl hfwCl

/-- Every vertex of a target ancestor component has a source
preimage inside the source unary closure. This is the
surjectivity half of the iterative closure argument. -/
private theorem genericC0Ancestor_image_backward
    (f : ℕ → ℕ)
    (hComp : ∀ x : ℕ,
      (genericC0Component (genericC0ComponentIndex x)).image f =
        genericC0Component (genericC0ComponentIndex (f x)))
    (hBack : ∀ x : ℕ,
      (genericTwoSparseGraph.oldNeighbours
        (genericC0MinimalStage (genericC0ComponentIndex x)) x).image f =
        genericTwoSparseGraph.oldNeighbours
          (genericC0MinimalStage (genericC0ComponentIndex (f x))) (f x))
    (v : ℕ) {j : ℕ}
    (hAnc : GenericC0Ancestor (genericC0ComponentIndex (f v)) j) :
    ∀ y ∈ genericC0Component j,
      ∃ w ∈ genericC0UnaryClosure v, f w = y := by
  induction hAnc with
  | root =>
      intro y hy
      have hImage :
          y ∈ (genericC0Component (genericC0ComponentIndex v)).image f := by
        rw [hComp v]
        exact hy
      obtain ⟨w, hwB, hfw⟩ := Finset.mem_image.mp hImage
      exact ⟨w, (genericC0UnaryClosure_contains_component v) hwB, hfw⟩
  | @step j k hPrev hStep ih =>
      obtain ⟨z, hz, hzIdx⟩ := Finset.mem_image.mp hStep
      obtain ⟨u, huB, hzBack⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨w, hwCl, hfw⟩ := ih u huB
      have huIdx : genericC0ComponentIndex u = j :=
        (genericC0ComponentIndex_eq_iff u j).mpr huB
      have hzTarget : z ∈ genericTwoSparseGraph.oldNeighbours
          (genericC0MinimalStage (genericC0ComponentIndex (f w)))
          (f w) := by
        rw [hfw, huIdx]
        exact hzBack
      have hzImage : z ∈ (genericTwoSparseGraph.oldNeighbours
          (genericC0MinimalStage (genericC0ComponentIndex w)) w).image f := by
        rw [hBack w]
        exact hzTarget
      obtain ⟨x, hxBack, hfx⟩ := Finset.mem_image.mp hzImage
      have hxCl : x ∈ genericC0UnaryClosure v :=
        genericC0UnaryClosure_oldNeighbour hwCl hxBack
      intro y hy
      have hyTarget :
          y ∈ genericC0Component (genericC0ComponentIndex (f x)) := by
        rw [hfx, hzIdx]
        exact hy
      have hyImage :
          y ∈ (genericC0Component (genericC0ComponentIndex x)).image f := by
        rw [hComp x]
        exact hyTarget
      obtain ⟨x', hx'B, hx'Image⟩ := Finset.mem_image.mp hyImage
      have hx'Cl : x' ∈ genericC0UnaryClosure x :=
        (genericC0UnaryClosure_contains_component x) hx'B
      exact ⟨x', genericC0UnaryClosure_trans hxCl hx'Cl, hx'Image⟩

/-- The two finite component/back-edge image conditions imply the
complete equality of all iterated unary closure values. -/
theorem genericC0ComponentBack_closure_image
    (f : ℕ → ℕ)
    (hComp : ∀ x : ℕ,
      (genericC0Component (genericC0ComponentIndex x)).image f =
        genericC0Component (genericC0ComponentIndex (f x)))
    (hBack : ∀ x : ℕ,
      (genericTwoSparseGraph.oldNeighbours
        (genericC0MinimalStage (genericC0ComponentIndex x)) x).image f =
        genericTwoSparseGraph.oldNeighbours
          (genericC0MinimalStage (genericC0ComponentIndex (f x))) (f x))
    (v : ℕ) :
    (genericC0UnaryClosure v).image f =
      genericC0UnaryClosure (f v) := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hy
    have hAnc : GenericC0Ancestor
        (genericC0ComponentIndex v) (genericC0ComponentIndex w) :=
      (mem_genericC0UnaryClosure_iff v w).mp hw
    have hFw : f w ∈ genericC0UnaryClosure (f v) :=
      genericC0Ancestor_image_forward f hComp hBack v hAnc w
        (genericC0ComponentIndex_mem w)
    rw [hfw] at hFw
    exact hFw
  · intro hy
    have hAnc : GenericC0Ancestor
        (genericC0ComponentIndex (f v)) (genericC0ComponentIndex y) :=
      (mem_genericC0UnaryClosure_iff (f v) y).mp hy
    obtain ⟨w, hw, hfw⟩ :=
      genericC0Ancestor_image_backward f hComp hBack v hAnc y
        (genericC0ComponentIndex_mem y)
    exact Finset.mem_image.mpr ⟨w, hw, hfw⟩

/-- Exact equivalence of the two embedding descriptions:
the unary set-valued closure language and the induced graph
with complete components and directed back-edge sets. -/
theorem genericC0UnaryEmbedding_iff_componentBack
    (f : ℕ → ℕ) :
    IsGenericC0UnaryEmbedding f ↔
      IsGenericC0ComponentBackEmbedding f := by
  constructor
  · intro hf
    exact ⟨hf.1, hf.2.1,
      genericC0UnaryEmbedding_component_image hf,
      genericC0UnaryEmbedding_oldNeighbours_image hf⟩
  · intro hf
    exact ⟨hf.1, hf.2.1,
      genericC0ComponentBack_closure_image f hf.2.2.1 hf.2.2.2⟩

end FiniteCatalogue
end BigHrushovski
