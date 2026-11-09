import BigHrushovski.FiniteBlockSupportSubtype
import BigHrushovski.CFBirthBlockSupportRigidity
import BigHrushovski.CFBirthBValues

/-!
# Exact named C_F supports under finite closed-source embeddings

The big Hrushovski finite unique level-lifting lemma concerns embeddings
of a finite b-closed source, not maps of the entire countable carrier.
Here the complete old support and entire fresh block of every source
vertex are represented inside the literal finite selected subtype.

An injective map of that subtype that preserves the WHOLE auxiliary
birth b-value and maps the WHOLE fresh block onto a target fresh
block must consequently send the old named support onto the
corresponding literal target support. No extension to a global
injective function or an arbitrary isomorphic graph copy is used.

This is the support-recovery step of intrinsic uniqueness. Fresh
size, full ordered adjacency code and ordinal-position rigidity
are separate inputs already available in the request catalogue.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- A finite b-closed source contains the entire literal old
support of each fresh block it meets. -/
theorem birthSupport_subset_finiteClosedSource
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    birthSupport F K n r ⊆ s := by
  have hValue := birthBValue_subset_of_closed F K s hs hi
  intro v hv
  apply hValue
  exact Finset.mem_union.mpr (Or.inl hv)

/-- The selected subtype represents every actual support vertex,
not merely a subset or an isomorphic copy. -/
theorem birthSupport_selectedFiniteSource_exact
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    (selectedFiniteSet s (birthSupport F K n r)).image
        (fun v : {w : Vertex F K // w ∈ s} => v.val) =
      birthSupport F K n r := by
  exact selectedFiniteSet_image_val s (birthSupport F K n r)
    (birthSupport_subset_finiteClosedSource F K s hs n r i hi)

/-- The selected subtype also represents EVERY ordinal of the
whole fresh block of any source vertex. -/
theorem birthBlock_selectedFiniteSource_exact
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    (selectedFiniteSet s (birthBlock F K n r)).image
        (fun v : {w : Vertex F K // w ∈ s} => v.val) =
      birthBlock F K n r := by
  exact selectedFiniteSet_image_val s (birthBlock F K n r)
    (birthBlock_subset_closed_of_fresh F K s hs n r i hi)

/-- The named old support of a source fresh block is forced by
a GENUINELY PARTIAL finite closed-source injection. Its complete
b-value must be transported ONTO the target complete b-value,
and its WHOLE fresh block onto the corresponding target block.

The map is defined only on the selected subtype of s. -/
theorem birthSupport_image_of_finiteClosedSource
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (r : BirthRequest F K n)
    (t : BirthRequest F K m)
    (i : Fin r.code.1.val)
    (j : Fin t.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s)
    (e : {v : Vertex F K // v ∈ s} → Vertex F K)
    (he : Function.Injective e)
    (hValue :
      (selectedFiniteSet s (birthBValue F K
        (⟨n, ⟨r, i⟩⟩ : Vertex F K))).image e =
      birthBValue F K (⟨m, ⟨t, j⟩⟩ : Vertex F K))
    (hBlock :
      (selectedFiniteSet s (birthBlock F K n r)).image e =
        birthBlock F K m t) :
    (selectedFiniteSet s (birthSupport F K n r)).image e =
      birthSupport F K m t := by
  have hFull :
      (selectedFiniteSet s
        (birthSupport F K n r ∪ birthBlock F K n r)).image e =
      birthSupport F K m t ∪ birthBlock F K m t := by
    simpa only [birthBValue_of_fresh] using hValue
  exact completeBlock_supportImage_partial
    s (birthSupport F K n r) (birthBlock F K n r)
    (birthSupport F K m t) (birthBlock F K m t)
    e he
    (birthSupport_disjoint_birthBlock F K n r)
    (birthSupport_disjoint_birthBlock F K m t)
    hFull hBlock

end CFCoherentTower
end BigHrushovski
