import BigHrushovski.CFClosedSubtypeEmbeddings

/-!
# The chosen order and finite birth-block roots

The C_F manuscript orders request blocks and their vertices. Its
root-recovery argument needs only one local property of the chosen
strict order: on the vertices of *one* request block, that order
is exactly the chosen Fin-ordinal order of the local code.

We separate this property from the arbitrary ordering of different
request blocks. It is enough to derive first-root preservation from
the ordinary order-preservation assumption on an embedding.

The resulting b/(R,H) value-equivalence theorem uses a literal map
from any (possibly empty or infinite) closed source subtype,
preserves the chosen strict order on that source, and has no separate
assumption about how the map acts on internal block ordinals.

To identify this theorem with the particular manuscript order,
one must construct that order on the actual birth carrier and
verify its local compatibility. This module does not pretend
that choosing an arbitrary unrelated order suffices.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The only property of the chosen strict order needed for
root recovery: its restriction to each complete tagged fresh
block is the order of the finite fresh ordinals. -/
def BirthBlockOrderCompatible
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (lt : Vertex F K → Vertex F K → Prop) : Prop :=
  ∀ v u w : Vertex F K,
    u ∈ birthBlockOf F K v →
    w ∈ birthBlockOf F K v →
    (lt u w ↔ birthOrdinal F K u < birthOrdinal F K w)

/-- Complete b-values and the reflected level preorder identify
entire blocks. If the map also preserves a strict relation which
agrees with the chosen finite order on each block, it preserves
that internal ordinal order. No totality or inter-block comparison
is used. -/
theorem preservesBirthBlockOrderOn_of_compatibleOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (lt : Vertex F K → Vertex F K → Prop)
    (hCompat : BirthBlockOrderCompatible F K lt)
    (hOrder : ∀ u ∈ X, ∀ v ∈ X,
      lt u v ↔ lt (f u) (f v)) :
    PreservesBirthBlockOrderOn F K X f := by
  classical
  intro v hv u w huB hwB huOrdW
  have hCsubX : ∀ z ∈ birthCValue F K v, z ∈ X :=
    generatedClosure_subset_closedSet F K X hX
      ({v} : Finset (Vertex F K)) (by
        intro z hz
        have hzv : z = v := by simpa using hz
        subst z
        exact hv)
  have huX : u ∈ X :=
    hCsubX u ((birthBlockOf_mem_iff F K v u).mp huB).1
  have hwX : w ∈ X :=
    hCsubX w ((birthBlockOf_mem_iff F K v w).mp hwB).1
  have hWhole :
      (birthBlockOf F K v).image f = birthBlockOf F K (f v) :=
    birthBlockOf_image_on_closedSet F K X hX f hB hLevel v hv
  have hfu : f u ∈ birthBlockOf F K (f v) := by
    rw [← hWhole]
    exact Finset.mem_image.mpr ⟨u, huB, rfl⟩
  have hfw : f w ∈ birthBlockOf F K (f v) := by
    rw [← hWhole]
    exact Finset.mem_image.mpr ⟨w, hwB, rfl⟩
  have hltSource : lt u w :=
    (hCompat v u w huB hwB).mpr huOrdW
  have hltImage : lt (f u) (f w) :=
    (hOrder u huX w hwX).mp hltSource
  exact (hCompat (f v) (f u) (f w) hfu hfw).mp hltImage

/-- Complete b- and (R,H)-values have the same embeddings on
arbitrary b-closed source subsets whenever the embedding
preserves the chosen strict order and that order agrees with
the finite local codes inside each birth block.

The internal ordinal hypothesis of the earlier theorem is
*derived*, not independently assumed. -/
theorem bValues_iff_RHValues_on_closedSet_of_chosenOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (lt : Vertex F K → Vertex F K → Prop)
    (hCompat : BirthBlockOrderCompatible F K lt)
    (hOrder : ∀ u ∈ X, ∀ v ∈ X,
      lt u v ↔ lt (f u) (f v)) :
    (∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v)) ↔
      (∀ v ∈ X,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        (∀ r ∈ s, IsBirthRoot F K r) →
        (birthDClosedHull F K s).image f =
          birthDClosedHull F K (s.image f)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        ((∀ r ∈ s, IsBirthRoot F K r) ↔
          (∀ r ∈ s.image f, IsBirthRoot F K r))) := by
  constructor
  · intro hB
    have hInternal : PreservesBirthBlockOrderOn F K X f :=
      preservesBirthBlockOrderOn_of_compatibleOrder
        F K X hX f hB hLevel lt hCompat hOrder
    exact (bValues_iff_RHValues_on_closedSet
      F K X hX f hf hAdj hLevel hInternal).mp hB
  · rintro ⟨hR, hH, _⟩
    exact RHValues_imply_bValues_on_closedSet
      F K X hX f hf hAdj hLevel hR hH

/-- Literal source-subtype form with the chosen order.
Only adjacency, the level preorder and the chosen order
are assumed preserved on the subtype. Its empty case is
included, as in the underlying literal-embedding theorem.

This eliminates an artificial *additional* requirement on an
embedding to preserve the fresh ordinal order separately.
The chosen order's agreement with that ordinal order is an
intrinsic property of the presentation, not of the embedding. -/
theorem literalClosedSource_bValues_iff_RHValues_of_chosenOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (lt : Vertex F K → Vertex F K → Prop)
    (hCompat : BirthBlockOrderCompatible F K lt)
    (e : {v : Vertex F K // v ∈ X} → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ u v : {v : Vertex F K // v ∈ X},
      (countableGraph F K).adj u.val v.val ↔
        (countableGraph F K).adj (e u) (e v))
    (heLevel : ∀ u v : {v : Vertex F K // v ∈ X},
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (e u) (e v))
    (heOrder : ∀ u v : {v : Vertex F K // v ∈ X},
      lt u.val v.val ↔ lt (e u) (e v)) :
    let f := extendClosedSourceMap F K X e
    (∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v)) ↔
      (∀ v ∈ X,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        (∀ r ∈ s, IsBirthRoot F K r) →
        (birthDClosedHull F K s).image f =
          birthDClosedHull F K (s.image f)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        ((∀ r ∈ s, IsBirthRoot F K r) ↔
          (∀ r ∈ s.image f, IsBirthRoot F K r))) := by
  let f := extendClosedSourceMap F K X e
  have hOn : ∀ v : Vertex F K, (hv : v ∈ X) →
      f v = e ⟨v, hv⟩ := by
    intro v hv
    exact extendClosedSourceMap_apply F K X e v hv
  have hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v := by
    intro u hu v hv huv
    rw [hOn u hu, hOn v hv] at huv
    exact congrArg Subtype.val (heInj huv)
  have hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heAdj (⟨u, hu⟩ : {w : Vertex F K // w ∈ X})
        (⟨v, hv⟩ : {w : Vertex F K // w ∈ X}))
  have hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heLevel (⟨u, hu⟩ : {w : Vertex F K // w ∈ X})
        (⟨v, hv⟩ : {w : Vertex F K // w ∈ X}))
  have hOrder : ∀ u ∈ X, ∀ v ∈ X,
      lt u v ↔ lt (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heOrder (⟨u, hu⟩ : {w : Vertex F K // w ∈ X})
        (⟨v, hv⟩ : {w : Vertex F K // w ∈ X}))
  exact bValues_iff_RHValues_on_closedSet_of_chosenOrder
    F K X hX f hf hAdj hLevel lt hCompat hOrder

end CFCoherentTower
end BigHrushovski
