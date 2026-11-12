import BigHrushovski.CFPrescribedFiniteRHLift
import BigHrushovski.CFBlockOrdinalRigidity
import BigHrushovski.CFFinitePartialPreorderRigidity

/-!
# Rigidity of arbitrary finite C_F functional embeddings

The prescribed finite lifting theorem provides existence. For
uniqueness one must also analyse an arbitrary finite embedding,
rather than only the particular map constructed by the recursion.

This module derives three necessary intrinsic invariants under
exact complete unary values and the birth-level preorder:
the entire old support, the entire birth block, and each vertex's
literal finite ordinal in that block. The ordinal also follows
for an arbitrary finite embedding preserving the actual R/H
language and its partial domain, using the already verified
equivalence of b- and (R,H)-values.

All hypotheses are imposed on a genuine finite source subtype.
No total graph embedding or map of the complete old stages is
assumed. These are rigidity lemmas, not the uniqueness theorem:
equality of target request tags still requires comparing complete
ordered local adjacency matrices.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- A possibly noncanonical finite map preserving the complete
restricted b-value and reflecting the level preorder must map
the *whole* named old support and the *whole* fresh birth block
onto the corresponding target sets. No whole-block surjectivity
is assumed separately, and no map outside the finite source is
introduced. -/
theorem arbitraryFiniteEmbedding_support_block
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    let w := e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
    (selectedFiniteSet s (birthSupport F K n r)).image e =
        birthSupport F K w.1 w.2.1 ∧
    (selectedFiniteSet s (birthBlock F K n r)).image e =
        birthBlock F K w.1 w.2.1 := by
  let v : Vertex F K := ⟨n, ⟨r, i⟩⟩
  let w : Vertex F K := e ⟨v, hi⟩
  have hValue :
      (selectedFiniteSet s (birthBValue F K v)).image e =
        birthBValue F K w := by
    change (finiteSourceBirthBValue F K s ⟨v, hi⟩).image e =
      birthBValue F K (e ⟨v, hi⟩)
    exact heB ⟨v, hi⟩
  exact finitePartial_birthSupport_block_of_preorder
    F K s n w.1 r w.2.1 i w.2.2 hi e
    hValue rfl heLevel

/-- Extending ANY complete b-value preserving finite map by
identity outside the source transports the ambient full b-values
at all source vertices. The extension has no claimed embedding
properties outside the source. -/
theorem arbitraryFiniteEmbedding_extendedBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x)) :
    let X : Set (Vertex F K) := {v | v ∈ s}
    let f := extendClosedSourceMap F K X e
    ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v) := by
  let X : Set (Vertex F K) := {v | v ∈ s}
  let f := extendClosedSourceMap F K X e
  change ∀ v ∈ X,
    (birthBValue F K v).image f = birthBValue F K (f v)
  intro v hv
  let x : SupportCarrier (Vertex F K) s := ⟨v, hv⟩
  have hFull :
      (finiteSourceBirthBValue F K s x).image Subtype.val =
        birthBValue F K v :=
    finiteSourceBirthBValue_image F K s hs x
  calc
    (birthBValue F K v).image f =
        ((finiteSourceBirthBValue F K s x).image Subtype.val).image f := by
          rw [hFull]
    _ = (finiteSourceBirthBValue F K s x).image e := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro u hu
          exact extendClosedSourceMap_apply F K X e u.val u.property
    _ = birthBValue F K (e x) := heB x
    _ = birthBValue F K (f v) := by
          change birthBValue F K (e x) =
            birthBValue F K (extendClosedSourceMap F K X e v)
          rw [extendClosedSourceMap_apply F K X e v hv]

/-- Every admissible finite embedding of a b-closed C_F source
preserves the exact ordinal within each full birth block.
The embedding need not be the prescribed map. No full graph
inducedness or injectivity is needed in addition to the stated
complete b-value and order/level conditions. -/
theorem arbitraryFiniteEmbedding_birthOrdinal
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (x : SupportCarrier (Vertex F K) s) :
    birthOrdinal F K (e x) = birthOrdinal F K x.val := by
  let X : Set (Vertex F K) := {v | v ∈ s}
  let f := extendClosedSourceMap F K X e
  have hX : IsBirthBlockClosedSet F K X :=
    finiteBirthBlockClosed_as_closedSet F K s hs
  have hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v) :=
    arbitraryFiniteEmbedding_extendedBValues F K s hs e heB
  have hOn : ∀ v : Vertex F K, (hv : v ∈ X) →
      f v = e ⟨v, hv⟩ := by
    intro v hv
    exact extendClosedSourceMap_apply F K X e v hv
  have hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔
        BirthLevelLe F K (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heLevel ⟨u, hu⟩ ⟨v, hv⟩)
  have hOrder : ∀ u ∈ X, ∀ v ∈ X,
      canonicalBirthLt F K u v ↔
        canonicalBirthLt F K (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heOrder ⟨u, hu⟩ ⟨v, hv⟩)
  have hOrdinal :=
    birthOrdinal_image_on_closedSet_of_canonicalOrder
      F K X hX f hB hLevel hOrder x.val x.property
  simpa only [hOn x.val x.property] using hOrdinal

/-- The ordinal conclusion also holds when the finite embedding
is specified by the actual R(v), defined H(S), and reflected H
domain instead of the auxiliary b-values. This provides a
uniqueness invariant directly in the manuscript language. -/
theorem arbitraryFiniteRHEmbedding_birthOrdinal
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (heRH :
      let X : Set (Vertex F K) := {v | v ∈ s}
      let f := extendClosedSourceMap F K X e
      (∀ v ∈ X,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ t : Finset (Vertex F K),
        (∀ v ∈ t, v ∈ X) →
        (∀ r ∈ t, IsBirthRoot F K r) →
        (birthDClosedHull F K t).image f =
          birthDClosedHull F K (t.image f)) ∧
      (∀ t : Finset (Vertex F K),
        (∀ v ∈ t, v ∈ X) →
        ((∀ r ∈ t, IsBirthRoot F K r) ↔
          (∀ r ∈ t.image f, IsBirthRoot F K r))))
    (x : SupportCarrier (Vertex F K) s) :
    birthOrdinal F K (e x) = birthOrdinal F K x.val := by
  let X : Set (Vertex F K) := {v | v ∈ s}
  let f := extendClosedSourceMap F K X e
  have hX : IsBirthBlockClosedSet F K X :=
    finiteBirthBlockClosed_as_closedSet F K s hs
  have hOn : ∀ v : Vertex F K, (hv : v ∈ X) →
      f v = e ⟨v, hv⟩ := by
    intro v hv
    exact extendClosedSourceMap_apply F K X e v hv
  have hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔
        BirthLevelLe F K (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heLevel ⟨u, hu⟩ ⟨v, hv⟩)
  have hOrder : ∀ u ∈ X, ∀ v ∈ X,
      canonicalBirthLt F K u v ↔
        canonicalBirthLt F K (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heOrder ⟨u, hu⟩ ⟨v, hv⟩)
  have hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v) :=
    (literalClosedSource_bValues_iff_RHValues_of_canonicalOrder
      F K X hX e heInj heAdj heLevel heOrder).mpr heRH
  have hOrdinal :=
    birthOrdinal_image_on_closedSet_of_canonicalOrder
      F K X hX f hB hLevel hOrder x.val x.property
  simpa only [hOn x.val x.property] using hOrdinal

end CFCoherentTower
end BigHrushovski
