import BigHrushovski.CFBirthLiteralCoordinates
import BigHrushovski.CFArbitraryFiniteEmbeddingRigidity

/-!
# The fresh size of a request is intrinsic under finite embeddings

For an arbitrary finite complete-b embedding, the birth-level
preorder and the full unary value recover the *whole* target
birth block. Injectivity then preserves its cardinality.
The exact literal finite-block cardinality lemma identifies
that cardinality with the fresh-size field of the request.

This removes the fresh-size hypothesis from the pending
one-level target request-tag uniqueness argument. It does not
assume that an arbitrary map is the recursively constructed lift,
or require a map outside its finite closed source.

A second version recovers the complete b-value hypothesis from
the actual R/H language, respecting the partial domain of H.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every injective finite map with exact complete b-values and
the reflected birth-level preorder preserves the *numerical*
size of each full request block. The map need not be the
canonical finite prescribed lift. -/
theorem arbitraryFiniteEmbedding_freshSize
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heInj : Function.Injective e)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    r.code.1.val =
      (e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩).2.1.code.1.val := by
  classical
  let w : Vertex F K :=
    e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
  let B := birthBlock F K n r
  let D := selectedFiniteSet s B
  have hBsubS : B ⊆ s :=
    birthBlock_subset_closed_of_fresh F K s hs n r i hi
  have hVal : D.image
      (fun u : SupportCarrier (Vertex F K) s => u.val) = B :=
    selectedFiniteSet_image_val s B hBsubS
  have hValInj : Function.Injective
      (fun u : SupportCarrier (Vertex F K) s => u.val) := by
    intro u v huv
    exact Subtype.ext huv
  have hDCard : D.card = B.card := by
    calc
      D.card = (D.image
        (fun u : SupportCarrier (Vertex F K) s => u.val)).card :=
          (Finset.card_image_of_injective D hValInj).symm
      _ = B.card := congrArg Finset.card hVal
  have hWhole :
      D.image e = birthBlock F K w.1 w.2.1 := by
    exact (arbitraryFiniteEmbedding_support_block
      F K s e heB heLevel n r i hi).2
  have hInjCard : (D.image e).card = D.card :=
    Finset.card_image_of_injective D heInj
  calc
    r.code.1.val = B.card := (birthBlock_card F K n r).symm
    _ = D.card := hDCard.symm
    _ = (D.image e).card := hInjCard.symm
    _ = (birthBlock F K w.1 w.2.1).card :=
      congrArg Finset.card hWhole
    _ = w.2.1.code.1.val :=
      birthBlock_card F K w.1 w.2.1

/-- For a finite R/H-embedding, recover the exact *restricted*
auxiliary b-value at every original finite source vertex.
The arbitrary identity extension is used for evaluation only;
its behavior outside the finite source is not constrained. -/
theorem arbitraryFiniteRHEmbedding_completeB
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
          (∀ r ∈ t.image f, IsBirthRoot F K r)))) :
    ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x) := by
  classical
  let X : Set (Vertex F K) := {v | v ∈ s}
  let f := extendClosedSourceMap F K X e
  have hX : IsBirthBlockClosedSet F K X :=
    finiteBirthBlockClosed_as_closedSet F K s hs
  have hFull : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v) :=
    (literalClosedSource_bValues_iff_RHValues_of_canonicalOrder
      F K X hX e heInj heAdj heLevel heOrder).mpr heRH
  intro x
  have hImage :
      (finiteSourceBirthBValue F K s x).image Subtype.val =
        birthBValue F K x.val :=
    finiteSourceBirthBValue_image F K s hs x
  calc
    (finiteSourceBirthBValue F K s x).image e =
        ((finiteSourceBirthBValue F K s x).image Subtype.val).image f := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro u hu
          exact (extendClosedSourceMap_apply
            F K X e u.val u.property).symm
    _ = (birthBValue F K x.val).image f := by rw [hImage]
    _ = birthBValue F K (f x.val) := hFull x.val x.property
    _ = birthBValue F K (e x) := by
          change birthBValue F K
            (extendClosedSourceMap F K X e x.val) =
              birthBValue F K (e x)
          rw [extendClosedSourceMap_apply F K X e x.val x.property]
          rfl

/-- In the actual R/H language, every admissible finite embedding
preserves the fresh cardinality of every represented birth block.
No extra cardinality or whole-block-surjectivity hypothesis is
required in this formulation. -/
theorem arbitraryFiniteRHEmbedding_freshSize
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
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    r.code.1.val =
      (e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩).2.1.code.1.val := by
  exact arbitraryFiniteEmbedding_freshSize F K s hs e heInj
    (arbitraryFiniteRHEmbedding_completeB
      F K s hs e heInj heAdj heLevel heOrder heRH)
    heLevel n r i hi

end CFCoherentTower
end BigHrushovski
