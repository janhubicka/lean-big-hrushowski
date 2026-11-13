import BigHrushovski.HrushovskiEllentuckCoherentStageGluing

/-!
# Restriction and stagewise uniqueness of finite C_F b-embeddings

A genuine ordered finite b-embedding of a finite source remains an
embedding upon restriction to a finite b-closed subset. The closure
hypothesis matters: every complete auxiliary b-value of a retained
source vertex must already be present in the smaller source.

Consequently uniqueness on complete one-generated closures
already forces uniqueness on an arbitrary literal finite
birth stage. This removes the need for an additional independent
stagewise uniqueness assumption in the countable lifting argument.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue

/-- The restricted finite b-value has the full ambient image whenever
the ambient b-value is contained in the chosen finite source. This
requires no closure of the *whole* source. -/
theorem finiteSourceBValue_image_of_subset
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (t : Finset (Vertex F K))
    (x : SupportCarrier (Vertex F K) t)
    (hB : birthBValue F K x.val ⊆ t) :
    (finiteSourceBirthBValue F K t x).image Subtype.val =
      birthBValue F K x.val := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨y, hy, hwy⟩ := Finset.mem_image.mp hw
    have hyB : y.val ∈ birthBValue F K x.val := by
      simpa [finiteSourceBirthBValue] using hy
    exact hwy ▸ hyB
  · intro hw
    refine Finset.mem_image.mpr
      ⟨⟨w, hB hw⟩, ?_, rfl⟩
    simpa [finiteSourceBirthBValue] using hw

/-- A finite complete b-closed source has the same restricted
unary values in every larger finite source, after the literal
subtype inclusion. In particular a larger source need not
itself be b-closed. -/
theorem finiteSourceBValue_restrict
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (hst : s ⊆ t)
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourceBirthBValue F K s x).image
      (fun y : SupportCarrier (Vertex F K) s =>
        (⟨y.val, hst y.property⟩ : SupportCarrier (Vertex F K) t)) =
      finiteSourceBirthBValue F K t
        ⟨x.val, hst x.property⟩ := by
  classical
  have hBsub : birthBValue F K x.val ⊆ t :=
    (birthBValue_subset_of_closed F K s hs x.property).trans hst
  apply Finset.image_injective (Subtype.val_injective)
  calc
    ((finiteSourceBirthBValue F K s x).image
        (fun y : SupportCarrier (Vertex F K) s =>
          (⟨y.val, hst y.property⟩ : SupportCarrier (Vertex F K) t))).image
          Subtype.val =
      (finiteSourceBirthBValue F K s x).image Subtype.val := by
        rw [Finset.image_image]
        rfl
    _ = birthBValue F K x.val :=
      finiteSourceBirthBValue_image F K s hs x
    _ = (finiteSourceBirthBValue F K t
        ⟨x.val, hst x.property⟩).image Subtype.val :=
      (finiteSourceBValue_image_of_subset F K t
        ⟨x.val, hst x.property⟩ hBsub).symm

/-- Restriction of a genuine finite ordered b-embedding to a
smaller b-closed source is still an exact ordered b-embedding.
In particular the full b-value, not merely its intersection
with the smaller source, is transported onto the target value. -/
theorem finiteOrderedBEmbedding_restrict
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (hst : s ⊆ t)
    (e : SupportCarrier (Vertex F K) t → Vertex F K)
    (he : IsFiniteOrderedBEmbedding F K t e) :
    IsFiniteOrderedBEmbedding F K s
      (fun x : SupportCarrier (Vertex F K) s =>
        e ⟨x.val, hst x.property⟩) := by
  classical
  obtain ⟨heInj, heAdj, heB, heLevel, heOrder⟩ := he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hxy' :
        (⟨x.val, hst x.property⟩ : SupportCarrier (Vertex F K) t) =
          ⟨y.val, hst y.property⟩ := heInj hxy
    exact Subtype.ext (congrArg
      (fun z : SupportCarrier (Vertex F K) t => z.val) hxy')
  · intro x y
    exact heAdj ⟨x.val, hst x.property⟩
      ⟨y.val, hst y.property⟩
  · intro x
    change
      (finiteSourceBirthBValue F K s x).image
        (fun y : SupportCarrier (Vertex F K) s =>
          e ⟨y.val, hst y.property⟩) =
        birthBValue F K (e ⟨x.val, hst x.property⟩)
    calc
      (finiteSourceBirthBValue F K s x).image
          (fun y : SupportCarrier (Vertex F K) s =>
            e ⟨y.val, hst y.property⟩) =
        ((finiteSourceBirthBValue F K s x).image
          (fun y : SupportCarrier (Vertex F K) s =>
            (⟨y.val, hst y.property⟩ : SupportCarrier (Vertex F K) t))).image
              e := by rw [Finset.image_image]; rfl
      _ = (finiteSourceBirthBValue F K t
          ⟨x.val, hst x.property⟩).image e := by
            rw [finiteSourceBValue_restrict F K s t hs hst x]
      _ = birthBValue F K (e ⟨x.val, hst x.property⟩) :=
        heB ⟨x.val, hst x.property⟩
  · intro x y
    exact heLevel ⟨x.val, hst x.property⟩
      ⟨y.val, hst y.property⟩
  · intro x y
    exact heOrder ⟨x.val, hst x.property⟩
      ⟨y.val, hst y.property⟩

/-- Uniqueness on all complete one-generated closures already implies
uniqueness on each literal finite birth stage. The proof restricts
the two competing finite embeddings to the full generated closure
of each stage vertex, which is still contained in that stage. -/
theorem finiteStage_uniqueness_of_singleton_uniqueness
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hUnique :
      ∀ v : Vertex F K,
        ∀ (g k : SupportCarrier (Vertex F K)
            (birthSingletonClosure F K v) → Vertex F K),
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) g →
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) k →
          (∀ x, (g x).1 = (k x).1) →
          g = k)
    (n : ℕ)
    (e g : SupportCarrier (Vertex F K)
      (stageImage F K n) → Vertex F K)
    (he : IsFiniteOrderedBEmbedding F K (stageImage F K n) e)
    (hg : IsFiniteOrderedBEmbedding F K (stageImage F K n) g)
    (hLevel : ∀ x, (e x).1 = (g x).1) :
    e = g := by
  classical
  funext x
  let s := birthSingletonClosure F K x.val
  have hs : IsBirthBlockClosed F K s :=
    birthGeneratedClosure_closed F K ({x.val} : Finset (Vertex F K))
  have hst : s ⊆ stageImage F K n :=
    birthGeneratedClosure_le_of_closed F K
      ({x.val} : Finset (Vertex F K)) (stageImage F K n)
      (by simpa using x.property) (stageImage_birthBlockClosed F K n)
  let e' : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun y => e ⟨y.val, hst y.property⟩
  let g' : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun y => g ⟨y.val, hst y.property⟩
  have he' : IsFiniteOrderedBEmbedding F K s e' :=
    finiteOrderedBEmbedding_restrict F K s (stageImage F K n)
      hs hst e he
  have hg' : IsFiniteOrderedBEmbedding F K s g' :=
    finiteOrderedBEmbedding_restrict F K s (stageImage F K n)
      hs hst g hg
  have hEq : e' = g' :=
    hUnique x.val e' g' he' hg' (by
      intro y
      exact hLevel ⟨y.val, hst y.property⟩)
  have hx : x.val ∈ s := birthSingletonClosure_self F K x.val
  have hAt : e ⟨x.val, hst hx⟩ = g ⟨x.val, hst hx⟩ := by
    exact congrFun hEq ⟨x.val, hx⟩
  have hxEq : (⟨x.val, hst hx⟩ :
      SupportCarrier (Vertex F K) (stageImage F K n)) = x :=
    Subtype.ext rfl
  rw [hxEq] at hAt
  exact hAt

end BigHrushovski.CFCoherentTower
