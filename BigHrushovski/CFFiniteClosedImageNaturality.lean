import BigHrushovski.CFFiniteSourceLevelLifting

/-!
# Complete b-values on images of finite C_F embeddings

The auxiliary unary operation b(v) contains the complete
old named support and fresh block of v. A finite map defined
only on a selected finite source which preserves these
complete values has a b-closed image, even before invoking
any countable embedding extension.

The induced image has the same complete finite-source
b-values as the source, carried exactly by the partial map.
This allows a second finite map defined only on the image
to be composed with the first while preserving all b-values.

No global map on the countable graph, total map of a finite
stage, or strict growth-class hypothesis is used.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The literal finite image of a map defined on the actual
finite source subtype, with no need to extend it. -/
noncomputable def finiteBirthSourceImage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K) :
    Finset (Vertex F K) := by
  classical
  exact (Finset.univ : Finset
    (SupportCarrier (Vertex F K) s)).image e

/-- Every image vertex comes from its exact selected source
vertex; this makes no injectivity assumption on e. -/
theorem finiteBirthSourceImage_mem
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (x : SupportCarrier (Vertex F K) s) :
    e x ∈ finiteBirthSourceImage F K s e := by
  classical
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

/-- The literal image of a finite source is closed under every
COMPLETE target b-value whenever the original finite map
preserves all complete restricted b-values ONTO their target
values. Injectivity is not needed for this closure assertion. -/
theorem finiteBirthSourceImage_bClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x)) :
    IsBirthBlockClosed F K (finiteBirthSourceImage F K s e) := by
  classical
  apply (birthBlockClosed_iff_bValue_subset F K
    (finiteBirthSourceImage F K s e)).mpr
  intro w hw
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
  rw [← hx]
  rw [← heB x]
  exact Finset.image_mono e (Finset.subset_univ _)

/-- The original finite source map, now viewed as a map INTO
the literal image subtype. No choice of a larger ambient
finite target stage is involved. -/
noncomputable def finiteBirthSourceImagePoint
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K) :
    SupportCarrier (Vertex F K) s →
      SupportCarrier (Vertex F K) (finiteBirthSourceImage F K s e) :=
  fun x => ⟨e x, finiteBirthSourceImage_mem F K s e x⟩

/-- A complete-b preserving partial source map becomes an
EXACT finite b-functional map into its own finite image
substructure: the whole source b-value maps onto the
complete image-substructure b-value.

This is equality of finite subsets of the image subtype,
not merely equality after forgetting the subtype or a
one-sided containment. -/
theorem finiteBirthSourceImage_bValue_natural
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourceBirthBValue F K s x).image
        (finiteBirthSourceImagePoint F K s e) =
      finiteSourceBirthBValue F K (finiteBirthSourceImage F K s e)
        (finiteBirthSourceImagePoint F K s e x) := by
  classical
  let t := finiteBirthSourceImage F K s e
  let j := finiteBirthSourceImagePoint F K s e
  have ht : IsBirthBlockClosed F K t :=
    finiteBirthSourceImage_bClosed F K s e heB
  apply Finset.image_injective (Subtype.val_injective :
    Function.Injective (Subtype.val :
      SupportCarrier (Vertex F K) t → Vertex F K))
  calc
    ((finiteSourceBirthBValue F K s x).image j).image
        (Subtype.val : SupportCarrier (Vertex F K) t → Vertex F K) =
      (finiteSourceBirthBValue F K s x).image e := by
        rw [Finset.image_image]
        rfl
    _ = birthBValue F K (e x) := heB x
    _ = (finiteSourceBirthBValue F K t (j x)).image
        (Subtype.val : SupportCarrier (Vertex F K) t → Vertex F K) :=
      (finiteSourceBirthBValue_image F K t ht (j x)).symm

/-- Composition of TWO genuinely partial finite maps preserves
the complete b-values whenever each map does so on its own
finite source. The second source is the literal finite image
of the first. Neither map has to extend outside its domain. -/
theorem finiteBirthSourceImage_comp_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (g : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e) → Vertex F K)
    (hgB : ∀ y : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      (finiteSourceBirthBValue F K
        (finiteBirthSourceImage F K s e) y).image g =
          birthBValue F K (g y))
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourceBirthBValue F K s x).image
        (fun y => g (finiteBirthSourceImagePoint F K s e y)) =
      birthBValue F K
        (g (finiteBirthSourceImagePoint F K s e x)) := by
  calc
    (finiteSourceBirthBValue F K s x).image
        (fun y => g (finiteBirthSourceImagePoint F K s e y)) =
      ((finiteSourceBirthBValue F K s x).image
        (finiteBirthSourceImagePoint F K s e)).image g := by
          rw [Finset.image_image]
          rfl
    _ = (finiteSourceBirthBValue F K
        (finiteBirthSourceImage F K s e)
        (finiteBirthSourceImagePoint F K s e x)).image g := by
          rw [finiteBirthSourceImage_bValue_natural F K s e heB x]
    _ = birthBValue F K
        (g (finiteBirthSourceImagePoint F K s e x)) :=
      hgB (finiteBirthSourceImagePoint F K s e x)

end CFCoherentTower
end BigHrushovski
