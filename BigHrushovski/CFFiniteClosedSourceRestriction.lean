import BigHrushovski.CFPrescribedFiniteOrderedLift

/-!
# Restricting finite C_F embeddings to closed finite substructures

For the finite unique level-lifting lemma, one needs more than
pointwise restriction of a function. When a finite b-closed source s
is contained in another finite b-closed source t, the complete
source b-value computed in s must agree, after inclusion, with
the complete source b-value computed in t.

This follows from the common complete ambient birth-b-value of
each vertex. It is an exact equality of finite sets, and does
not require a total map on the countable birth carrier.

A strictly increasing level assignment on the levels represented
in t restricts to one on s. The two facts are the preparation for
using finite uniqueness to prove compatibility under restrictions.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The literal inclusion of one finite source into another.
The input may be empty; no vertex of the target is chosen. -/
def finiteClosedSourceInclusion
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K)) (hst : s ⊆ t) :
    SupportCarrier (Vertex F K) s →
      SupportCarrier (Vertex F K) t :=
  fun x => ⟨x.val, hst x.property⟩

/-- The inclusion is injective simply because it retains the
literal original birth vertex. -/
theorem finiteClosedSourceInclusion_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K)) (hst : s ⊆ t) :
    Function.Injective (finiteClosedSourceInclusion F K s t hst) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : SupportCarrier (Vertex F K) t => z.val) hxy

/-- Complete finite-source b-values are natural under literal
inclusion of two b-closed finite sources: no extra elements
are gained by computing the same unary value in a larger
finite source. This is equality, not just inclusion. -/
theorem finiteSourceBirthBValue_inclusion
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (ht : IsBirthBlockClosed F K t)
    (hst : s ⊆ t)
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourceBirthBValue F K s x).image
        (finiteClosedSourceInclusion F K s t hst) =
      finiteSourceBirthBValue F K t
        (finiteClosedSourceInclusion F K s t hst x) := by
  classical
  let incl := finiteClosedSourceInclusion F K s t hst
  apply Finset.image_injective (Subtype.val_injective :
    Function.Injective (Subtype.val :
      SupportCarrier (Vertex F K) t → Vertex F K))
  calc
    ((finiteSourceBirthBValue F K s x).image incl).image
        (Subtype.val : SupportCarrier (Vertex F K) t → Vertex F K) =
      (finiteSourceBirthBValue F K s x).image Subtype.val := by
        rw [Finset.image_image]
        rfl
    _ = birthBValue F K x.val :=
      finiteSourceBirthBValue_image F K s hs x
    _ = (finiteSourceBirthBValue F K t (incl x)).image
        (Subtype.val : SupportCarrier (Vertex F K) t → Vertex F K) :=
      (finiteSourceBirthBValue_image F K t ht (incl x)).symm

/-- Restriction of ANY complete-b preserving map on t is
complete-b preserving on the smaller b-closed source s.
The restriction is defined only where the original finite map
was defined; no ambient total extension is assumed. -/
theorem finiteSourceBirthBValue_restriction
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (ht : IsBirthBlockClosed F K t)
    (hst : s ⊆ t)
    (e : SupportCarrier (Vertex F K) t → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) t,
      (finiteSourceBirthBValue F K t x).image e =
        birthBValue F K (e x))
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourceBirthBValue F K s x).image
        (fun y => e (finiteClosedSourceInclusion F K s t hst y)) =
      birthBValue F K
        (e (finiteClosedSourceInclusion F K s t hst x)) := by
  calc
    (finiteSourceBirthBValue F K s x).image
        (fun y => e (finiteClosedSourceInclusion F K s t hst y)) =
      ((finiteSourceBirthBValue F K s x).image
        (finiteClosedSourceInclusion F K s t hst)).image e := by
          rw [Finset.image_image]
          rfl
    _ = (finiteSourceBirthBValue F K t
        (finiteClosedSourceInclusion F K s t hst x)).image e := by
          rw [finiteSourceBirthBValue_inclusion F K s t hs ht hst x]
    _ = birthBValue F K
        (e (finiteClosedSourceInclusion F K s t hst x)) :=
          heB (finiteClosedSourceInclusion F K s t hst x)

/-- A level assignment strictly increasing on the levels actually
represented in t is also strictly increasing on those represented
in s ⊆ t. No condition on unused levels is introduced. -/
theorem strictOnRepresented_of_subset
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K)) (hst : s ⊆ t)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K t level) :
    StrictOnRepresented F K s level := by
  intro n hn m hm hnm
  apply hStrict n ?_ m ?_ hnm
  · obtain ⟨v, hv, hvn⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨v, hst hv, hvn⟩
  · obtain ⟨v, hv, hvm⟩ := Finset.mem_image.mp hm
    exact Finset.mem_image.mpr ⟨v, hst hv, hvm⟩

end CFCoherentTower
end BigHrushovski
