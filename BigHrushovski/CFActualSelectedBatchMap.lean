import BigHrushovski.CFSelectedBatchImageExact
import BigHrushovski.CFActualRequestOrderTransport

/-!
# The actual simultaneous transport of selected C_F request tags

An old finite source is represented by a subset S of a source stage.
Every selected request r has its complete old support inside S, and
the earlier map f is increasing on S and induced on each support.
The literal image of every support is strictly d-closed in the target
old stage.

These finite conditions determine an actual target request T(r) and
the unique increasing isomorphism of its fresh ordinal interval.
We assemble these choices into one map of the selected old vertices
and *all* their fresh blocks at the same prescribed target level.

The request-tag map is injective by the previously verified
complete-code noncollision theorem. The fresh ordinal maps are
bijective by equality of their finite sizes. The resulting map is
injective, and its image is strictly d-closed in the whole target
level when the old image is strictly d-closed.

This does not yet discharge the graph boundary comparisons needed
for inducedness or verify the canonical order. Those steps are kept
separate from the definition of the map.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Finite hypotheses needed to transport all selected requests
over the prescribed old map. No embedding of the whole old stage
is assumed, and the selected request family may be empty. -/
structure SelectedGrowthTransport
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card))) : Prop where
  supports : ∀ r ∈ D, r.support ⊆ S
  induced : ∀ r ∈ D,
    ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔ H.adj (f p.val) (f q.val)
  closed : ∀ r ∈ D,
    H.toPredimension.IsDClosed (r.support.image f) Finset.univ

/-- Construct the actual transported target request tag for each
selected source request, with no arbitrary enumeration. -/
noncomputable def selectedGrowthTag
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D) :
    SelectedRequests G (GrowthAllowedLocal F) (fun P => K P.card) D →
      Requests H (GrowthAllowedLocal F) (fun Q => K Q.card) :=
  fun r => transportGrowthStageRequest F K G H S f hf r.val
    (h.supports r.val r.property)
    (h.induced r.val r.property)
    (h.closed r.val r.property)

/-- The actual request transport is injective on the selected
family. Equality of two target tags reflects equality of the
source's literal named request records. -/
theorem selectedGrowthTag_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D) :
    Function.Injective (selectedGrowthTag F K G H S f hf D h) := by
  intro r s hEq
  apply Subtype.ext
  exact transportGrowthStageRequest_reflects_eq
    F K G H S f hf r.val s.val
    (h.supports r.val r.property)
    (h.supports s.val s.property)
    (h.induced r.val r.property)
    (h.induced s.val s.property)
    (h.closed r.val r.property)
    (h.closed s.val s.property)
    hEq

/-- The finite ordinal map is the canonical order isomorphism
given by equality of fresh sizes. It fixes every ordinal value
and is automatically injective and surjective. -/
noncomputable def selectedGrowthOrdinalIso
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D) :
    Fin r.val.code.1.val ≃o
      Fin (selectedGrowthTag F K G H S f hf D h r).code.1.val :=
  Fin.castOrderIso
    (transportGrowthStageRequest_size F K G H S f hf
      r.val (h.supports r.val r.property)
      (h.induced r.val r.property)
      (h.closed r.val r.property)).symm

/-- Each position within a transported block retains its natural
finite ordinal, as required by the manuscript's chosen order. -/
theorem selectedGrowthOrdinalIso_val
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D)
    (i : Fin r.val.code.1.val) :
    (selectedGrowthOrdinalIso F K G H S f hf D h r i).val =
      i.val := by
  simp [selectedGrowthOrdinalIso]

/-- Map all selected old vertices and fresh blocks into the
same single target tagged level, using the actual constructed
target request tags. -/
noncomputable def selectedGrowthBatchMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D) :
    SelectedCarrier G (GrowthAllowedLocal F) (fun P => K P.card) S D →
      LevelCarrier H (GrowthAllowedLocal F) (fun Q => K Q.card) :=
  selectedTargetMap G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D f (selectedGrowthTag F K G H S f hf D h)
    (fun r i => selectedGrowthOrdinalIso F K G H S f hf D h r i)

/-- The actual simultaneous map is injective, even when its
source consists of several independent blocks at the same level.
No ordinal equality or request-tag noncollision is assumed. -/
theorem selectedGrowthBatchMap_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D) :
    Function.Injective (selectedGrowthBatchMap F K G H S f hf D h) := by
  have hfInj : Set.InjOn f S := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact False.elim ((ne_of_lt (hf ha hb hlt)) hab)
    · exact heq
    · exact False.elim ((ne_of_lt (hf hb ha hgt)) hab.symm)
  exact selectedTargetMap_injective
    G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D f hfInj
    (selectedGrowthTag F K G H S f hf D h)
    (selectedGrowthTag_injective F K G H S f hf D h)
    (fun r i => selectedGrowthOrdinalIso F K G H S f hf D h r i)
    (fun r => (selectedGrowthOrdinalIso F K G H S f hf D h r).injective)

/-- The actual finite map has strictly d-closed image in the
whole target level, if the old image is strictly d-closed.
Every selected target request's support lies in the old image
by construction. No sequential block ordering is used. -/
theorem selectedGrowthBatchMap_dClosed_full
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D)
    (hOld : H.toPredimension.IsDClosed
      (S.image f) Finset.univ) :
    (levelGraph H (GrowthAllowedLocal F)
      (fun Q => K Q.card)).toPredimension.IsDClosed
      ((Finset.univ : Finset (SelectedCarrier G
        (GrowthAllowedLocal F) (fun P => K P.card) S D)).image
        (selectedGrowthBatchMap F K G H S f hf D h))
      Finset.univ := by
  exact selectedTargetMap_dClosed_full
    G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D f hOld
    (selectedGrowthTag F K G H S f hf D h)
    (by
      intro r
      change r.val.support.image f ⊆ S.image f
      exact Finset.image_mono f (h.supports r.val r.property))
    (fun r i => selectedGrowthOrdinalIso F K G H S f hf D h r i)
    (fun r => (selectedGrowthOrdinalIso F K G H S f hf D h r).surjective)

end CFStageCatalogue
end BigHrushovski
