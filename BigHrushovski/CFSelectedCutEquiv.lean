import BigHrushovski.CFSelectedCutLevel
import BigHrushovski.CFActualSubtypeStageOrder

/-!
# The literal stage-cut carrier and its one-step partial lift

A finite b-closed source is not an abstract copy of a selected
batch. Its actual successor-stage cut is canonically identified
with the selected old cut together with the full blocks of all
selected requests. The identification keeps every old vertex
and each actual request tag and ordinal literally named.

This makes the previously verified simultaneous selected map into
a function on the actual next stage cut. Its old part agrees
pointwise with the prescribed old map; each fresh vertex is sent
to the actual constructed target request at the same ordinal.

It does not yet induct through different represented levels, or
assert uniqueness of arbitrary functional embeddings.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The finite old cut together with all whole selected blocks
on the next represented source level. -/
abbrev CutSelectedCarrier
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ) :=
  SelectedCarrier (stage F K n).graph
    (GrowthAllowedLocal F) (fun P => K P.card)
    (stageCut F K s n) (selectedRequests F K s n)

/-- The selected carrier is canonically equivalent to the *literal*
next cut of a finite b-closed source, not a renamed copy. -/
noncomputable def selectedCutEquiv
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ) :
    CutSelectedCarrier F K s n ≃
      SupportCarrier (stage F K (n + 1)).carrier
        (stageCut F K s (n + 1)) := by
  classical
  let inc : CutSelectedCarrier F K s n →
      (stage F K (n + 1)).carrier :=
    selectedSourceMap (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (stageCut F K s n) (selectedRequests F K s n)
  have hImage :
      ((Finset.univ : Finset (CutSelectedCarrier F K s n)).image inc) =
        stageCut F K s (n + 1) :=
    stageCut_succ_eq_selectedSourceImage F K s hs n
  let f : CutSelectedCarrier F K s n →
      SupportCarrier (stage F K (n + 1)).carrier
        (stageCut F K s (n + 1)) :=
    fun x => ⟨inc x, by
      rw [← hImage]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply selectedSourceMap_injective (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (stageCut F K s n) (selectedRequests F K s n)
    exact congrArg Subtype.val hxy
  · intro y
    have hy :
        y.val ∈
          (Finset.univ : Finset (CutSelectedCarrier F K s n)).image inc := by
      rw [hImage]
      exact y.property
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
    exact ⟨x, Subtype.ext hx⟩

/-- The equivalence embeds the selected carrier by its original
old/fresh tags. All names and ordinals are unchanged. -/
theorem selectedCutEquiv_val
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ)
    (x : CutSelectedCarrier F K s n) :
    (selectedCutEquiv F K s hs n x).val =
      selectedSourceMap (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card)
        (stageCut F K s n) (selectedRequests F K s n) x := by
  rfl

/-- Turn a one-level selected simultaneous map into a map defined
on every vertex of the actual next finite source cut. -/
noncomputable def selectedCutOneStepLift
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n)) :
    SupportCarrier (stage F K (n + 1)).carrier
      (stageCut F K s (n + 1)) →
      (stage F K (m + 1)).carrier := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  exact fun x =>
    selectedGrowthBatchMapSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e he
      (selectedRequests F K s n) h
      ((selectedCutEquiv F K s hs n).symm x)

/-- The induced one-level map on the literal next cut is injective,
without extending the old map outside its selected domain. -/
theorem selectedCutOneStepLift_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n)) :
    Function.Injective (selectedCutOneStepLift F K s hs n m e he h) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  intro x y hxy
  apply (selectedCutEquiv F K s hs n).symm.injective
  exact (selectedGrowthBatchMapSubtype_injective F K
    (stage F K n).graph (stage F K m).graph
    (stageCut F K s n) e he
    (selectedRequests F K s n) h) hxy

end CFCoherentTower
end BigHrushovski
