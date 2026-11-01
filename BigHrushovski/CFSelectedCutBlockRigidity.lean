import BigHrushovski.CFSelectedCutEmbedding

/-!
# Pointwise old-block and fresh-tag rigidity of a literal C_F cut lift

The canonical one-step map on the *actual* successor source cut
restricts pointwise to the prescribed old embedding. Every fresh
vertex is sent to the canonical target request determined by
its old support and full ordered local graph code, at the same
finite ordinal.

The final theorem identifies any other map with this canonical
one when it agrees on the complete old and fresh data. It does
not assert that an arbitrary functional embedding automatically
satisfies these data: that is the remaining intrinsic uniqueness
argument in the represented-level induction.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The one-step map of an actual next cut restricts exactly to
the prescribed old-source embedding. -/
theorem selectedCutOneStepLift_old
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n))
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    selectedCutOneStepLift F K s hs n m e he h
        (selectedCutEquiv F K s hs n (Sum.inl u)) =
      (Sum.inl (e u) : (stage F K (m+1)).carrier) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  change selectedGrowthBatchMapSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e he (selectedRequests F K s n) h
      ((selectedCutEquiv F K s hs n).symm
        (selectedCutEquiv F K s hs n (Sum.inl u))) =
      (Sum.inl (e u) : (stage F K (m+1)).carrier)
  rw [Equiv.symm_apply_apply]
  rfl

/-- Every fresh vertex of the actual cut goes to the literal
transported request tag, with its original finite ordinal. -/
theorem selectedCutOneStepLift_fresh
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n))
    (r : SelectedRequests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (selectedRequests F K s n))
    (i : Fin r.val.code.1.val) :
    letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
    selectedCutOneStepLift F K s hs n m e he h
        (selectedCutEquiv F K s hs n (Sum.inr ⟨r, i⟩)) =
      (Sum.inr
        ⟨selectedGrowthTagSubtype F K
            (stage F K n).graph (stage F K m).graph
            (stageCut F K s n) e he (selectedRequests F K s n) h r,
         selectedGrowthOrdinalIsoSubtype F K
            (stage F K n).graph (stage F K m).graph
            (stageCut F K s n) e he (selectedRequests F K s n) h r i⟩ :
        (stage F K (m+1)).carrier) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  change selectedGrowthBatchMapSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e he (selectedRequests F K s n) h
      ((selectedCutEquiv F K s hs n).symm
        (selectedCutEquiv F K s hs n (Sum.inr ⟨r, i⟩))) =
      (Sum.inr
        ⟨selectedGrowthTagSubtype F K
            (stage F K n).graph (stage F K m).graph
            (stageCut F K s n) e he (selectedRequests F K s n) h r,
         selectedGrowthOrdinalIsoSubtype F K
            (stage F K n).graph (stage F K m).graph
            (stageCut F K s n) e he (selectedRequests F K s n) h r i⟩ :
        (stage F K (m+1)).carrier)
  rw [Equiv.symm_apply_apply]
  rfl

/-- A map of the actual next source cut is uniquely determined
by the prescribed old map and by the precise transported target
request tag and fresh ordinal for each selected new vertex. -/
theorem selectedCutOneStepLift_unique_of_block_codes
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n))
    (g : SupportCarrier (stage F K (n+1)).carrier
      (stageCut F K s (n+1)) → (stage F K (m+1)).carrier)
    (hgOld : ∀ u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      g (selectedCutEquiv F K s hs n (Sum.inl u)) =
        (Sum.inl (e u) : (stage F K (m+1)).carrier))
    (hgFresh : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      ∀ (r : SelectedRequests (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card)
        (selectedRequests F K s n))
        (i : Fin r.val.code.1.val),
      g (selectedCutEquiv F K s hs n (Sum.inr ⟨r, i⟩)) =
        (Sum.inr
          ⟨selectedGrowthTagSubtype F K
              (stage F K n).graph (stage F K m).graph
              (stageCut F K s n) e he (selectedRequests F K s n) h r,
           selectedGrowthOrdinalIsoSubtype F K
              (stage F K n).graph (stage F K m).graph
              (stageCut F K s n) e he (selectedRequests F K s n) h r i⟩ :
          (stage F K (m+1)).carrier)) :
    g = selectedCutOneStepLift F K s hs n m e he h := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  funext x
  obtain ⟨u, rfl⟩ := (selectedCutEquiv F K s hs n).surjective x
  cases u with
  | inl a =>
      exact (hgOld a).trans
        (selectedCutOneStepLift_old F K s hs n m e he h a).symm
  | inr z =>
      rcases z with ⟨r, i⟩
      exact (hgFresh r i).trans
        (selectedCutOneStepLift_fresh F K s hs n m e he h r i).symm

end CFCoherentTower
end BigHrushovski
