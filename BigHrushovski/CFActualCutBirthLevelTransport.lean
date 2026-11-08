import BigHrushovski.CFActualCutAutomaticLift
import BigHrushovski.CFSelectedCutBlockRigidity

/-!
# Exact birth levels under the automatic C_F one-level lifting map

In the finite level-lifting induction, every represented source
level must be sent to its PRESCRIBED target birth level. The
canonical selected-batch graph map alone is not a proof of that
statement unless its actual old/fresh tags are inspected.

We record these exact literal birth-label assertions for the
automatic one-level map, whose old source is a genuine selected
subtype and whose target support-transport certificates are
derived automatically from inducedness and strict d-closure.

Old selected source vertices retain the birth labels of the
already constructed target old map. Every selected fresh block
is born at the new target level m, and hence follows every old
image vertex in the target level preorder.

No whole ambient source-stage map U_n → U_m is constructed.
No global increasing self-map of all birth indices is assumed.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The old part of the automatic successor map leaves the
already prescribed target birth vertex LITERALLY unchanged. -/
theorem actualCutLift_oldBirthExact
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj (e u) (e v))
    (hClosed : (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    toVertex F K (m + 1)
      (actualCutLift F K s hs n m e he hAdj hClosed
        (selectedCutEquiv F K s hs n (Sum.inl u))) =
    toVertex F K m (e u) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier :=
    stageLinearOrder F K m
  let h := actualCutTransport F K s hs n m e he hAdj hClosed
  change toVertex F K (m + 1)
      (selectedCutOneStepLift F K s hs n m e he h
        (selectedCutEquiv F K s hs n (Sum.inl u))) =
    toVertex F K m (e u)
  rw [selectedCutOneStepLift_old F K s hs n m e he h u]
  exact toVertex_old F K m (e u)

/-- Each fresh vertex is sent to birth level m exactly,
with the constructed actual request tag and finite ordinal. -/
theorem actualCutLift_freshBirthLevel
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj (e u) (e v))
    (hClosed : (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ)
    (r : SelectedRequests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (selectedRequests F K s n))
    (i : Fin r.val.code.1.val) :
    (toVertex F K (m + 1)
      (actualCutLift F K s hs n m e he hAdj hClosed
        (selectedCutEquiv F K s hs n (Sum.inr ⟨r, i⟩)))).1 = m := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier :=
    stageLinearOrder F K m
  let h := actualCutTransport F K s hs n m e he hAdj hClosed
  change (toVertex F K (m + 1)
      (selectedCutOneStepLift F K s hs n m e he h
        (selectedCutEquiv F K s hs n (Sum.inr ⟨r, i⟩)))).1 = m
  rw [selectedCutOneStepLift_fresh F K s hs n m e he h r i]
  rfl

/-- An old vertex of the selected source cut has target birth
level strictly before the one just used for new blocks. -/
theorem actualCutLift_oldBirthBefore
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj (e u) (e v))
    (hClosed : (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    (toVertex F K (m + 1)
      (actualCutLift F K s hs n m e he hAdj hClosed
        (selectedCutEquiv F K s hs n (Sum.inl u)))).1 < m := by
  rw [actualCutLift_oldBirthExact F K s hs n m
      e he hAdj hClosed u]
  exact toVertex_birth_lt F K m (e u)

/-- The automatic one-level map sends each new block after
all old images in the ACTUAL target birth-level preorder. -/
theorem actualCutLift_oldBirthLtFresh
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj (e u) (e v))
    (hClosed : (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n))
    (r : SelectedRequests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (selectedRequests F K s n))
    (i : Fin r.val.code.1.val) :
    (toVertex F K (m + 1)
      (actualCutLift F K s hs n m e he hAdj hClosed
        (selectedCutEquiv F K s hs n (Sum.inl u)))).1 <
    (toVertex F K (m + 1)
      (actualCutLift F K s hs n m e he hAdj hClosed
        (selectedCutEquiv F K s hs n (Sum.inr ⟨r, i⟩)))).1 := by
  rw [actualCutLift_freshBirthLevel F K s hs n m
      e he hAdj hClosed r i]
  exact actualCutLift_oldBirthBefore F K s hs n m
    e he hAdj hClosed u

end CFCoherentTower
end BigHrushovski
