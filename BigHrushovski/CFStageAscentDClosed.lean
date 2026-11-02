import BigHrushovski.CFStageBirthOrderCoherence
import BigHrushovski.CFPartialSupportAutomaticClosure

/-!
# Strict d-closedness and order across arbitrary finite target-stage gaps

A finite C_F level lift may use source levels t_0<...<t_r but
arbitrary prescribed increasing target levels s_0<...<s_r.
The image at stage s_i+1 must be carried into the old part of
stage s_(i+1), even when those stages are not consecutive.

The canonical old-stage ascent is induced, preserves and reflects
the inherited order, and has strictly d-closed image.
We prove that an arbitrary finite d-closed subset stays strictly
d-closed after any such ascent, then instantiate this for the
image of a genuinely partial old-source embedding.

This does NOT assume or construct a total increasing map on all
birth levels. It does not yet carry the complete b-values or the
multi-level finite lift.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The literal old-stage image is strictly d-closed after every
finite number of successor-stage inclusions. -/
theorem ascend_fullStage_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ) :
    (stage F K (n+k)).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset (stage F K n).carrier).image
        (ascend F K n k))
      Finset.univ := by
  classical
  induction k with
  | zero =>
      have hRefl : (stage F K n).graph.toPredimension.IsDClosed
          (Finset.univ : Finset (stage F K n).carrier) Finset.univ :=
        (stage F K n).graph.toPredimension.dclosed_refl _
      simpa only [Nat.add_zero, ascend, Finset.image_id] using hRefl
  | succ k ih =>
      have hRel :
          (stage F K ((n+k)+1)).graph.toPredimension.IsDClosed
            (((Finset.univ : Finset (stage F K n).carrier).image
              (ascend F K n k)).image Sum.inl)
            ((Finset.univ : Finset (stage F K (n+k)).carrier).image
              (Sum.inl : (stage F K (n+k)).carrier →
                (stage F K ((n+k)+1)).carrier)) := by
        exact (((stage F K (n+k)).graph).dClosed_image_iff
          (stage F K ((n+k)+1)).graph
          (Sum.inl : (stage F K (n+k)).carrier →
            (stage F K ((n+k)+1)).carrier)
          Sum.inl_injective
          (fun u v => (stage_succ_induced F K (n+k) u v).symm)
          ((Finset.univ : Finset (stage F K n).carrier).image
            (ascend F K n k))
          Finset.univ (Finset.subset_univ _)).mpr ih
      have hWhole := stage_succ_dClosed F K (n+k)
      have h := (stage F K ((n+k)+1)).graph.toPredimension.dclosed_trans
        hRel hWhole
      simpa only [Nat.add_succ, ascend, Finset.image_image,
        Function.comp_def] using h

/-- Any strictly d-closed subset of stage n remains strictly
d-closed in the whole stage n+k under the literal old ascent. -/
theorem ascend_dClosed_image_full
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ)
    (A : Finset (stage F K n).carrier)
    (hA : (stage F K n).graph.toPredimension.IsDClosed
      A Finset.univ) :
    (stage F K (n+k)).graph.toPredimension.IsDClosed
      (A.image (ascend F K n k)) Finset.univ := by
  classical
  have hRel : (stage F K (n+k)).graph.toPredimension.IsDClosed
      (A.image (ascend F K n k))
      ((Finset.univ : Finset (stage F K n).carrier).image
        (ascend F K n k)) := by
    exact (((stage F K n).graph).dClosed_image_iff
      (stage F K (n+k)).graph
      (ascend F K n k)
      (ascend_injective F K n k)
      (fun u v => (ascend_induced F K n k u v).symm)
      A Finset.univ (Finset.subset_univ A)).mpr hA
  exact (stage F K (n+k)).graph.toPredimension.dclosed_trans
    hRel (ascend_fullStage_dClosed F K n k)

/-- The strictly d-closed image of a selected partial old map
remains strictly d-closed after advancing the target old stage.
There is no map defined outside the selected source subtype. -/
theorem selectedOldImage_ascend_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ)
    {U : Type*} [Fintype U] [DecidableEq U]
    (S : Finset U)
    (e : SupportCarrier U S → (stage F K n).carrier)
    (hClosed : (stage F K n).graph.toPredimension.IsDClosed
      (selectedOldImage S e) Finset.univ) :
    (stage F K (n+k)).graph.toPredimension.IsDClosed
      (selectedOldImage S (fun u => ascend F K n k (e u)))
      Finset.univ := by
  classical
  have h := ascend_dClosed_image_full F K n k
    (selectedOldImage S e) hClosed
  simpa only [selectedOldImage, Finset.image_image,
    Function.comp_def] using h

/-- An induced map of a selected source remains induced after
arbitrary target-stage ascent, including reflected nonedges. -/
theorem selectedOldMap_ascend_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ)
    {U : Type*} [Fintype U] [DecidableEq U]
    (G : GraphOn U) (S : Finset U)
    (e : SupportCarrier U S → (stage F K n).carrier)
    (hAdj : ∀ u v : SupportCarrier U S,
      G.adj u.val v.val ↔ (stage F K n).graph.adj (e u) (e v))
    (u v : SupportCarrier U S) :
    G.adj u.val v.val ↔
      (stage F K (n+k)).graph.adj
        (ascend F K n k (e u)) (ascend F K n k (e v)) :=
  (hAdj u v).trans (ascend_induced F K n k (e u) (e v)).symm

/-- An increasing selected old-source map remains increasing
for the exact inherited order at any later target stage. -/
theorem selectedOldMap_ascend_strictMono
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ)
    {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]
    (S : Finset U)
    (e : SupportCarrier U S → (stage F K n).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      StrictMono e) :
    letI : LinearOrder (stage F K (n+k)).carrier :=
      stageLinearOrder F K (n+k)
    StrictMono (fun u => ascend F K n k (e u)) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K (n+k)).carrier :=
    stageLinearOrder F K (n+k)
  intro u v huv
  exact (stageLt_ascend_iff F K n k (e u) (e v)).mpr (he huv)

end CFCoherentTower
end BigHrushovski
