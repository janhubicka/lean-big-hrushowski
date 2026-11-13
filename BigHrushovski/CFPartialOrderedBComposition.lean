import BigHrushovski.CFFiniteClosedImageNaturality
import BigHrushovski.CFCompleteFiniteUniqueLevelLift

/-!
# Composition of genuinely partial finite C_F embeddings

A complete-b-preserving map on a finite selected source has a
b-closed finite image. We prove that two embeddings, the second
defined only on that literal image, compose to an embedding
preserving the full graph, complete b-values, the birth-level
preorder, and the actual canonical birth order.

The second theorem identifies any such composite with the
prescribed finite lift as soon as its target birth labels are
fixed. Both proofs concern actual finite partial maps; neither
introduces a total map on the countable structure or a global
strictly increasing map of all natural-number levels.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Two genuinely partial finite ordered b-functional embeddings
compose. The target of the first embedding is its *literal* finite
image, which is the entire domain of the second embedding.

The conclusion includes induced adjacency and nonadjacency,
complete b-values, reflection of the level preorder, and
reflection of the canonical order. No ambient total embedding
or finite-stage extension is used. -/
theorem finiteBirthSourceImage_comp_orderedB
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (g : SupportCarrier (Vertex F K)
      (finiteBirthSourceImage F K s e) → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (hgInj : Function.Injective g)
    (hgAdj : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      (countableGraph F K).adj u.val v.val ↔
        (countableGraph F K).adj (g u) (g v))
    (hgB : ∀ u : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      (finiteSourceBirthBValue F K
        (finiteBirthSourceImage F K s e) u).image g =
          birthBValue F K (g u))
    (hgLevel : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (g u) (g v))
    (hgOrder : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      canonicalBirthLt F K u.val v.val ↔
        canonicalBirthLt F K (g u) (g v)) :
    let j := finiteBirthSourceImagePoint F K s e
    let c := fun x => g (j x)
    Function.Injective c ∧
    (∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (c x) (c y)) ∧
    (∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image c =
        birthBValue F K (c x)) ∧
    (∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (c x) (c y)) ∧
    (∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (c x) (c y)) := by
  let j := finiteBirthSourceImagePoint F K s e
  have hjInj : Function.Injective j := by
    intro x y hxy
    apply heInj
    exact congrArg
      (fun z : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e) => z.val) hxy
  refine ⟨hgInj.comp hjInj, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact (heAdj x y).trans (hgAdj (j x) (j y))
  · intro x
    exact finiteBirthSourceImage_comp_bValues
      F K s e heB g hgB x
  · intro x y
    exact (heLevel x y).trans (hgLevel (j x) (j y))
  · intro x y
    exact (heOrder x y).trans (hgOrder (j x) (j y))

/-- Composition compatibility with the *actual prescribed finite
lift*: any composite of two partial ordered b-embeddings on finite
sources, if it realizes the required target birth levels, is
literally the constructed prescribed lift.

The stage cover used to define that lift is arbitrary. As in the
finite uniqueness theorem, strictness is required only at
represented source birth levels; no global increasing self-map
of ℕ is assumed. -/
theorem finiteBirthSourceImage_comp_eq_prescribedLift
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (g : SupportCarrier (Vertex F K)
      (finiteBirthSourceImage F K s e) → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (hgInj : Function.Injective g)
    (hgAdj : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      (countableGraph F K).adj u.val v.val ↔
        (countableGraph F K).adj (g u) (g v))
    (hgB : ∀ u : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      (finiteSourceBirthBValue F K
        (finiteBirthSourceImage F K s e) u).image g =
          birthBValue F K (g u))
    (hgLevel : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (g u) (g v))
    (hgOrder : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      canonicalBirthLt F K u.val v.val ↔
        canonicalBirthLt F K (g u) (g v))
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (hBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (g (finiteBirthSourceImagePoint F K s e x)).1 =
        level x.val.1)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    (fun x => g (finiteBirthSourceImagePoint F K s e x)) =
      finiteSourcePrescribedLift F K s hs level hStrict n hCover := by
  obtain ⟨hCompInj, hCompAdj, hCompB, hCompLevel, hCompOrder⟩ :=
    finiteBirthSourceImage_comp_orderedB F K s e g
      heInj heAdj heB heLevel heOrder
      hgInj hgAdj hgB hgLevel hgOrder
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  let lift := finiteSourcePrescribedLift
    F K s hs level hStrict n hCover
  have hLiftInj : Function.Injective lift :=
    finiteSourceLiftOfCut_injective F K s n
      (assignedTargetStage F K s level n) hCover M.map
  have hLiftAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (lift x) (lift y) := by
    intro x y
    exact finiteSourceLiftOfCut_induced F K s n
      (assignedTargetStage F K s level n) hCover M.map x y
  have hLiftB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image lift =
        birthBValue F K (lift x) := by
    intro x
    exact finiteSourceLiftOfCut_birthBValues F K s hs n
      (assignedTargetStage F K s level n) hCover M.map x
  have hLiftBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (lift x).1 = level x.val.1 := by
    intro x
    exact finiteSourcePrescribedLift_birthLevel
      F K s hs level hStrict n hCover x
  have hLiftLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (lift x) (lift y) := by
    intro x y
    exact finiteSourcePrescribedLift_birthLevelPreorder
      F K s hs level hStrict n hCover x y
  have hLiftOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (lift x) (lift y) := by
    intro x y
    exact finiteSourcePrescribedLift_canonicalOrder
      F K s hs level hStrict n hCover x y
  exact arbitraryFiniteEmbedding_unique_of_prescribedLevels
    F K s hs level
    (fun x => g (finiteBirthSourceImagePoint F K s e x)) lift
    hCompInj hLiftInj hCompAdj hLiftAdj hCompB hLiftB
    hCompLevel hLiftLevel hCompOrder hLiftOrder hBirth hLiftBirth

end CFCoherentTower
end BigHrushovski
