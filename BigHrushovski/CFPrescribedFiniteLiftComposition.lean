import BigHrushovski.CFPartialOrderedBComposition

/-!
# Canonical finite C_F prescribed lifts commute with composition

The preceding finite-image theorem proves composition for arbitrary
genuinely partial ordered b-embeddings. Here we specialize to two
successive *constructed* prescribed lifts. The intermediate source is
the literal finite image of the first lift, not a whole finite stage.

The composite has the target birth labels obtained by composing the
two assignments on represented levels. Reflection of the birth-level
preorder forces this composite assignment to be strictly increasing
on the source levels actually represented, even when there are gaps.

Finite uniqueness then identifies the composite with the prescribed
lift for this composite assignment. This is a finite statement, not
yet a theorem about the monoid of countable embeddings.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Collect the six verified properties of the *particular*
constructed finite prescribed lift. This removes repeated
administrative proofs from composition and later coherence
arguments. -/
theorem finiteSourcePrescribedLift_orderedB_properties
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    let e := finiteSourcePrescribedLift
      F K s hs level hStrict n hCover
    Function.Injective e ∧
    (∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y)) ∧
    (∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x)) ∧
    (∀ x : SupportCarrier (Vertex F K) s,
      (e x).1 = level x.val.1) ∧
    (∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y)) ∧
    (∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y)) := by
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteSourceLiftOfCut_injective F K s n
      (assignedTargetStage F K s level n) hCover M.map
  · intro x y
    exact finiteSourceLiftOfCut_induced F K s n
      (assignedTargetStage F K s level n) hCover M.map x y
  · intro x
    exact finiteSourceLiftOfCut_birthBValues F K s hs n
      (assignedTargetStage F K s level n) hCover M.map x
  · intro x
    exact finiteSourcePrescribedLift_birthLevel
      F K s hs level hStrict n hCover x
  · intro x y
    exact finiteSourcePrescribedLift_birthLevelPreorder
      F K s hs level hStrict n hCover x y
  · intro x y
    exact finiteSourcePrescribedLift_canonicalOrder
      F K s hs level hStrict n hCover x y

/-- The image of the actual finite prescribed lift is complete
b-closed, not merely closed under old named roots. -/
theorem finiteSourcePrescribedLift_image_bClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    IsBirthBlockClosed F K
      (finiteBirthSourceImage F K s
        (finiteSourcePrescribedLift F K s hs level hStrict n hCover)) := by
  apply finiteBirthSourceImage_bClosed
  intro x
  exact finiteSourceLiftOfCut_birthBValues F K s hs n
    (assignedTargetStage F K s level n) hCover
    (finiteLevelCutLiftWithBirth F K s hs level hStrict n).map x

/-- Exact target labels and reflection of the birth-level
preorder imply strictness on represented source levels.
The labels need NOT be increasing at unrepresented levels. -/
theorem finiteEmbedding_strictOnRepresented_of_birthLabels
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (f : SupportCarrier (Vertex F K) s → Vertex F K)
    (level : ℕ → ℕ)
    (hfLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (f x) (f y))
    (hfBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (f x).1 = level x.val.1) :
    StrictOnRepresented F K s level := by
  intro i hi j hj hij
  rw [finiteEmbeddingLevelMap_unique_on_represented
        F K s f hfLevel level hfBirth i hi,
      finiteEmbeddingLevelMap_unique_on_represented
        F K s f hfLevel level hfBirth j hj]
  exact finiteEmbeddingLevelMap_strictOnRepresented
    F K s f hfLevel i hi j hj hij

/-- Canonical finite lifts respect composition. Start with one
prescribed finite lift on s, take its literal finite b-closed
image t, and form a second prescribed lift on t. Their
composite equals the prescribed lift on s for the composite
level assignment.

The result supplies the necessary strictness proof for that
assignment, rather than assuming it. This holds with arbitrary
finite stage covers in all three constructions. -/
theorem finiteSourcePrescribedLift_comp
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level1 : ℕ → ℕ)
    (hStrict1 : StrictOnRepresented F K s level1)
    (n1 : ℕ) (hCover1 : s ⊆ stageImage F K n1)
    (level2 : ℕ → ℕ)
    (ht : IsBirthBlockClosed F K
      (finiteBirthSourceImage F K s
        (finiteSourcePrescribedLift
          F K s hs level1 hStrict1 n1 hCover1)))
    (hStrict2 : StrictOnRepresented F K
      (finiteBirthSourceImage F K s
        (finiteSourcePrescribedLift
          F K s hs level1 hStrict1 n1 hCover1)) level2)
    (n2 : ℕ)
    (hCover2 :
      finiteBirthSourceImage F K s
        (finiteSourcePrescribedLift
          F K s hs level1 hStrict1 n1 hCover1) ⊆ stageImage F K n2)
    (n3 : ℕ) (hCover3 : s ⊆ stageImage F K n3) :
    ∃ hStrictComp : StrictOnRepresented
      F K s (fun i => level2 (level1 i)),
      (fun x : SupportCarrier (Vertex F K) s =>
        finiteSourcePrescribedLift F K
          (finiteBirthSourceImage F K s
            (finiteSourcePrescribedLift
              F K s hs level1 hStrict1 n1 hCover1))
          ht level2 hStrict2 n2 hCover2
          (finiteBirthSourceImagePoint F K s
            (finiteSourcePrescribedLift
              F K s hs level1 hStrict1 n1 hCover1) x)) =
      finiteSourcePrescribedLift F K s hs
        (fun i => level2 (level1 i)) hStrictComp n3 hCover3 := by
  let e := finiteSourcePrescribedLift
    F K s hs level1 hStrict1 n1 hCover1
  let t := finiteBirthSourceImage F K s e
  let j := finiteBirthSourceImagePoint F K s e
  let g := finiteSourcePrescribedLift
    F K t ht level2 hStrict2 n2 hCover2
  let c : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun x => g (j x)
  let compLevel : ℕ → ℕ := fun i => level2 (level1 i)
  obtain ⟨heInj, heAdj, heB, heBirth, heLevel, heOrder⟩ :=
    finiteSourcePrescribedLift_orderedB_properties
      F K s hs level1 hStrict1 n1 hCover1
  obtain ⟨hgInj, hgAdj, hgB, hgBirth, hgLevel, hgOrder⟩ :=
    finiteSourcePrescribedLift_orderedB_properties
      F K t ht level2 hStrict2 n2 hCover2
  obtain ⟨hCompInj, hCompAdj, hCompB, hCompLevel, hCompOrder⟩ :=
    finiteBirthSourceImage_comp_orderedB
      F K s e g heInj heAdj heB heLevel heOrder
      hgInj hgAdj hgB hgLevel hgOrder
  have hCompBirth :
      ∀ x : SupportCarrier (Vertex F K) s,
        (c x).1 = compLevel x.val.1 := by
    intro x
    calc
      (c x).1 = level2 (j x).val.1 := hgBirth (j x)
      _ = level2 (level1 x.val.1) := by
        change level2 (e x).1 = level2 (level1 x.val.1)
        rw [heBirth x]
  have hCompStrict : StrictOnRepresented F K s compLevel :=
    finiteEmbedding_strictOnRepresented_of_birthLabels
      F K s c compLevel hCompLevel hCompBirth
  refine ⟨hCompStrict, ?_⟩
  exact finiteBirthSourceImage_comp_eq_prescribedLift
    F K s hs e g heInj heAdj heB heLevel heOrder
    hgInj hgAdj hgB hgLevel hgOrder
    compLevel hCompStrict hCompBirth n3 hCover3

end CFCoherentTower
end BigHrushovski
