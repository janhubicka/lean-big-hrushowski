import BigHrushovski.CFCompletePrescribedFiniteLift
import BigHrushovski.CFFinitePartialPreorderRigidity

/-!
# Exact finite C_F birth-level preorder and full block images

The prescribed-level recursion already fixes the target birth label
of every source vertex. Strict increase on the finitely represented
levels therefore preserves and reflects the entire birth-level
preorder. No increasing map on all natural numbers is needed.

Combined with the existing exact complete b-value theorem and the
partial-map support/block rigidity theorem, this identifies the
images of the complete literal old supports and birth blocks under
the *same* constructed finite lift. No ambient total self-embedding
is introduced. This is a finite interface towards uniqueness; it
does not itself prove that arbitrary embeddings equal the lift, nor
does it establish the canonical-order comparison or R/H transport.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- A strict level assignment on the represented finite set reflects
the weak order there. The unused source levels play no role. -/
theorem prescribedLevel_le_iff_on_represented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (a b : ℕ)
    (ha : a ∈ representedLevels F K s)
    (hb : b ∈ representedLevels F K s) :
    a ≤ b ↔ level a ≤ level b := by
  constructor
  · intro hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · rw [heq]
    · exact (hStrict a ha b hb hlt).le
  · intro hTarget
    by_contra hNot
    have hReverse : b < a := lt_of_not_ge hNot
    exact (not_lt_of_ge hTarget) (hStrict b hb a ha hReverse)

/-- The genuine finite source lift also preserves and reflects
the literal birth-level preorder, without assuming an extension
of the prescribed assignment to an increasing map of ℕ. -/
theorem finiteSourcePrescribedLift_birthLevelPreorder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (x y : SupportCarrier (Vertex F K) s) :
    BirthLevelLe F K x.val y.val ↔
      BirthLevelLe F K
        (finiteSourcePrescribedLift F K s hs level hStrict n hCover x)
        (finiteSourcePrescribedLift F K s hs level hStrict n hCover y) := by
  change x.val.1 ≤ y.val.1 ↔
      (finiteSourcePrescribedLift F K s hs level hStrict n hCover x).1 ≤
      (finiteSourcePrescribedLift F K s hs level hStrict n hCover y).1
  rw [finiteSourcePrescribedLift_birthLevel F K s hs level hStrict n hCover x,
      finiteSourcePrescribedLift_birthLevel F K s hs level hStrict n hCover y]
  exact prescribedLevel_le_iff_on_represented F K s level hStrict
    x.val.1 y.val.1
    (Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)
    (Finset.mem_image.mpr ⟨y.val, y.property, rfl⟩)

/-- The existing finite-source existence theorem can therefore be
strengthened to include the complete reflected level preorder for
the very same induced, b-value-preserving concrete embedding. -/
theorem finiteSourcePrescribedLift_exists_with_preorder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level) :
    ∃ f : SupportCarrier (Vertex F K) s → Vertex F K,
      Function.Injective f ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        (countableGraph F K).adj x.val y.val ↔
          (countableGraph F K).adj (f x) (f y)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (finiteSourceBirthBValue F K s x).image f =
          birthBValue F K (f x)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (f x).1 = level x.val.1) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        BirthLevelLe F K x.val y.val ↔
          BirthLevelLe F K (f x) (f y)) := by
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  let f := finiteSourcePrescribedLift F K s hs level hStrict n hCover
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
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

/-- Each complete support and fresh block of the finite source
has exactly the corresponding image under the actual prescribed
lift. This applies the existing partial-map rigidity theorem:
there is no artificial map outside s and no assumed block
surjectivity. -/
theorem finiteSourcePrescribedLift_support_block
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (k : ℕ) (r : BirthRequest F K k)
    (i : Fin r.code.1.val)
    (hi : (⟨k, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    let f := finiteSourcePrescribedLift F K s hs level hStrict n hCover
    let w := f ⟨(⟨k, ⟨r, i⟩⟩ : Vertex F K), hi⟩
    (selectedFiniteSet s (birthSupport F K k r)).image f =
        birthSupport F K w.1 w.2.1 ∧
    (selectedFiniteSet s (birthBlock F K k r)).image f =
        birthBlock F K w.1 w.2.1 := by
  classical
  let f := finiteSourcePrescribedLift F K s hs level hStrict n hCover
  let v : Vertex F K := ⟨k, ⟨r, i⟩⟩
  let w : Vertex F K := f ⟨v, hi⟩
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  have hValue :
      (selectedFiniteSet s (birthBValue F K v)).image f =
        birthBValue F K w := by
    change (finiteSourceBirthBValue F K s ⟨v, hi⟩).image f =
      birthBValue F K w
    exact finiteSourceLiftOfCut_birthBValues F K s hs n
      (assignedTargetStage F K s level n) hCover M.map ⟨v, hi⟩
  have hPreorder : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (f x) (f y) := by
    intro x y
    exact finiteSourcePrescribedLift_birthLevelPreorder
      F K s hs level hStrict n hCover x y
  exact finitePartial_birthSupport_block_of_preorder
    F K s k w.1 r w.2.1 i w.2.2 hi f
    hValue rfl hPreorder

end CFCoherentTower
end BigHrushovski
