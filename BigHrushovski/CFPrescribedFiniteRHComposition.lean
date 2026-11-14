import BigHrushovski.CFPrescribedFiniteLiftComposition
import BigHrushovski.CFPrescribedFiniteRHLift

/-!
# Composition of finite C_F lifts in the actual (R,H) language

The auxiliary complete b-value presentation is used to prove
rigidity of finite lifted maps. The manuscript, however, states
its finite lifting lemma for the actual root operation R and
the partial hull operation H. This module transfers the
canonical composition identity back to R and H.

There is no need for a second induction through birth blocks:
a composite of two prescribed lifts agrees literally with
the prescribed lift at its composite represented-level assignment,
and the latter has already been verified to preserve the
complete root values and all defined partial-hull values,
including reflection of the domain of H.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The actual finite-source root/H embedding conditions.
The partial operation H requires exact transport of all
defined values and *reflection* of its domain. The extension
outside the finite source is used only to express finite-set
functional values; no assumption is made about that extension
outside the source. -/
def FiniteSourceRHValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K) : Prop :=
  let X : Set (Vertex F K) := {v | v ∈ s}
  let f := extendClosedSourceMap F K X e
  (∀ v ∈ X,
    (birthReachableRoots F K v).image f =
      birthReachableRoots F K (f v)) ∧
  (∀ t : Finset (Vertex F K),
    (∀ v ∈ t, v ∈ X) →
    (∀ r ∈ t, IsBirthRoot F K r) →
    (birthDClosedHull F K t).image f =
      birthDClosedHull F K (t.image f)) ∧
  (∀ t : Finset (Vertex F K),
    (∀ v ∈ t, v ∈ X) →
    ((∀ r ∈ t, IsBirthRoot F K r) ↔
      (∀ r ∈ t.image f, IsBirthRoot F K r)))

/-- A constructed finite prescribed lift satisfies the exact
finite-source R,H conditions, with reflection of the partial
domain of H. This only repackages the previously verified
manuscript-language theorem. -/
theorem finiteSourcePrescribedLift_has_RHValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    FiniteSourceRHValues F K s
      (finiteSourcePrescribedLift F K s hs level hStrict n hCover) := by
  exact finiteSourcePrescribedLift_RHValues
    F K s hs level hStrict n hCover

/-- Two actual finite prescribed lifts compose to the prescribed
lift at the composed assignment in the **real R,H language**:
the composite preserves all complete root values, all defined
partial H-values, and reflects the domain of H.

The intermediate domain is the literal finite image of the
first lift. No total old-stage map or increasing assignment on
unused levels is needed. The finite covers may be different. -/
theorem finiteSourcePrescribedLift_comp_RHValues
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
      let c : SupportCarrier (Vertex F K) s → Vertex F K :=
        fun x =>
          finiteSourcePrescribedLift F K
            (finiteBirthSourceImage F K s
              (finiteSourcePrescribedLift
                F K s hs level1 hStrict1 n1 hCover1))
            ht level2 hStrict2 n2 hCover2
            (finiteBirthSourceImagePoint F K s
              (finiteSourcePrescribedLift
                F K s hs level1 hStrict1 n1 hCover1) x)
      c = finiteSourcePrescribedLift F K s hs
        (fun i => level2 (level1 i)) hStrictComp n3 hCover3 ∧
      FiniteSourceRHValues F K s c := by
  obtain ⟨hStrictComp, hEq⟩ :=
    finiteSourcePrescribedLift_comp
      F K s hs level1 hStrict1 n1 hCover1
      level2 ht hStrict2 n2 hCover2 n3 hCover3
  refine ⟨hStrictComp, ?_⟩
  change
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
        (fun i => level2 (level1 i)) hStrictComp n3 hCover3 ∧
    FiniteSourceRHValues F K s
      (fun x =>
        finiteSourcePrescribedLift F K
          (finiteBirthSourceImage F K s
            (finiteSourcePrescribedLift
              F K s hs level1 hStrict1 n1 hCover1))
          ht level2 hStrict2 n2 hCover2
          (finiteBirthSourceImagePoint F K s
            (finiteSourcePrescribedLift
              F K s hs level1 hStrict1 n1 hCover1) x))
  refine ⟨hEq, ?_⟩
  rw [hEq]
  exact finiteSourcePrescribedLift_has_RHValues
    F K s hs (fun i => level2 (level1 i))
    hStrictComp n3 hCover3

end CFCoherentTower
end BigHrushovski
