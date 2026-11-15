import BigHrushovski.C0FairCanonicalStageTransfer
import BigHrushovski.C0ClosedEmptyStepHeredity

/-!
# Track A: exact finite closed functional age of countable canonical C₀ models

Let (N,C) be a countable functional C₀ graph equipped with a cofinal
family of *literal* finite canonical presentations whose complete
one-generated unary values are exactly C.

Every finite C-closed subset s inherits not just a finite component
index with the same complete values, but a full **empty-or-minimal
strong canonical presentation** in its *induced* graph. Unused component
positions are retained. This proves the missing hereditary direction
of the intrinsic finite functional age, on the actual finite carrier.

The construction is the existing closed-subtype restriction followed
by the existing relabelling equivalence. The new work consists solely
of transporting its empty-or-minimal-strong certificate, now available
from the refined finite restriction theorem.
-/

namespace BigHrushovski
namespace FiniteC0

/-- Every finite closed *literal* induced substructure of a countable
canonical C₀ model is itself a finite canonical functional C₀
presentation, preserving the **entire** unary operation. -/
theorem canonicalStages_closed_literal_fullPresentation
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (s : Finset ℕ) (hClosed : N.IsClosedUnderValues C s) :
    ∃ (m : ℕ) (κ : {v : ℕ // v ∈ s} → Fin m),
      (∀ k : ℕ, k < m →
        oldStage κ k = oldStage κ (k + 1) ∨
        (N.pullback (Subtype.val :
          {w : ℕ // w ∈ s} → ℕ)).toPredimension.IsMinimalStrongStep
            (oldStage κ k) (oldStage κ (k + 1))) ∧
      (∀ v : {w : ℕ // w ∈ s},
        C v.val =
          (canonicalValue
            (N.pullback (Subtype.val : {w : ℕ // w ∈ s} → ℕ))
            κ v).image
              (Subtype.val : {w : ℕ // w ∈ s} → ℕ)) := by
  classical
  obtain ⟨t, hst⟩ := hCover s
  let T := {v : ℕ // v ∈ stage t}
  let G : GraphOn T :=
    N.pullback (Subtype.val : T → ℕ)
  obtain ⟨m, κ, hSteps, hValues⟩ := hStage t
  let sT : Finset T :=
    (Finset.univ : Finset T).filter (fun v => v.val ∈ s)
  let U := {v : T // v ∈ sT}
  let S := {v : ℕ // v ∈ s}
  let H₁ : GraphOn U :=
    G.pullback (Subtype.val : U → T)
  let H : GraphOn S :=
    N.pullback (Subtype.val : S → ℕ)
  have hClosedT :
      G.IsClosedUnderValues (canonicalValue G κ) sT := by
    intro u hu v hv
    have huS : u.val ∈ s := (Finset.mem_filter.mp hu).2
    have hvC : v.val ∈ C u.val := by
      rw [hValues u]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hClosed u.val huS hvC⟩
  let e : U ≃ S :=
    { toFun := fun u =>
        ⟨u.val.val, (Finset.mem_filter.mp u.property).2⟩
      invFun := fun v =>
        ⟨⟨v.val, hst v.property⟩,
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, v.property⟩⟩
      left_inv := by
        intro u
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro v
        apply Subtype.ext
        rfl }
  let κU : U → Fin m := restrictIndex κ sT
  let κS : S → Fin m := relabelIndex κU e
  have hAdj : ∀ a b : U, H₁.adj a b ↔ H.adj (e a) (e b) := by
    intro a b
    rfl
  have hStepsU :
      ∀ k : ℕ, k < m →
        oldStage κU k = oldStage κU (k + 1) ∨
        H₁.toPredimension.IsMinimalStrongStep
          (oldStage κU k) (oldStage κU (k + 1)) :=
    canonicalValue_restrict_emptyOrMinimalSteps
      G κ hSteps sT hClosedT
  have hStepsS :
      ∀ k : ℕ, k < m →
        oldStage κS k = oldStage κS (k + 1) ∨
        H.toPredimension.IsMinimalStrongStep
          (oldStage κS k) (oldStage κS (k + 1)) :=
    minimalSteps_relabel H₁ H e hAdj κU hStepsU
  refine ⟨m, κS, hStepsS, ?_⟩
  intro v
  let u : U := e.symm v
  have heu : e u = v := e.apply_symm_apply v
  have hRelabel :
      canonicalValue H κS (e u) =
        (canonicalValue H₁ κU u).image e :=
    canonicalValue_relabel H₁ H e hAdj κU u
  have hRestrict :
      (canonicalValue H₁ κU u).image
        (Subtype.val : U → T) =
      canonicalValue G κ u.val :=
    canonicalValue_restrict_image G κ sT hClosedT u
  have hComp :
      (Subtype.val : S → ℕ) ∘ e =
        (Subtype.val : T → ℕ) ∘ (Subtype.val : U → T) := by
    funext a
    rfl
  have hImages :
      ((canonicalValue H₁ κU u).image e).image
        (Subtype.val : S → ℕ) =
      ((canonicalValue H₁ κU u).image
        (Subtype.val : U → T)).image
          (Subtype.val : T → ℕ) := by
    rw [Finset.image_image, Finset.image_image, hComp]
  have hOnU :
      C (e u).val =
        (canonicalValue H κS (e u)).image
          (Subtype.val : S → ℕ) := by
    calc
      C (e u).val = C u.val.val := rfl
      _ = (canonicalValue G κ u.val).image
          (Subtype.val : T → ℕ) := hValues u.val
      _ = ((canonicalValue H₁ κU u).image
          (Subtype.val : U → T)).image
          (Subtype.val : T → ℕ) := by rw [hRestrict]
      _ = ((canonicalValue H₁ κU u).image e).image
          (Subtype.val : S → ℕ) := hImages.symm
      _ = (canonicalValue H κS (e u)).image
          (Subtype.val : S → ℕ) := by rw [hRelabel]
  simpa only [heu] using hOnU


/-- Consequently, any chosen family of finite closed subsets inherits
literal canonical finite C₀ stage certificates, whether or not that
family is cofinal or consists of the original construction stages. -/
theorem canonicalStages_anyClosedFamily_isCanonical
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage family : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (hClosed : ∀ n : ℕ, N.IsClosedUnderValues C (family n)) :
    HasCanonicalFiniteStages N C family := by
  intro n
  exact canonicalStages_closed_literal_fullPresentation
    N C stage hCover hStage (family n) (hClosed n)

end FiniteC0
end BigHrushovski
