import BigHrushovski.C0FairBirthCanonicalValues
import BigHrushovski.C0FiniteCanonicalRestriction
import BigHrushovski.C0FiniteEquivTransport

/-!
# Track A: complete fair-birth values from the actual countable canonical stages

A finite C-closed subset s of a countable canonical C₀ presentation
inherits a *literal* finite component index with the identical
complete vertex-valued unary operation. To construct it, first
restrict an enclosing finite canonical stage to the corresponding
closed subtype, then use the evident equivalence between that
nested subtype and the literal subtype of s.

Applying the fair birth-index invariance theorem gives the complete
unary value identity for every finite fair prefix Q_n. The argument
uses no chosen order inside the components.
-/

namespace BigHrushovski
namespace FiniteC0

/-- Every finite subset closed under the ambient complete unary
operation has a finite canonical component index on its literal
induced graph, with *exact* complete values in the original
numeric vertex carrier. No strongness or component order is
assumed for s beyond closure. -/
theorem canonicalStages_closed_literal_fullValues
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (s : Finset ℕ) (hClosed : N.IsClosedUnderValues C s) :
    ∃ (m : ℕ) (κ : {v : ℕ // v ∈ s} → Fin m),
      ∀ v : {w : ℕ // w ∈ s},
      C v.val =
        (canonicalValue
          (N.pullback (Subtype.val : {w : ℕ // w ∈ s} → ℕ))
          κ v).image
            (Subtype.val : {w : ℕ // w ∈ s} → ℕ) := by
  classical
  obtain ⟨t, hst⟩ := hCover s
  let T := {v : ℕ // v ∈ stage t}
  let G : GraphOn T :=
    N.pullback (Subtype.val : T → ℕ)
  obtain ⟨m, κ, _hSteps, hValues⟩ := hStage t
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
  refine ⟨m, κS, ?_⟩
  intro v
  let u : U := e.symm v
  have heu : e u = v := e.apply_symm_apply v
  have hAdj : ∀ a b : U, H₁.adj a b ↔ H.adj (e a) (e b) := by
    intro a b
    rfl
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

/-- Complete graph-defined canonical C₀ values agree with the
original full unary operation at every actual finite fair prefix.
The comparison presentation is obtained from the countable stage
certificates; it is not postulated as an extra hypothesis. -/
theorem canonicalStages_fairBirthIndex_exact_fullValues
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (hC : IsCompleteUnaryClosure C)
    (n : ℕ)
    (x : {v : ℕ // v ∈ fairComponentPrefix C hC n}) :
    (canonicalValue (fairPrefixGraph N C hC n)
      (fairComponentBirthIndex C hC n) x).image
        (Subtype.val :
          {v : ℕ // v ∈ fairComponentPrefix C hC n} → ℕ) =
      C x.val := by
  have hClosed :
      N.IsClosedUnderValues C (fairComponentPrefix C hC n) :=
    canonicalStages_fairComponentPrefix_closed
      N C stage hCover hStage hC n
  obtain ⟨m, κ, hValues⟩ :=
    canonicalStages_closed_literal_fullValues
      N C stage hCover hStage
      (fairComponentPrefix C hC n) hClosed
  exact fairBirthIndex_preserves_complete_canonicalValue
    N C hC n κ hValues x

end FiniteC0
end BigHrushovski
