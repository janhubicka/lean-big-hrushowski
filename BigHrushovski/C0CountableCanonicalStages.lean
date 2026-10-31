import BigHrushovski.C0CompleteUnaryCovers
import BigHrushovski.InducedEmbedding

/-!
# Countable C₀ reducts from coherent finite canonical presentations

Suppose a countable graph N has cofinal finite induced stages and a
complete unary function C. On each finite stage, we require a
minimal-component index whose canonical *complete* unary values are
literally equal to the restriction of C.

These finite certificates imply:
* C is reflexive and transitive as a one-generated closure;
* every finite subset has a finite C-closed cover;
* every finite C-closed set is globally strong in N, without assuming
  that the individual stages are globally strong.

The remaining hypothesis for identifying N with M₀ is precisely the
labelled strong graph extension property. Nothing in this module
constructs the functional Fraïssé limit or assumes its conclusion.
-/

namespace BigHrushovski
namespace FiniteC0

/-- A countable graph with explicit, finite, *literal* canonical
C₀ presentations on each stage. The complete unary value on a stage
equals the ambient one-generated C-value, not merely its
intersection with the stage. Every stage therefore is C-closed. -/
def HasCanonicalFiniteStages
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ) : Prop :=
  ∀ n : ℕ, ∃ (m : ℕ)
    (κ : {v : ℕ // v ∈ stage n} → Fin m),
    (∀ k : ℕ, k < m →
      oldStage κ k = oldStage κ (k+1) ∨
      ((N.pullback (Subtype.val :
          {v : ℕ // v ∈ stage n} → ℕ)).toPredimension).IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1))) ∧
    (∀ v : {v : ℕ // v ∈ stage n},
      C v.val =
        (canonicalValue
          (N.pullback (Subtype.val : {v : ℕ // v ∈ stage n} → ℕ))
          κ v).image
            (Subtype.val : {v : ℕ // v ∈ stage n} → ℕ))

/-- A finite C-closed set s lying in a canonical stage is strong
in the induced graph on that stage. Its vertices are pulled back to
the literal stage subtype: no arbitrary relabelling or graph
isomorphism is used. -/
theorem localStrong_of_canonicalStage
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (t s : Finset ℕ) (hs : s ⊆ t)
    (hClosed : N.IsClosedUnderValues C s)
    {m : ℕ} (κ : {v : ℕ // v ∈ t} → Fin m)
    (hSteps : ∀ k : ℕ, k < m →
      oldStage κ k = oldStage κ (k+1) ∨
      ((N.pullback (Subtype.val : {v : ℕ // v ∈ t} → ℕ)).toPredimension).IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1)))
    (hValues : ∀ v : {v : ℕ // v ∈ t},
      C v.val =
        (canonicalValue
          (N.pullback (Subtype.val : {v : ℕ // v ∈ t} → ℕ))
          κ v).image
            (Subtype.val : {v : ℕ // v ∈ t} → ℕ)) :
    N.toPredimension.IsStrong s t := by
  classical
  let T := {v : ℕ // v ∈ t}
  let G : GraphOn T := N.pullback (Subtype.val : T → ℕ)
  let S : Finset T :=
    (Finset.univ : Finset T).filter (fun v => v.val ∈ s)
  have hSImage : S.image (Subtype.val : T → ℕ) = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hEq⟩ := Finset.mem_image.mp hx
      exact hEq ▸ (Finset.mem_filter.mp hv).2
    · intro hx
      refine Finset.mem_image.mpr
        ⟨⟨x, hs hx⟩, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hUImage :
      (Finset.univ : Finset T).image (Subtype.val : T → ℕ) = t := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, _, hEq⟩ := Finset.mem_image.mp hx
      exact hEq ▸ v.property
    · intro hx
      exact Finset.mem_image.mpr
        ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have hClosedS : G.IsClosedUnderValues (canonicalValue G κ) S := by
    intro u hu v hv
    have huS : u.val ∈ s := (Finset.mem_filter.mp hu).2
    have hvC : v.val ∈ C u.val := by
      rw [hValues u]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hClosed u.val huS hvC⟩
  have hStrongSteps : ∀ k : ℕ, k < m →
      G.toPredimension.IsStrong
        (oldStage κ k) (oldStage κ (k+1)) := by
    intro k hk
    rcases hSteps k hk with hEq | hMin
    · rw [hEq]
      exact G.toPredimension.strong_refl _
    · exact hMin.1
  have hStrong : G.toPredimension.IsStrong
      S (Finset.univ : Finset T) :=
    canonicalValue_closed_strong G κ hStrongSteps S hClosedS
  have hInduced : ∀ u v : T,
      G.adj u v ↔ N.adj u.val v.val := by
    intro u v
    rfl
  have hTransport :=
    (G.strong_image_iff N (Subtype.val : T → ℕ)
      Subtype.val_injective hInduced
      S (Finset.univ : Finset T) (Finset.subset_univ S)).mpr
      hStrong
  rw [hSImage, hUImage] at hTransport
  exact hTransport

/-- The exact stage certificates discharge *every* local
strongness hypothesis in the previous countable reduct criterion. -/
theorem localStrong_of_canonicalFiniteStages
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hStage : HasCanonicalFiniteStages N C stage) :
    ∀ (n : ℕ) (s : Finset ℕ),
      s ⊆ stage n →
      N.IsClosedUnderValues C s →
      N.toPredimension.IsStrong s (stage n) := by
  intro n s hs hc
  obtain ⟨m, κ, hSteps, hValues⟩ := hStage n
  exact localStrong_of_canonicalStage N C (stage n) s
    hs hc κ hSteps hValues

/-- Complete canonical values on cofinal finite stages force
the *ambient* one-generated operation C to be reflexive and
transitive. There is no separate closure axiom. -/
theorem completeUnary_of_canonicalFiniteStages
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage) :
    IsCompleteUnaryClosure C := by
  constructor
  · intro x
    obtain ⟨n, hn⟩ := hCover ({x} : Finset ℕ)
    have hx : x ∈ stage n := hn (Finset.mem_singleton.mpr rfl)
    obtain ⟨m, κ, _, hValues⟩ := hStage n
    let u : {v : ℕ // v ∈ stage n} := ⟨x, hx⟩
    rw [hValues u]
    exact Finset.mem_image.mpr
      ⟨u, canonicalValue_mem_self _ κ u, rfl⟩
  · intro x y hxy
    obtain ⟨n, hn⟩ := hCover ({x} : Finset ℕ)
    have hx : x ∈ stage n := hn (Finset.mem_singleton.mpr rfl)
    obtain ⟨m, κ, _, hValues⟩ := hStage n
    let G : GraphOn {v : ℕ // v ∈ stage n} :=
      N.pullback (Subtype.val : {v : ℕ // v ∈ stage n} → ℕ)
    let u : {v : ℕ // v ∈ stage n} := ⟨x, hx⟩
    have hxyImage : y ∈
        (canonicalValue G κ u).image
          (Subtype.val : {v : ℕ // v ∈ stage n} → ℕ) := by
      rw [← hValues u]
      exact hxy
    obtain ⟨v, hv, hvVal⟩ :=
      Finset.mem_image.mp hxyImage
    have hTrans :=
      canonicalValue_subset_of_mem G κ hv
    intro z hz
    have hzImage : z ∈ (canonicalValue G κ v).image
        (Subtype.val : {v : ℕ // v ∈ stage n} → ℕ) := by
      rw [← hValues v, hvVal]
      exact hz
    have hzIn : z ∈ (canonicalValue G κ u).image
        (Subtype.val : {v : ℕ // v ∈ stage n} → ℕ) := by
      exact Finset.image_mono _ hTrans hzImage
    rw [← hValues u] at hzIn
    exact hzIn

/-- Recognition of M₀ now requires only cofinality of
*literal* finite canonical stages, finite graph sparsity and
the genuinely labelled strong graph extension property. Finite
closed covers and local strongness are obtained automatically. -/
theorem graphReduct_iso_generic_of_canonicalFiniteStages
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hSparse : ∀ s : Finset ℕ, 0 ≤ N.predim s)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (hExt : FiniteCatalogue.HasStrongExtensionProperty N) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      FiniteCatalogue.genericTwoSparseGraph.adj x y ↔
        N.adj (e x) (e y) := by
  exact graphReduct_iso_generic_of_completeUnary N C stage
    (completeUnary_of_canonicalFiniteStages N C stage hCover hStage)
    hSparse hCover
    (localStrong_of_canonicalFiniteStages N C stage hStage)
    hExt

end FiniteC0
end BigHrushovski
