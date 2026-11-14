import BigHrushovski.C0FairCanonicalStageTransfer

/-!
# Track A: the fair prefixes are canonical finite C₀ presentations

The least-enabled-component recursion gives finite C-closed prefixes Q_n
which exhaust the countable graph. Each prefix has the intrinsic birth
component index β_n : Q_n → Fin n. This file proves that the literal
initial cuts of β_n are precisely the earlier Q_k, and transports each
globally minimal strong step Q_k < Q_(k+1) to the induced graph on Q_n.

Together with the previously certified equality of *complete* unary
values, this shows that the fair prefixes themselves are a cofinal
system of canonical finite C₀ presentations. This is a component
chronology, not yet a choice of a uniform order within each component.
-/

namespace BigHrushovski
namespace FiniteC0

/-- The k-th old stage of the birth index on Q_n is exactly Q_k, on
literal vertices, whenever k ≤ n. This includes k = 0 and n = 0. -/
theorem fairBirthIndex_oldStage_image
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n k : ℕ) (hk : k ≤ n) :
    (oldStage (fairComponentBirthIndex C hC n) k).image
      (Subtype.val : {v : ℕ // v ∈ fairComponentPrefix C hC n} → ℕ) =
      fairComponentPrefix C hC k := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have hBirth :
        fairComponentBirth C hC u.val < k :=
      (mem_oldStage_iff
        (fairComponentBirthIndex C hC n) k u).mp hu
    exact (fairComponentBirth_lt_iff_mem C hC k u.val).mp hBirth
  · intro hx
    have hxN : x ∈ fairComponentPrefix C hC n :=
      (fairComponentPrefix_mono C hC k n hk) hx
    refine Finset.mem_image.mpr ⟨⟨x, hxN⟩, ?_, rfl⟩
    exact (mem_oldStage_iff
      (fairComponentBirthIndex C hC n) k ⟨x, hxN⟩).mpr
        ((fairComponentBirth_lt_iff_mem C hC k x).mpr hx)

/-- Each nonempty consecutive cut of the actual birth index is a
minimal strong step in the *induced finite graph on Q_n*. No new
predimension argument is needed: transport the certified ambient
minimal strong step along the literal subtype inclusion. -/
theorem canonicalStages_fairBirthIndex_minimalStep
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (hC : IsCompleteUnaryClosure C)
    (n k : ℕ) (hk : k < n) :
    (fairPrefixGraph N C hC n).toPredimension.IsMinimalStrongStep
      (oldStage (fairComponentBirthIndex C hC n) k)
      (oldStage (fairComponentBirthIndex C hC n) (k + 1)) := by
  classical
  let T := {v : ℕ // v ∈ fairComponentPrefix C hC n}
  let G : GraphOn T := fairPrefixGraph N C hC n
  let β : T → Fin n := fairComponentBirthIndex C hC n
  have hSub : oldStage β k ⊆ oldStage β (k + 1) := by
    intro v hv
    have hlt : (β v).val < k := (mem_oldStage_iff β k v).mp hv
    exact (mem_oldStage_iff β (k + 1) v).mpr (by omega)
  have hOld :
      (oldStage β k).image (Subtype.val : T → ℕ) =
        fairComponentPrefix C hC k :=
    fairBirthIndex_oldStage_image C hC n k (by omega)
  have hNew :
      (oldStage β (k + 1)).image (Subtype.val : T → ℕ) =
        fairComponentPrefix C hC (k + 1) :=
    fairBirthIndex_oldStage_image C hC n (k + 1) (by omega)
  have hStep :
      N.toPredimension.IsMinimalStrongStep
        (fairComponentPrefix C hC k)
        (fairComponentPrefix C hC (k + 1)) :=
    (canonicalStages_fairComponentPrefix_minimal_and_strong
      N C stage hCover hStage hC k).1
  have hTransport :
      N.toPredimension.IsMinimalStrongStep
        ((oldStage β k).image (Subtype.val : T → ℕ))
        ((oldStage β (k + 1)).image (Subtype.val : T → ℕ)) := by
    rw [hOld, hNew]
    exact hStep
  have hAdj : ∀ u v : T,
      G.adj u v ↔ N.adj u.val v.val := by
    intro u v
    rfl
  exact (G.minimalStrongStep_image_iff N
    (Subtype.val : T → ℕ)
    Subtype.val_injective hAdj
    (oldStage β k) (oldStage β (k + 1)) hSub).mp hTransport

/-- With the original exact cofinal canonical finite stages as input,
the *fair* finite prefixes are themselves canonical finite stages:
all nonempty steps are minimal strong in each induced finite graph,
and each complete unary value is literally the inherited value. -/
theorem canonicalStages_fairPrefixes_areCanonical
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (hC : IsCompleteUnaryClosure C) :
    HasCanonicalFiniteStages N C (fairComponentPrefix C hC) := by
  intro n
  refine ⟨n, fairComponentBirthIndex C hC n, ?_, ?_⟩
  · intro k hk
    exact Or.inr (canonicalStages_fairBirthIndex_minimalStep
      N C stage hCover hStage hC n k hk)
  · intro v
    exact (canonicalStages_fairBirthIndex_exact_fullValues
      N C stage hCover hStage hC n v).symm

/-- Exhaustion of the countable carrier also gives genuine cofinality
for arbitrary finite sets of vertices, not just for singletons. -/
theorem fairComponentPrefix_covers_finite
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (s : Finset ℕ) :
    ∃ n : ℕ, s ⊆ fairComponentPrefix C hC n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, Finset.empty_subset _⟩
  | @insert x s hx ih =>
      obtain ⟨a, ha⟩ := fairComponentPrefix_exhaustive C hC x
      obtain ⟨b, hb⟩ := ih
      refine ⟨max a b, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact (fairComponentPrefix_mono C hC a (max a b)
          (Nat.le_max_left a b)) ha
      · exact (fairComponentPrefix_mono C hC b (max a b)
          (Nat.le_max_right a b)) (hb hyS)

/-- The fair chronological component presentation is cofinal,
canonically finite at every stage, and has strict minimal increments.
This packages the validated component-enumeration part without
claiming an ordered representative inside each component. -/
theorem canonicalStages_fairPrefixes_cofinalCanonical
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (hC : IsCompleteUnaryClosure C) :
    (∀ b : Finset ℕ, ∃ n : ℕ,
      b ⊆ fairComponentPrefix C hC n) ∧
    HasCanonicalFiniteStages N C (fairComponentPrefix C hC) ∧
    (∀ n : ℕ,
      N.toPredimension.IsMinimalStrongStep
        (fairComponentPrefix C hC n)
        (fairComponentPrefix C hC (n + 1))) := by
  refine ⟨fairComponentPrefix_covers_finite C hC,
    canonicalStages_fairPrefixes_areCanonical
      N C stage hCover hStage hC, ?_⟩
  intro n
  exact (canonicalStages_fairComponentPrefix_minimal_and_strong
    N C stage hCover hStage hC n).1

end FiniteC0
end BigHrushovski
