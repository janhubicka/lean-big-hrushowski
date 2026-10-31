import BigHrushovski.C0FiniteCanonicalValues
import BigHrushovski.StrongHomogeneity

/-!
# Recognizing the C₀ graph reduct of a countable unary-closure limit

The finite C₀ functional age has a canonical unary set-valued closure.
To identify the graph reduct of its countable Fraïssé limit with M₀,
one needs both finite strong covers and the *labelled* strong graph
extension property. The latter does not follow from a finite
graph-to-functional lifting lemma in isolation.

The first part of this file transfers finite relative strongness to
global strongness through cofinal finite stages, with every hypothesis
displayed. It then packages the exact hypotheses which identify a
countable graph as M₀ using the already certified strong uniqueness
theorem. This is a conditional recognition criterion, not a construction
of the functional Fraïssé limit or its strong extension property.
-/

namespace BigHrushovski

namespace Predimension

variable {V : Type*} [DecidableEq V] {d : Predimension V}

/-- A fixed finite subset which is strong inside every sufficiently
large cofinal finite stage is globally strong. No individual stage
is required to be globally strong; the stages need only contain
every finite test set somewhere. -/
theorem globallyStrong_of_cofinal_finite
    (stage : ℕ → Finset V)
    (hCover : ∀ b : Finset V, ∃ n : ℕ, b ⊆ stage n)
    (s : Finset V)
    (hStrong : ∀ n : ℕ, s ⊆ stage n → d.IsStrong s (stage n)) :
    d.IsGloballyStrong s := by
  intro b hsb
  obtain ⟨n, hb⟩ := hCover b
  exact d.strong_restrict (hStrong n (hsb.trans hb)) hsb hb

end Predimension

namespace FiniteC0

/-- A finite set closed under the *complete* unary C-value is
globally strong as soon as it is strong in all finite induced
stage containers in which it occurs. The finite-stage hypothesis
is intended to be discharged by the canonical finite C₀
closed-set strongness theorem after transport of stage indices. -/
theorem globallyStrong_of_closed_stages
    (N : GraphOn ℕ)
    (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hLocal : ∀ (n : ℕ) (s : Finset ℕ),
      s ⊆ stage n →
      N.IsClosedUnderValues C s →
      N.toPredimension.IsStrong s (stage n))
    (s : Finset ℕ)
    (hClosed : N.IsClosedUnderValues C s) :
    N.toPredimension.IsGloballyStrong s := by
  apply Predimension.globallyStrong_of_cofinal_finite
    (d := N.toPredimension) stage hCover s
  intro n hsn
  exact hLocal n s hsn hClosed

/-- Finite unary-closed covers provide genuine finite globally
strong graph covers. The proof does not assume that arbitrary
finite graph-strong sets are already unary-closed. -/
theorem finiteStrongCover_of_unaryClosedCovers
    (N : GraphOn ℕ)
    (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hLocal : ∀ (n : ℕ) (s : Finset ℕ),
      s ⊆ stage n →
      N.IsClosedUnderValues C s →
      N.toPredimension.IsStrong s (stage n))
    (hUnaryCover : ∀ s : Finset ℕ, ∃ c : Finset ℕ,
      s ⊆ c ∧ N.IsClosedUnderValues C c) :
    Predimension.FiniteStrongCover N.toPredimension := by
  refine ⟨?_⟩
  intro s
  obtain ⟨c, hsc, hc⟩ := hUnaryCover s
  exact ⟨c, hsc,
    globallyStrong_of_closed_stages
      N C stage hCover hLocal c hc⟩

/-- Recognition of M₀ from a countable functional presentation:
all hypotheses are exposed explicitly. The finite functional
amalgamation theorem must provide the countable limit, finite
unary-closed covers and the labelled strong graph extension
property; none is silently derived in this theorem. -/
theorem graphReduct_iso_generic_of_unaryPresentation
    (N : GraphOn ℕ)
    (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hSparse : ∀ s : Finset ℕ, 0 ≤ N.predim s)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hLocal : ∀ (n : ℕ) (s : Finset ℕ),
      s ⊆ stage n →
      N.IsClosedUnderValues C s →
      N.toPredimension.IsStrong s (stage n))
    (hUnaryCover : ∀ s : Finset ℕ, ∃ c : Finset ℕ,
      s ⊆ c ∧ N.IsClosedUnderValues C c)
    (hExt : FiniteCatalogue.HasStrongExtensionProperty N) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      FiniteCatalogue.genericTwoSparseGraph.adj x y ↔
        N.adj (e x) (e y) := by
  exact FiniteCatalogue.genericTwoSparseGraph_unique
    N hSparse
    (finiteStrongCover_of_unaryClosedCovers
      N C stage hCover hLocal hUnaryCover) hExt

end FiniteC0

end BigHrushovski
