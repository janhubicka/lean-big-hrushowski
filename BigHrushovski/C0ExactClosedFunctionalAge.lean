import BigHrushovski.C0CountableClosedCanonicalAge
import BigHrushovski.C0FiniteAgeClosedRealization
import BigHrushovski.C0NamedClosedBaseValues

/-!
# Track A: the exact finite closed functional C₀ age

A finite canonical functional C₀ presentation is a 2-sparse finite
graph with a finite component index whose stages are empty or minimal
strong, together with its complete graph-defined one-generated
unary values.

Every finite closed induced substructure of the constructed countable
C₀ functional limit has such a presentation, and conversely every
finite canonical functional C₀ presentation is realized by a closed
globally strong finite induced substructure of the limit.

The first direction uses the literal finite closed canonical-age
restriction theorem. The second uses the already certified finite
functional age universality and complete-functional image closure.
No ordered representatives of the components are selected.
-/

namespace BigHrushovski
namespace FiniteC0

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The finite **unordered functional C₀ age**: genuine 2-sparsity,
a (possibly non-surjective) canonical finite component index whose
nonempty increments are minimal strong, and the entire graph-defined
canonical value at each vertex. -/
def HasFiniteCanonicalC0Structure
    (G : GraphOn B) (D : B → Finset B) : Prop :=
  G.IsTwoSparse (Finset.univ : Finset B) ∧
  ∃ (m : ℕ) (κ : B → Fin m),
    (∀ k : ℕ, k < m →
      oldStage κ k = oldStage κ (k + 1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k + 1))) ∧
    (∀ u : B, D u = canonicalValue G κ u)

end FiniteC0

namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- Every finite **C-closed** literal induced substructure of the
actually constructed countable functional C₀ limit is a canonical
finite functional C₀ structure. Its complete one-generated operation
is the entire inherited operation, with no cut-off at the boundary
of the subset. -/
theorem fairLimit_closedFinite_isCanonicalC0
    (s : Finset ℕ)
    (hClosed :
      fairGraphStages.limitGraph.IsClosedUnderValues
        fairUnaryStages.limitValue s) :
    FiniteC0.HasFiniteCanonicalC0Structure
      (fairGraphStages.limitGraph.pullback
        (Subtype.val : {v : ℕ // v ∈ s} → ℕ))
      (FiniteC0.namedClosedBaseValue fairUnaryStages.limitValue s) := by
  classical
  let N : GraphOn ℕ := fairGraphStages.limitGraph
  let C : ℕ → Finset ℕ := fairUnaryStages.limitValue
  let S := {v : ℕ // v ∈ s}
  let G : GraphOn S := N.pullback (Subtype.val : S → ℕ)
  have hSImage :
      (Finset.univ : Finset S).image (Subtype.val : S → ℕ) = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
      exact u.property
    · intro hx
      exact Finset.mem_image.mpr
        ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have hSparseN : N.IsTwoSparse
      ((Finset.univ : Finset S).image (Subtype.val : S → ℕ)) := by
    rw [hSImage]
    intro t ht
    exact FiniteC0.sparse_of_canonicalFiniteStages
      N C fairGraphStages.stage
      fairCoherentC0Stages.finite_stage_cover
      fairLimitCanonicalStages t
  have hAdj : ∀ u v : S,
      G.adj u v ↔ N.adj u.val v.val := by
    intro u v
    rfl
  have hSparseG : G.IsTwoSparse (Finset.univ : Finset S) :=
    (G.twoSparse_image_iff N (Subtype.val : S → ℕ)
      Subtype.val_injective hAdj Finset.univ).mp hSparseN
  obtain ⟨m, κ, hSteps, hValues⟩ :=
    FiniteC0.canonicalStages_closed_literal_fullPresentation
      N C fairGraphStages.stage
      fairCoherentC0Stages.finite_stage_cover
      fairLimitCanonicalStages s hClosed
  refine ⟨hSparseG, m, κ, hSteps, ?_⟩
  intro u
  apply Finset.image_injective
    (Subtype.val_injective :
      Function.Injective (Subtype.val : S → ℕ))
  calc
    (FiniteC0.namedClosedBaseValue C s u).image
        (Subtype.val : S → ℕ) =
          C u.val :=
            FiniteC0.namedClosedBaseValue_image
              N C s hClosed u
    _ = (FiniteC0.canonicalValue G κ u).image
        (Subtype.val : S → ℕ) :=
          hValues u

/-- Every finite canonical functional C₀ structure has a copy in
the actual constructed countable limit whose literal image is
C-closed and globally strong. The same injective map is induced
for graphs and preserves **all** finite unary values. -/
theorem fairLimit_realizesCanonicalC0Structure
    {B : Type} [Fintype B] [DecidableEq B]
    (H : GraphOn B) (D : B → Finset B)
    (hCanonical : FiniteC0.HasFiniteCanonicalC0Structure H D) :
    ∃ f : B → ℕ,
      Function.Injective f ∧
      (∀ u v : B,
        H.adj u v ↔ fairGraphStages.limitGraph.adj (f u) (f v)) ∧
      (∀ u : B,
        fairUnaryStages.limitValue (f u) = (D u).image f) ∧
      fairGraphStages.limitGraph.IsClosedUnderValues
        fairUnaryStages.limitValue ((Finset.univ : Finset B).image f) ∧
      fairGraphStages.limitGraph.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset B).image f) := by
  rcases hCanonical with ⟨hSparse, m, κ, hSteps, hValues⟩
  obtain ⟨f, hf, hAdj, hFull, hClosed, hStrong⟩ :=
    fairLimit_realizesFiniteCanonicalAsClosedStrong
      H κ hSteps hSparse
  refine ⟨f, hf, hAdj, ?_, hClosed, hStrong⟩
  intro u
  rw [hValues u]
  exact hFull u

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
