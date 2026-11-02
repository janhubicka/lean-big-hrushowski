import BigHrushovski.C0CoordinateGeneratedSubcode
import BigHrushovski.C0FiniteCanonicalRestriction

/-!
# Finite C₀ age certificates for generated coordinate subcodes

For a finite canonical C₀ presentation by minimal strong blocks,
one-generated canonical unary values are closed. Restricting to such
a value produces an induced finite graph with its inherited component
index, a minimal-strong presentation (allowing omitted empty cuts),
and exactly the full original set-valued unary values.

This packages the *existing finite hereditary theorem* with the
literal-code interface used by Track D. It does not construct the
countable coordinate host, the functional Fraïssé limit, or its
order-compatible return embedding.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- Reflexive reachability in a finite component dependency graph
implies that every point lies in its complete canonical unary value. -/
theorem canonicalValue_mem_self
    (G : GraphOn V) (κ : V → Fin n) (a : V) :
    a ∈ canonicalValue G κ a := by
  apply (mem_canonicalValue_iff G κ a a).mpr
  exact TaggedAmalgam.DependencyAncestor.root

/-- Composition of finite component-dependency paths. -/
theorem canonicalValue_mem_trans
    (G : GraphOn V) (κ : V → Fin n) {a b c : V}
    (hab : b ∈ canonicalValue G κ a)
    (hbc : c ∈ canonicalValue G κ b) :
    c ∈ canonicalValue G κ a := by
  have hAB : TaggedAmalgam.DependencyAncestor
      (backDependency G κ) (κ a) (κ b) :=
    (mem_canonicalValue_iff G κ a b).mp hab
  have hBC : TaggedAmalgam.DependencyAncestor
      (backDependency G κ) (κ b) (κ c) :=
    (mem_canonicalValue_iff G κ b c).mp hbc
  have hAC : TaggedAmalgam.DependencyAncestor
      (backDependency G κ) (κ a) (κ c) := by
    induction hBC with
    | root => exact hAB
    | @step u v hu hdep ih =>
        exact TaggedAmalgam.DependencyAncestor.step ih hdep
  exact (mem_canonicalValue_iff G κ a c).mpr hAC

/-- Every one-generated finite canonical C₀ value is itself a
substructure for the COMPLETE set-valued unary operation. -/
theorem canonicalValue_oneGenerated_closed
    (G : GraphOn V) (κ : V → Fin n) (a : V) :
    G.IsClosedUnderValues (canonicalValue G κ)
      (canonicalValue G κ a) := by
  intro b hb c hc
  exact canonicalValue_mem_trans G κ hb hc

/-- Consequently the generated finite closed set inherits a genuine
minimal-strong presentation from the given finite C₀ enumeration.
The original finite minimal-strong-step hypothesis is explicit. -/
theorem canonicalValue_oneGenerated_minimalChain
    (G : GraphOn V) (κ : V → Fin n)
    (hMin : ∀ k : ℕ, k < n →
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k + 1)))
    (a : V) :
    Predimension.MinimalStrongChain G.toPredimension ∅
      (canonicalValue G κ a) :=
  canonicalValue_closed_minimalPresentation
    G κ hMin (canonicalValue G κ a)
    (canonicalValue_oneGenerated_closed G κ a)

/-- The complete named unary values of the restricted finite C₀
presentation are exactly the inherited ambient values, not just
inclusions or equalities of their cardinalities. -/
theorem canonicalValue_oneGenerated_restrict_exact
    (G : GraphOn V) (κ : V → Fin n) (a : V)
    (u : {v : V // v ∈ canonicalValue G κ a}) :
    (canonicalValue
      (G.pullback
        (Subtype.val :
          {v : V // v ∈ canonicalValue G κ a} → V))
      (restrictIndex κ (canonicalValue G κ a)) u).image
        (Subtype.val :
          {v : V // v ∈ canonicalValue G κ a} → V) =
      canonicalValue G κ u.val := by
  classical
  exact canonicalValue_restrict_image G κ
    (canonicalValue G κ a)
    (canonicalValue_oneGenerated_closed G κ a) u

/-- Every restricted chronological stage is either empty or an
actual minimal strong step in the induced finite graph. This is the
strong functional-age certificate needed to declare generated
coordinate subcodes permitted, with no global generic assumption. -/
theorem canonicalValue_oneGenerated_restrict_minimalSteps
    (G : GraphOn V) (κ : V → Fin n)
    (hMin : ∀ k : ℕ, k < n →
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1)))
    (a : V) (k : ℕ) (hk : k < n) :
    let s := canonicalValue G κ a
    let H := G.pullback
      (Subtype.val : {v : V // v ∈ s} → V)
    let κs := restrictIndex κ s
    oldStage κs (k+1) = oldStage κs k ∨
      H.toPredimension.IsMinimalStrongStep
        (oldStage κs k) (oldStage κs (k+1)) := by
  classical
  exact canonicalValue_restrict_minimalSteps G κ hMin
    (canonicalValue G κ a)
    (canonicalValue_oneGenerated_closed G κ a) k hk

end FiniteC0
end BigHrushovski
