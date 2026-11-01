import BigHrushovski.C0TaggedFullFunctionalAmalgam
import BigHrushovski.FiniteCatalogue
import Mathlib.Logic.Encodable.Basic

/-!
# Countable catalogue of finite canonical functional C₀ diagrams

A finite functional member is represented by a graph on Fin n
and a witnessing minimal-component index into Fin k. The
complete set-valued unary function is the canonical one; no
extra independent, possibly incompatible function data are
chosen.

An embedding of finite functional members must preserve and
reflect the entire graph and preserve each COMPLETE unary
value onto its target value. A mere graph embedding or a map
of supports is insufficient.

The catalogue enumerates all these finite diagrams, and
the corresponding requests with prescribed old labels in ℕ,
using the same fair Nat-pairing schedule as the already
certified strong graph construction. This is a finite
enumeration interface only; construction of a responder
and the countable functional limit is separate.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- A labelled finite canonical C₀ component presentation, allowing
unused index ranks but only empty or minimal strong steps.
It determines an actual graph and an actual complete set-valued
unary function on Fin n. -/
structure FiniteFunctionalC0 (n k : ℕ) where
  graph : GraphOn (Fin n)
  index : Fin n → Fin k
  minimal : ∀ j : ℕ, j < k →
    FiniteC0.oldStage index j =
      FiniteC0.oldStage index (j+1) ∨
    graph.toPredimension.IsMinimalStrongStep
      (FiniteC0.oldStage index j)
      (FiniteC0.oldStage index (j+1))

/-- A finite canonical functional presentation is determined by its
finite graph and its component-index map. Minimality is a proof
condition and carries no additional countable information. -/
noncomputable instance finiteFunctionalC0_finite (n k : ℕ) :
    Finite (FiniteFunctionalC0 n k) := by
  classical
  have h : Function.Injective
      (fun x : FiniteFunctionalC0 n k => (x.graph, x.index)) := by
    intro x y hEq
    cases x
    cases y
    cases hEq
    rfl
  exact Finite.of_injective
    (fun x : FiniteFunctionalC0 n k => (x.graph, x.index)) h

/-- Complete one-generated functional closure of a labelled
presentation, including the whole component and all recursively
reachable earlier components. -/
noncomputable def FiniteFunctionalC0.unaryValue
    {n k : ℕ} (A : FiniteFunctionalC0 n k) (v : Fin n) :
    Finset (Fin n) :=
  FiniteC0.canonicalValue A.graph A.index v

/-- A finite embedding of the *functional* structures represented
by two component enumerations. The source and target indices are
witnesses; the map is not required to preserve numeric ranks.
It must preserve all complete vertex-valued unary function values. -/
structure FunctionalC0Diagram (n k m l : ℕ) where
  source : FiniteFunctionalC0 n k
  target : FiniteFunctionalC0 m l
  embedding : Fin n → Fin m
  inj : Function.Injective embedding
  induced : ∀ x y : Fin n,
    source.graph.adj x y ↔
      target.graph.adj (embedding x) (embedding y)
  values : ∀ x : Fin n,
    target.unaryValue (embedding x) =
      (source.unaryValue x).image embedding

/-- A finite functional diagram has only finitely many labelled
graph, index and embedding data. -/
noncomputable instance functionalC0Diagram_finite (n k m l : ℕ) :
    Finite (FunctionalC0Diagram n k m l) := by
  classical
  have h : Function.Injective
      (fun d : FunctionalC0Diagram n k m l =>
        (d.source, d.target, d.embedding)) := by
    intro d e hEq
    cases d
    cases e
    cases hEq
    rfl
  exact Finite.of_injective
    (fun d : FunctionalC0Diagram n k m l =>
      (d.source, d.target, d.embedding)) h

/-- Every finite functional diagram has a representation by
finite natural-number parameters, without bounding its total
number of vertices or component blocks in advance. -/
abbrev FunctionalC0DiagramCatalogue :=
  Σ n : ℕ, Σ k : ℕ, Σ m : ℕ, Σ l : ℕ,
    FunctionalC0Diagram n k m l

noncomputable instance : Countable FunctionalC0DiagramCatalogue := by
  infer_instance

/-- The graph embedding in a functional request is required to
extend a prescribed labelled map of its source into ℕ. The map is
checked for applicability at the stage where the request fires. -/
abbrev FunctionalC0RequestCatalogue :=
  Σ n : ℕ, Σ k : ℕ, Σ m : ℕ, Σ l : ℕ,
    FunctionalC0Diagram n k m l × (Fin n → ℕ)

noncomputable instance : Countable FunctionalC0RequestCatalogue := by
  infer_instance

noncomputable instance : Encodable FunctionalC0RequestCatalogue :=
  Encodable.ofCountable FunctionalC0RequestCatalogue

/-- Revisit every finite functional embedding request infinitely
often, by coupling its code with an arbitrary repetition counter.
This is independent of any choice of finite response. -/
noncomputable def fairFunctionalC0Request (stage : ℕ) :
    Option FunctionalC0RequestCatalogue :=
  (Encodable.decode : ℕ → Option FunctionalC0RequestCatalogue)
    (Nat.unpair stage).1

theorem fairFunctionalC0Request_after
    (req : FunctionalC0RequestCatalogue) (threshold : ℕ) :
    ∃ stage : ℕ,
      threshold ≤ stage ∧ fairFunctionalC0Request stage = some req := by
  refine ⟨Nat.pair (Encodable.encode req) threshold,
    Nat.right_le_pair _ _, ?_⟩
  simp [fairFunctionalC0Request, Nat.unpair_pair, Encodable.encodek]

end FiniteCatalogue
end BigHrushovski
