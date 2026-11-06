import BigHrushovski.CoherentNatUnaryStages
import BigHrushovski.C0CountableStageFunctionalExtension
import BigHrushovski.CountableStrongLimit

/-!
# Countable C₀ presentations from coherent graph and unary stages

A graph is built as the union of finite supported graph relations,
and the complete finite-valued unary operation is built by
exact coherence across strictly growing consecutive finite stages.

Assume each finite induced stage has a canonical minimal-component
presentation whose complete unary values agree literally with
the finite unary function at that stage. Then:
* every finite stage is strong in its successor;
* the limit operation has the exact canonical complete values
  on every finite induced stage;
* every finite set lies in a finite closed strong cover;
* the graph reduct is isomorphic to M₀ as soon as the
  **functional stage extension property** is established.

In particular, the graph strong-step condition is DERIVED,
not assumed, from complete unary closure of old stages
and the finite canonical presentation of the successor.
Constructing the fair responding stages remains a separate task.
-/

namespace BigHrushovski

namespace GraphOn

/-- Two graphs on the same carrier are equal if their
complete adjacency predicates agree on all ordered pairs.
This includes the reflection of nonedges. -/
theorem eq_of_adj_iff {V : Type*} (G H : GraphOn V)
    (h : ∀ x y : V, G.adj x y ↔ H.adj x y) : G = H := by
  cases G with
  | mk adjG symmG irreflG =>
      cases H with
      | mk adjH symmH irreflH =>
          have hAdj : adjG = adjH := by
            funext x y
            exact propext (h x y)
          cases hAdj
          rfl

end GraphOn

/-- A coherent Nat-labelled graph and a coherent finite-valued
unary operation sharing the same strictly growing stage
intervals. Each finite induced graph carries its own actual
canonical C₀ component-index witness whose complete unary
values coincide with that stage's unary function. -/
structure CoherentNatC0Stages where
  graph : CoherentNatGraphStages
  unary : CoherentNatUnaryStages
  sameStage : ∀ n : ℕ,
    graph.stage n = Finset.range (unary.size n)
  finiteCanonical : ∀ n : ℕ,
    ∃ (k : ℕ)
      (κ : {v : ℕ // v ∈ graph.stage n} → Fin k),
      (∀ j : ℕ, j < k →
        FiniteC0.oldStage κ j = FiniteC0.oldStage κ (j+1) ∨
        ((graph.graph n).pullback
          (Subtype.val : {v : ℕ // v ∈ graph.stage n} → ℕ)).toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage κ j)
          (FiniteC0.oldStage κ (j+1))) ∧
      (∀ v : {v : ℕ // v ∈ graph.stage n},
        unary.value n v.val =
          (FiniteC0.canonicalValue
            ((graph.graph n).pullback
              (Subtype.val : {v : ℕ // v ∈ graph.stage n} → ℕ))
            κ v).image
              (Subtype.val : {v : ℕ // v ∈ graph.stage n} → ℕ))

namespace CoherentNatC0Stages

variable (S : CoherentNatC0Stages)

/-- Every finite set lies in one actual stage of the graph
and unary construction. This follows from strictly growing
consecutive labels, not from an extra coverage premise. -/
theorem finite_stage_cover (s : Finset ℕ) :
    ∃ n : ℕ, s ⊆ S.graph.stage n := by
  obtain ⟨n, hn⟩ := S.unary.finite_stage_cover s
  refine ⟨n, ?_⟩
  rw [S.sameStage n]
  exact hn

/-- Every old stage is closed under the successor's entire
set-valued unary function, by exact old-value coherence. -/
theorem old_stage_closed_in_successor (n : ℕ) :
    (S.graph.graph (n+1)).IsClosedUnderValues
      (S.unary.value (n+1)) (S.graph.stage n) := by
  intro x hx y hy
  have hxSize : x < S.unary.size n := by
    have h : x ∈ Finset.range (S.unary.size n) := by
      rw [← S.sameStage n]
      exact hx
    exact Finset.mem_range.mp h
  have hStable := S.unary.coherent n x hxSize
  rw [hStable] at hy
  have hyOld : y ∈ Finset.range (S.unary.size n) :=
    S.unary.supported n x hxSize hy
  rw [S.sameStage n]
  exact hyOld

/-- The complete unary closure of the old stage implies that
it is a strong graph substructure of the successor. No separate
strong-step assumption is necessary. -/
theorem strong_steps :
    S.graph.HasStrongSteps := by
  intro n
  obtain ⟨k, κ, hSteps, hValues⟩ := S.finiteCanonical (n+1)
  exact FiniteC0.localStrong_of_canonicalStage
    (S.graph.graph (n+1)) (S.unary.value (n+1))
    (S.graph.stage (n+1)) (S.graph.stage n)
    (S.graph.stage_step n)
    (S.old_stage_closed_in_successor n)
    κ hSteps hValues

/-- The finite graph induced by the direct-limit graph agrees
literally with the finite graph induced by the corresponding
stage graph. This uses reflection of nonedges. -/
theorem limit_pullback_eq_stage (n : ℕ) :
    S.graph.limitGraph.pullback
      (Subtype.val : {v : ℕ // v ∈ S.graph.stage n} → ℕ) =
    (S.graph.graph n).pullback
      (Subtype.val : {v : ℕ // v ∈ S.graph.stage n} → ℕ) := by
  apply GraphOn.eq_of_adj_iff
  intro u v
  exact S.graph.limitGraph_induced n u.property v.property

/-- Exact canonical finite-stage certificates pass to the
countable limit graph and stable complete unary operation. -/
theorem limit_hasCanonicalFiniteStages :
    FiniteC0.HasCanonicalFiniteStages
      S.graph.limitGraph S.unary.limitValue S.graph.stage := by
  intro n
  obtain ⟨k, κ, hSteps, hValues⟩ := S.finiteCanonical n
  refine ⟨k, κ, ?_, ?_⟩
  · rw [S.limit_pullback_eq_stage n]
    exact hSteps
  · intro v
    have hv : v.val < S.unary.size n := by
      have h : v.val ∈ Finset.range (S.unary.size n) := by
        rw [← S.sameStage n]
        exact v.property
      exact Finset.mem_range.mp h
    rw [S.unary.limitValue_eq_stage n v.val hv,
      S.limit_pullback_eq_stage n]
    exact hValues v

/-- The graph limit has finite globally strong covers by
unary-closed finite stages. This is a consequence of the
finite canonical stage certificates and coherence. -/
theorem limit_finiteStrongCover :
    Predimension.FiniteStrongCover
      S.graph.limitGraph.toPredimension :=
  S.graph.finiteStrongCover_of_strong_steps S.strong_steps

/-- Conditional identification of the graph reduct of the
coherent functional limit with M₀. The only remaining
substantive hypothesis is its genuine FUNCTIONAL extension
property over canonical finite stages. -/
theorem limit_reduct_iso_generic_of_functionalExtension
    (hExt : FiniteC0.HasCanonicalStageExtensionProperty
      S.graph.limitGraph S.unary.limitValue S.graph.stage) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      FiniteCatalogue.genericTwoSparseGraph.adj x y ↔
        S.graph.limitGraph.adj (e x) (e y) := by
  exact FiniteC0.graphReduct_iso_generic_of_functionalStageExtension
    S.graph.limitGraph S.unary.limitValue S.graph.stage
    S.finite_stage_cover S.limit_hasCanonicalFiniteStages hExt

end CoherentNatC0Stages
end BigHrushovski
