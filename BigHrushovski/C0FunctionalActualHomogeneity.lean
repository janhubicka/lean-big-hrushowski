import BigHrushovski.C0FunctionalActualForth

/-!
# Track A: finite closed functional back steps and actual homogeneity

The countable C₀ functional limit has an actual finite closed forth
extension over every prescribed vertex, using the full finite
closed-base extension theorem.

The inverse of a finite closed complete-functional partial
isomorphism is again such an isomorphism. Moreover pointwise
extension is invariant under taking inverses. Thus the same forth
lemma supplies a back step. Composing the two steps proves the
genuine joint finite extension property required by the previously
verified functional back-and-forth recursion.

Applying that recursion to any initial finite closed functional
partial isomorphism yields an automorphism of the actual countable
functional limit which extends the given initial map, preserves and
reflects all graph edges, and transports every complete unary value.

No choice of local orders in the ordered Ramsey expansion is made.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso
namespace FiniteClosedFunctionalPartialIso

/-- Inverting the finite graph equivalence also inverts the complete
functional structure, provided both domains are closed and the
original finite map preserves the entire unary membership relation. -/
noncomputable def symm
    {M N : GraphOn ℕ} {CM CN : ℕ → Finset ℕ}
    (p : FiniteClosedFunctionalPartialIso M N CM CN) :
    FiniteClosedFunctionalPartialIso N M CN CM where
  graph := p.graph.symm
  sourceClosed := p.targetClosed
  targetClosed := p.sourceClosed
  fullValues := by
    intro x y
    have h :=
      (p.fullValues (p.graph.equiv.symm x)
        (p.graph.equiv.symm y)).symm
    change y.val ∈ CN x.val ↔
      (p.graph.equiv.symm y).val ∈ CM (p.graph.equiv.symm x).val
    simpa only [Equiv.apply_symm_apply] using h

/-- Taking inverses preserves genuine pointwise extension of finite
closed functional partial maps. No assumption on the ordering of
their component presentations is needed. -/
theorem Extends_symm
    {M N : GraphOn ℕ} {CM CN : ℕ → Finset ℕ}
    {p q : FiniteClosedFunctionalPartialIso M N CM CN}
    (hpq : Extends p q) :
    Extends p.symm q.symm := by
  obtain ⟨hs, ht, hValues⟩ := hpq
  refine ⟨ht, hs, ?_⟩
  intro y
  let x := p.graph.equiv.symm y
  have hOld :
      (q.graph.equiv ⟨x.val, hs x.property⟩).val = y.val := by
    simpa only [Equiv.apply_symm_apply] using hValues x
  have hEq :
      q.graph.equiv ⟨x.val, hs x.property⟩ =
        (⟨y.val, ht y.property⟩ :
          {v : ℕ // v ∈ q.graph.target}) :=
    Subtype.ext hOld
  change
    (q.graph.equiv.symm ⟨y.val, ht y.property⟩).val =
      (p.graph.equiv.symm y).val
  calc
    (q.graph.equiv.symm ⟨y.val, ht y.property⟩).val =
        (q.graph.equiv.symm
          (q.graph.equiv ⟨x.val, hs x.property⟩)).val := by
            rw [hEq]
    _ = x.val := by simp
    _ = (p.graph.equiv.symm y).val := rfl

/-- A prescribed target vertex can also be reached by a closed
functional partial-isomorphism extension: apply the actual forth
step to the inverse and then invert the new finite map. -/
theorem fairLimit_back
    (p : FiniteClosedFunctionalPartialIso
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairUnaryStages.limitValue
      FiniteFunctionalNatStage.fairUnaryStages.limitValue)
    (k : ℕ) :
    ∃ q : FiniteClosedFunctionalPartialIso
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairUnaryStages.limitValue
      FiniteFunctionalNatStage.fairUnaryStages.limitValue,
      Extends p q ∧ k ∈ q.graph.target := by
  obtain ⟨r, hr, hk⟩ := fairLimit_forth p.symm k
  refine ⟨r.symm, ?_, hk⟩
  have h := Extends_symm hr
  simpa [Extends, symm, FiniteStrongPartialIso.symm] using h

/-- The actual countable C₀ functional limit satisfies the finite
**joint** extension property over every finite closed complete-
functional partial automorphism: at one finite step it can include
any prescribed source and target vertices simultaneously. -/
theorem fairLimit_hasClosedFunctionalJointSteps :
    HasJointSteps
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairUnaryStages.limitValue
      FiniteFunctionalNatStage.fairUnaryStages.limitValue := by
  intro k p
  obtain ⟨q, hpq, hkSource⟩ := fairLimit_forth p k
  obtain ⟨r, hqr, hkTarget⟩ := fairLimit_back q k
  refine ⟨r, ?_, ?_, hkTarget⟩
  · exact FiniteStrongPartialIso.Extends.trans hpq hqr
  · exact hqr.1 hkSource

/-- Any finite closed complete-functional partial isomorphism of the
actual countable C₀ limit extends to an automorphism of its *whole*
functional structure. The conclusion uses one bijection and gives
exact preservation of graph edges and nonedges and complete C-values. -/
theorem fairLimit_functionalHomogeneous
    (p0 : FiniteClosedFunctionalPartialIso
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairUnaryStages.limitValue
      FiniteFunctionalNatStage.fairUnaryStages.limitValue) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        FiniteFunctionalNatStage.fairGraphStages.limitGraph.adj x y ↔
          FiniteFunctionalNatStage.fairGraphStages.limitGraph.adj (e x) (e y)) ∧
      (∀ x : ℕ,
        FiniteFunctionalNatStage.fairUnaryStages.limitValue (e x) =
          (FiniteFunctionalNatStage.fairUnaryStages.limitValue x).image e) ∧
      (∀ x : ℕ, ∀ hx : x ∈ p0.graph.source,
        e x = (p0.graph.equiv ⟨x, hx⟩).val) := by
  exact exists_functional_equiv_extending p0
    fairLimit_hasClosedFunctionalJointSteps

end FiniteClosedFunctionalPartialIso
end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
