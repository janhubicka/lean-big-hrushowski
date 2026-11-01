import BigHrushovski.C0FunctionalSpanNormalization

/-!
# Exact finite response to a labelled functional C₀ request

A finite canonical stage S and a finite functional extension
diagram D are given, with a *prescribed* source map e from D into S.
This map preserves and reflects the entire graph and all complete
unary values; it need not identify component ranks.

The arbitrary-span normalization theorem supplies a literal tagged
free amalgam of S and D's target. Its two maps are induced and strong,
both complete unary functions are transported exactly, and every
named source vertex is identified pointwise. This is the finite
responding step for the planned functional fair recursion.

The new carrier has not yet been relabelled onto an initial
segment of ℕ and no countable functional limit is asserted.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- The finite canonical minimal-component presentation itself
implies 2-sparsity without an additional premise. -/
theorem FiniteFunctionalC0.sparse {n k : ℕ}
    (A : FiniteFunctionalC0 n k) :
    A.graph.IsTwoSparse (Finset.univ : Finset (Fin n)) := by
  classical
  have hStrongStages : ∀ j : ℕ, j < k →
      A.graph.toPredimension.IsStrong
        (FiniteC0.oldStage A.index j)
        (FiniteC0.oldStage A.index (j+1)) := by
    intro j hj
    rcases A.minimal j hj with hEq | hMin
    · rw [hEq]
      exact A.graph.toPredimension.strong_refl _
    · exact hMin.1
  have hEmptyClosed : A.graph.IsClosedUnderValues
      (FiniteC0.canonicalValue A.graph A.index)
      (∅ : Finset (Fin n)) := by
    intro x hx
    simp at hx
  have hEmptyStrong :
      A.graph.toPredimension.IsStrong (∅ : Finset (Fin n))
        (Finset.univ : Finset (Fin n)) :=
    FiniteC0.canonicalValue_closed_strong
      A.graph A.index hStrongStages ∅ hEmptyClosed
  intro s _
  have hStrong : A.graph.toPredimension.IsStrong ∅ s :=
    A.graph.toPredimension.strong_restrict hEmptyStrong
      (Finset.empty_subset _) (Finset.subset_univ s)
  have hIneq := hStrong.2 s
    (Finset.empty_subset _) (Finset.Subset.refl s)
  change A.graph.predim ∅ ≤ A.graph.predim s at hIneq
  rw [A.graph.predim_empty] at hIneq
  exact hIneq

/-- Respond to a genuinely labelled finite functional extension,
retaining every prescribed source vertex and both full unary
structures. Neither the two component rank orders nor the
original vertex names need agree across the span. -/
theorem exists_taggedResponse_to_functionalC0Request
    {a p b q c r : ℕ}
    (S : FiniteFunctionalC0 a p)
    (D : FunctionalC0Diagram b q c r)
    (e : Fin b → Fin a)
    (he : Function.Injective e)
    (hInd : ∀ x y : Fin b,
      D.source.graph.adj x y ↔ S.graph.adj (e x) (e y))
    (hValues : ∀ x : Fin b,
      S.unaryValue (e x) =
        (D.source.unaryValue x).image e) :
    let L := FiniteSpan.normalGraph S.graph e he
    let R := FiniteSpan.normalGraph D.target.graph
      D.embedding D.inj
    let K := TaggedAmalgam.freeGraph L R
    let eS := (FiniteSpan.splitEquiv e he).symm
    let eD := (FiniteSpan.splitEquiv D.embedding D.inj).symm
    ∃ (t : ℕ)
      (θ : TaggedAmalgam.Carrier (Fin b)
        (FiniteSpan.Tail e) (FiniteSpan.Tail D.embedding) → Fin t),
      K.IsTwoSparse Finset.univ ∧
      K.toPredimension.IsStrong
        (TaggedAmalgam.leftDomain :
          Finset (TaggedAmalgam.Carrier (Fin b)
            (FiniteSpan.Tail e) (FiniteSpan.Tail D.embedding)))
        Finset.univ ∧
      K.toPredimension.IsStrong
        (TaggedAmalgam.rightDomain :
          Finset (TaggedAmalgam.Carrier (Fin b)
            (FiniteSpan.Tail e) (FiniteSpan.Tail D.embedding)))
        Finset.univ ∧
      (∀ k : ℕ, k < t →
        FiniteC0.oldStage θ k = FiniteC0.oldStage θ (k+1) ∨
        K.toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage θ k) (FiniteC0.oldStage θ (k+1))) ∧
      (∀ x y : Fin a,
        S.graph.adj x y ↔
          K.adj (TaggedAmalgam.leftTag (eS x))
            (TaggedAmalgam.leftTag (eS y))) ∧
      (∀ x y : Fin c,
        D.target.graph.adj x y ↔
          K.adj (TaggedAmalgam.rightTag (eD x))
            (TaggedAmalgam.rightTag (eD y))) ∧
      (∀ x : Fin a,
        FiniteC0.canonicalValue K θ
          (TaggedAmalgam.leftTag (eS x)) =
          (S.unaryValue x).image
            (fun y => TaggedAmalgam.leftTag (eS y))) ∧
      (∀ x : Fin c,
        FiniteC0.canonicalValue K θ
          (TaggedAmalgam.rightTag (eD x)) =
          (D.target.unaryValue x).image
            (fun y => TaggedAmalgam.rightTag (eD y))) ∧
      (∀ x : Fin b,
        TaggedAmalgam.leftTag (eS (e x)) =
          TaggedAmalgam.rightTag (eD (D.embedding x))) := by
  classical
  let eS := (FiniteSpan.splitEquiv e he).symm
  let eD := (FiniteSpan.splitEquiv D.embedding D.inj).symm
  have hAgree : ∀ x y : Fin b,
      S.graph.adj (e x) (e y) ↔
        D.target.graph.adj (D.embedding x) (D.embedding y) := by
    intro x y
    exact (hInd x y).symm.trans (D.induced x y)
  have hNamedS : ∀ x : Fin b,
      FiniteC0.canonicalValue S.graph S.index (e x) =
        (D.source.unaryValue x).image e := hValues
  have hNamedD : ∀ x : Fin b,
      FiniteC0.canonicalValue D.target.graph
          D.target.index (D.embedding x) =
        (D.source.unaryValue x).image D.embedding := D.values
  obtain ⟨t, θ, hSparse, hStrongS, hStrongD, hSteps,
      hAdjS, hAdjD, hValS, hValD⟩ :=
    FiniteSpan.exists_normalized_canonicalFunctionalAmalgam
      S.graph D.target.graph e D.embedding
      he D.inj hAgree
      S.index D.target.index S.minimal D.target.minimal
      D.source.unaryValue hNamedS hNamedD S.sparse D.target.sparse
  refine ⟨t, θ, hSparse, hStrongS, hStrongD, hSteps,
    hAdjS, hAdjD, hValS, hValD, ?_⟩
  intro x
  calc
    TaggedAmalgam.leftTag (eS (e x)) =
      TaggedAmalgam.leftTag (Sum.inl x) := by
        rw [FiniteSpan.splitEquiv_symm_base e he x]
    _ = TaggedAmalgam.rightTag (Sum.inl x) := rfl
    _ = TaggedAmalgam.rightTag (eD (D.embedding x)) := by
        rw [FiniteSpan.splitEquiv_symm_base D.embedding D.inj x]

end FiniteCatalogue
end BigHrushovski
