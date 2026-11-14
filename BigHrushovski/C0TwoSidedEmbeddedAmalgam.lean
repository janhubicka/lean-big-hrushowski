import BigHrushovski.C0TaggedFullFunctionalAmalgam
import BigHrushovski.C0FiniteEquivTransport
import BigHrushovski.SpanNormalization

/-!
# Track A: the finite two-sided C₀ functional amalgam over arbitrary embeddings

The certified finite functional amalgamation theorem is stated for two
graphs with a common literally named P-summand. Here we normalize
arbitrary injective embeddings i : P → A and j : P → B by their finite
base/tail decompositions, transport both complete canonical unary
operations to these decompositions, and apply the existing theorem.

The result preserves and reflects both original graphs, identifies
only the named base vertices, provides a canonical minimal-component
presentation of the actual free amalgam, and preserves BOTH complete
unary values. In particular, no numerical alignment of the component
indices on the base is required.

This is a finite theorem. The countable extension over arbitrary finite
closed bases still needs to apply the certified cofinal-stage extension
property to this finite amalgam.
-/

namespace BigHrushovski
namespace FiniteSpan

variable {P A B : Type*}
variable [Fintype P] [Fintype A] [Fintype B]
variable [DecidableEq P] [DecidableEq A] [DecidableEq B]
variable {n m : ℕ}

/-- The two-sided canonical functional free amalgam of two finite
graphs whose common finite base is embedded through arbitrary
injections. Compatibility is equality of the whole named unary values
on the base, not equality of arbitrary numerical component ranks.

The output carrier and maps are the existing normalized tagged free
amalgam; thus all conclusions refer to the SAME actual graph and
the SAME full canonical component index. -/
theorem exists_twoSidedCanonicalFunctionalAmalgam
    (G : GraphOn A) (H : GraphOn B)
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (hSparseG : G.IsTwoSparse (Finset.univ : Finset A))
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset B))
    (κA : A → Fin n) (κB : B → Fin m)
    (hStepsA : ∀ k : ℕ, k < n →
      FiniteC0.oldStage κA k = FiniteC0.oldStage κA (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κA k) (FiniteC0.oldStage κA (k+1)))
    (hStepsB : ∀ k : ℕ, k < m →
      FiniteC0.oldStage κB k = FiniteC0.oldStage κB (k+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κB k) (FiniteC0.oldStage κB (k+1)))
    (F : P → Finset P)
    (hValueA : ∀ p : P,
      FiniteC0.canonicalValue G κA (i p) =
        (F p).image i)
    (hValueB : ∀ p : P,
      FiniteC0.canonicalValue H κB (j p) =
        (F p).image j) :
    let K := TaggedAmalgam.freeGraph
      (normalGraph G i hi) (normalGraph H j hj)
    let f := leftAmalgamEmbedding i hi j
    let g := rightAmalgamEmbedding i j hj
    ∃ (t : ℕ)
      (θ : TaggedAmalgam.Carrier P (Tail i) (Tail j) → Fin t),
      K.IsTwoSparse
        (Finset.univ : Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j))) ∧
      K.toPredimension.IsStrong
        (TaggedAmalgam.leftDomain (P := P) (L := Tail i) (R := Tail j))
        Finset.univ ∧
      K.toPredimension.IsStrong
        (TaggedAmalgam.rightDomain (P := P) (L := Tail i) (R := Tail j))
        Finset.univ ∧
      (∀ k : ℕ, k < t →
        FiniteC0.oldStage θ k = FiniteC0.oldStage θ (k+1) ∨
        K.toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage θ k) (FiniteC0.oldStage θ (k+1))) ∧
      (∀ a b : A, K.adj (f a) (f b) ↔ G.adj a b) ∧
      (∀ a b : B, K.adj (g a) (g b) ↔ H.adj a b) ∧
      (∀ p : P, f (i p) = g (j p)) ∧
      (∀ a : A, ∀ b : B, f a = g b →
        ∃ p : P, a = i p ∧ b = j p) ∧
      (∀ a : A,
        FiniteC0.canonicalValue K θ (f a) =
          (FiniteC0.canonicalValue G κA a).image f) ∧
      (∀ b : B,
        FiniteC0.canonicalValue K θ (g b) =
          (FiniteC0.canonicalValue H κB b).image g) := by
  classical
  let eA : A ≃ (P ⊕ Tail i) := (splitEquiv i hi).symm
  let eB : B ≃ (P ⊕ Tail j) := (splitEquiv j hj).symm
  let GA : GraphOn (P ⊕ Tail i) := normalGraph G i hi
  let HB : GraphOn (P ⊕ Tail j) := normalGraph H j hj
  let κAN : (P ⊕ Tail i) → Fin n :=
    FiniteC0.relabelIndex κA eA
  let κBN : (P ⊕ Tail j) → Fin m :=
    FiniteC0.relabelIndex κB eB
  let K := TaggedAmalgam.freeGraph GA HB
  let f := leftAmalgamEmbedding i hi j
  let g := rightAmalgamEmbedding i j hj

  have hAdjA : ∀ a b : A,
      G.adj a b ↔ GA.adj (eA a) (eA b) := by
    intro a b
    change G.adj a b ↔
      G.adj (splitEquiv i hi (eA a)) (splitEquiv i hi (eA b))
    simp [eA]
  have hAdjB : ∀ a b : B,
      H.adj a b ↔ HB.adj (eB a) (eB b) := by
    intro a b
    change H.adj a b ↔
      H.adj (splitEquiv j hj (eB a)) (splitEquiv j hj (eB b))
    simp [eB]

  have hBaseA (p : P) : eA (i p) = (Sum.inl p : P ⊕ Tail i) := by
    apply (splitEquiv i hi).injective
    simp [eA]
  have hBaseB (p : P) : eB (j p) = (Sum.inl p : P ⊕ Tail j) := by
    apply (splitEquiv j hj).injective
    simp [eB]
  have hCompA : eA ∘ i = (Sum.inl : P → P ⊕ Tail i) := by
    funext p
    exact hBaseA p
  have hCompB : eB ∘ j = (Sum.inl : P → P ⊕ Tail j) := by
    funext p
    exact hBaseB p

  have hStagesA :
      ∀ k : ℕ, k < n →
        FiniteC0.oldStage κAN k =
          FiniteC0.oldStage κAN (k+1) ∨
        GA.toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage κAN k)
          (FiniteC0.oldStage κAN (k+1)) :=
    FiniteC0.minimalSteps_relabel G GA eA hAdjA κA hStepsA
  have hStagesB :
      ∀ k : ℕ, k < m →
        FiniteC0.oldStage κBN k =
          FiniteC0.oldStage κBN (k+1) ∨
        HB.toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage κBN k)
          (FiniteC0.oldStage κBN (k+1)) :=
    FiniteC0.minimalSteps_relabel H HB eB hAdjB κB hStepsB

  have hBaseValueA : ∀ p : P,
      FiniteC0.canonicalValue GA κAN (.inl p) =
        (F p).image (Sum.inl : P → P ⊕ Tail i) := by
    intro p
    have hTransport :=
      FiniteC0.canonicalValue_relabel G GA eA hAdjA κA (i p)
    calc
      FiniteC0.canonicalValue GA κAN (.inl p) =
          (FiniteC0.canonicalValue G κA (i p)).image eA := by
            simpa [κAN, hBaseA p] using hTransport
      _ = ((F p).image i).image eA := by rw [hValueA p]
      _ = (F p).image (Sum.inl : P → P ⊕ Tail i) := by
        rw [Finset.image_image, hCompA]
  have hBaseValueB : ∀ p : P,
      FiniteC0.canonicalValue HB κBN (.inl p) =
        (F p).image (Sum.inl : P → P ⊕ Tail j) := by
    intro p
    have hTransport :=
      FiniteC0.canonicalValue_relabel H HB eB hAdjB κB (j p)
    calc
      FiniteC0.canonicalValue HB κBN (.inl p) =
          (FiniteC0.canonicalValue H κB (j p)).image eB := by
            simpa [κBN, hBaseB p] using hTransport
      _ = ((F p).image j).image eB := by rw [hValueB p]
      _ = (F p).image (Sum.inl : P → P ⊕ Tail j) := by
        rw [Finset.image_image, hCompB]

  have hAgreeN : TaggedAmalgam.AgreeBase GA HB :=
    normalGraphs_agree_base G H i j hi hj hAgree
  have hSparseA : GA.IsTwoSparse
      (Finset.univ : Finset (P ⊕ Tail i)) :=
    (normalGraph_twoSparse_iff G i hi).mpr hSparseG
  have hSparseB : HB.IsTwoSparse
      (Finset.univ : Finset (P ⊕ Tail j)) :=
    (normalGraph_twoSparse_iff H j hj).mpr hSparseH

  obtain ⟨t, θ, hSparse, hStrongL, hStrongR,
      hStages, hValuesL, hValuesR⟩ :=
    TaggedAmalgam.exists_taggedFunctionalAmalgam_of_named_base
      GA HB hAgreeN κAN κBN F
      hSparseA hSparseB hStagesA hStagesB
      hBaseValueA hBaseValueB

  refine ⟨t, θ, hSparse, hStrongL, hStrongR, hStages,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact leftAmalgamEmbedding_induced G H i j hi hj hAgree a b
  · intro a b
    exact rightAmalgamEmbedding_induced G H i j hi hj hAgree a b
  · intro p
    exact amalgamEmbeddings_agree_base i j hi hj p
  · intro a b hab
    exact amalgamEmbeddings_identify_only_base i j hi hj hab
  · intro a
    have hRelabel :=
      FiniteC0.canonicalValue_relabel G GA eA hAdjA κA a
    calc
      FiniteC0.canonicalValue K θ (f a) =
          (FiniteC0.canonicalValue GA κAN (eA a)).image
            (TaggedAmalgam.leftTag :
              P ⊕ Tail i → TaggedAmalgam.Carrier P (Tail i) (Tail j)) :=
                hValuesL (eA a)
      _ = ((FiniteC0.canonicalValue G κA a).image eA).image
            (TaggedAmalgam.leftTag :
              P ⊕ Tail i → TaggedAmalgam.Carrier P (Tail i) (Tail j)) := by
        rw [hRelabel]
      _ = (FiniteC0.canonicalValue G κA a).image f := by
        rw [Finset.image_image]
        rfl
  · intro b
    have hRelabel :=
      FiniteC0.canonicalValue_relabel H HB eB hAdjB κB b
    calc
      FiniteC0.canonicalValue K θ (g b) =
          (FiniteC0.canonicalValue HB κBN (eB b)).image
            (TaggedAmalgam.rightTag :
              P ⊕ Tail j → TaggedAmalgam.Carrier P (Tail i) (Tail j)) :=
                hValuesR (eB b)
      _ = ((FiniteC0.canonicalValue H κB b).image eB).image
            (TaggedAmalgam.rightTag :
              P ⊕ Tail j → TaggedAmalgam.Carrier P (Tail i) (Tail j)) := by
        rw [hRelabel]
      _ = (FiniteC0.canonicalValue H κB b).image g := by
        rw [Finset.image_image]
        rfl

end FiniteSpan
end BigHrushovski
