import BigHrushovski.C0FiniteFunctionalCatalogue
import BigHrushovski.C0FiniteEquivTransport
import BigHrushovski.C0TaggedFullFunctionalAmalgam

/-!
# Arbitrary C₀ functional spans in literal tagged normal form

The tagged two-sided functional free-amalgamation theorem was proved
for two presentations on P ⊕ L and P ⊕ R sharing the *literal* base P.
A functional amalgamation request in the Fraïssé construction has
arbitrary injective base maps i:P→A and j:P→B.

The split equivalences already certified in SpanNormalization
identify A with P ⊕ Tail(i) and B with P ⊕ Tail(j). We transfer
the entire canonical component index and complete unary values
through those equivalences. In particular, equality of the named
unary values on P supplies exactly the shared-base hypotheses of
the tagged amalgamation theorem; no agreement of numerical ranks
is needed.

The resulting finite carrier, graph and component index are explicit.
All graph maps are induced and the two complete vertex-valued unary
functions agree exactly with the images of the originals. This is
a finite theorem; it does not construct countable responding stages.
-/

namespace BigHrushovski
namespace FiniteSpan

variable {P A B : Type*}
variable [Fintype P] [Fintype A] [Fintype B]
variable [DecidableEq P] [DecidableEq A] [DecidableEq B]
variable {n m : ℕ}

/-- A split equivalence sends the literal name of every old base
vertex back to the corresponding canonical first-summand tag. -/
theorem splitEquiv_symm_base
    (i : P → A) (hi : Function.Injective i) (p : P) :
    (splitEquiv i hi).symm (i p) =
      (Sum.inl p : P ⊕ Tail i) := by
  let e := splitEquiv i hi
  calc
    e.symm (i p) = e.symm (e (.inl p)) := by
      exact congrArg e.symm (splitEquiv_inl i hi p).symm
    _ = .inl p := e.symm_apply_apply _

/-- Exact transport of a complete named base unary value through
the arbitrary carrier split P ⊕ Tail(i). No assumption that the
original base is an initial component segment is used. -/
theorem normalGraph_namedBase_canonicalValue
    (G : GraphOn A) (i : P → A) (hi : Function.Injective i)
    (κ : A → Fin n) (F : P → Finset P)
    (hNamed : ∀ p : P,
      FiniteC0.canonicalValue G κ (i p) = (F p).image i)
    (p : P) :
    FiniteC0.canonicalValue (normalGraph G i hi)
      (FiniteC0.relabelIndex κ (splitEquiv i hi).symm)
      (.inl p) =
      (F p).image (Sum.inl : P → P ⊕ Tail i) := by
  classical
  let e : A ≃ (P ⊕ Tail i) := (splitEquiv i hi).symm
  have hAdj : ∀ u v : A,
      G.adj u v ↔ (normalGraph G i hi).adj (e u) (e v) := by
    intro u v
    change G.adj u v ↔
      G.adj ((splitEquiv i hi) (e u))
        ((splitEquiv i hi) (e v))
    simp [e]
  have hVal :=
    FiniteC0.canonicalValue_relabel
      G (normalGraph G i hi) e hAdj κ (i p)
  have hBase : ∀ p : P, e (i p) = (.inl p : P ⊕ Tail i) := by
    intro q
    exact splitEquiv_symm_base i hi q
  calc
    FiniteC0.canonicalValue (normalGraph G i hi)
        (FiniteC0.relabelIndex κ (splitEquiv i hi).symm) (.inl p)
      = (FiniteC0.canonicalValue G κ (i p)).image e := by
          simpa only [hBase p] using hVal
    _ = ((F p).image i).image e := by rw [hNamed p]
    _ = (F p).image (Sum.inl : P → P ⊕ Tail i) := by
        rw [Finset.image_image]
        have hFun : e ∘ i = (Sum.inl : P → P ⊕ Tail i) := by
          funext q
          exact hBase q
        rw [hFun]

/-- The verified two-sided tagged finite theorem applies to any
abstract span of finite canonical C₀ structures whose complete
unary values agree on the prescribed common named base. The
original input component orders may differ on P.

The conclusion uses the explicit tagged carrier of both split
normal forms. We retain the full input graph data, not merely
positive edges. -/
theorem exists_normalized_canonicalFunctionalAmalgam
    (G : GraphOn A) (H : GraphOn B)
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (κA : A → Fin n) (κB : B → Fin m)
    (hStepsA : ∀ k : ℕ, k < n →
      FiniteC0.oldStage κA k =
        FiniteC0.oldStage κA (k + 1) ∨
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κA k)
        (FiniteC0.oldStage κA (k + 1)))
    (hStepsB : ∀ k : ℕ, k < m →
      FiniteC0.oldStage κB k =
        FiniteC0.oldStage κB (k + 1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κB k)
        (FiniteC0.oldStage κB (k + 1)))
    (F : P → Finset P)
    (hNamedA : ∀ p : P,
      FiniteC0.canonicalValue G κA (i p) = (F p).image i)
    (hNamedB : ∀ p : P,
      FiniteC0.canonicalValue H κB (j p) = (F p).image j)
    (hSparseA : G.IsTwoSparse (Finset.univ : Finset A))
    (hSparseB : H.IsTwoSparse (Finset.univ : Finset B)) :
    let L := normalGraph G i hi
    let R := normalGraph H j hj
    let K := TaggedAmalgam.freeGraph L R
    let eA := (splitEquiv i hi).symm
    let eB := (splitEquiv j hj).symm
    ∃ (t : ℕ)
      (θ : TaggedAmalgam.Carrier P (Tail i) (Tail j) → Fin t),
      K.IsTwoSparse Finset.univ ∧
      K.toPredimension.IsStrong
        (TaggedAmalgam.leftDomain :
          Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j)))
        Finset.univ ∧
      K.toPredimension.IsStrong
        (TaggedAmalgam.rightDomain :
          Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j)))
        Finset.univ ∧
      (∀ k : ℕ, k < t →
        FiniteC0.oldStage θ k = FiniteC0.oldStage θ (k+1) ∨
        K.toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage θ k) (FiniteC0.oldStage θ (k+1))) ∧
      (∀ x y : A,
        G.adj x y ↔
          K.adj (TaggedAmalgam.leftTag (eA x))
            (TaggedAmalgam.leftTag (eA y))) ∧
      (∀ x y : B,
        H.adj x y ↔
          K.adj (TaggedAmalgam.rightTag (eB x))
            (TaggedAmalgam.rightTag (eB y))) ∧
      (∀ x : A,
        FiniteC0.canonicalValue K θ
            (TaggedAmalgam.leftTag (eA x)) =
          (FiniteC0.canonicalValue G κA x).image
            (fun y => TaggedAmalgam.leftTag (eA y))) ∧
      (∀ x : B,
        FiniteC0.canonicalValue K θ
            (TaggedAmalgam.rightTag (eB x)) =
          (FiniteC0.canonicalValue H κB x).image
            (fun y => TaggedAmalgam.rightTag (eB y))) := by
  classical
  let eA : A ≃ (P ⊕ Tail i) := (splitEquiv i hi).symm
  let eB : B ≃ (P ⊕ Tail j) := (splitEquiv j hj).symm
  let L := normalGraph G i hi
  let R := normalGraph H j hj
  let K := TaggedAmalgam.freeGraph L R
  let κL := FiniteC0.relabelIndex κA eA
  let κR := FiniteC0.relabelIndex κB eB
  have hAdjA : ∀ x y : A, G.adj x y ↔ L.adj (eA x) (eA y) := by
    intro x y
    change G.adj x y ↔ G.adj ((splitEquiv i hi) (eA x))
      ((splitEquiv i hi) (eA y))
    simp [eA]
  have hAdjB : ∀ x y : B, H.adj x y ↔ R.adj (eB x) (eB y) := by
    intro x y
    change H.adj x y ↔ H.adj ((splitEquiv j hj) (eB x))
      ((splitEquiv j hj) (eB y))
    simp [eB]
  have hSparseL : L.IsTwoSparse Finset.univ :=
    (normalGraph_twoSparse_iff G i hi).mpr hSparseA
  have hSparseR : R.IsTwoSparse Finset.univ :=
    (normalGraph_twoSparse_iff H j hj).mpr hSparseB
  have hLeftSteps : ∀ k : ℕ, k < n →
      FiniteC0.oldStage κL k = FiniteC0.oldStage κL (k+1) ∨
      L.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κL k) (FiniteC0.oldStage κL (k+1)) :=
    FiniteC0.minimalSteps_relabel G L eA hAdjA κA hStepsA
  have hRightSteps : ∀ k : ℕ, k < m →
      FiniteC0.oldStage κR k = FiniteC0.oldStage κR (k+1) ∨
      R.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κR k) (FiniteC0.oldStage κR (k+1)) :=
    FiniteC0.minimalSteps_relabel H R eB hAdjB κB hStepsB
  have hBaseAgree : TaggedAmalgam.AgreeBase L R :=
    normalGraphs_agree_base G H i j hi hj hAgree
  have hBaseL : ∀ p : P,
      FiniteC0.canonicalValue L κL (.inl p) =
        (F p).image (Sum.inl : P → P ⊕ Tail i) := by
    intro p
    exact normalGraph_namedBase_canonicalValue G i hi κA F hNamedA p
  have hBaseR : ∀ p : P,
      FiniteC0.canonicalValue R κR (.inl p) =
        (F p).image (Sum.inl : P → P ⊕ Tail j) := by
    intro p
    exact normalGraph_namedBase_canonicalValue H j hj κB F hNamedB p
  obtain ⟨t, θ, hSparse, hStrongL, hStrongR, hStages,
      hValueL, hValueR⟩ :=
    TaggedAmalgam.exists_taggedFunctionalAmalgam_of_named_base
      L R hBaseAgree κL κR F hSparseL hSparseR
      hLeftSteps hRightSteps hBaseL hBaseR
  refine ⟨t, θ, hSparse, hStrongL, hStrongR, hStages,
    ?_, ?_, ?_, ?_⟩
  · intro x y
    exact (hAdjA x y).trans
      (TaggedAmalgam.freeGraph_left L R hBaseAgree (eA x) (eA y)).symm
  · intro x y
    exact (hAdjB x y).trans
      (TaggedAmalgam.freeGraph_right L R hBaseAgree (eB x) (eB y)).symm
  · intro x
    calc
      FiniteC0.canonicalValue K θ
          (TaggedAmalgam.leftTag (eA x)) =
        (FiniteC0.canonicalValue L κL (eA x)).image
          (TaggedAmalgam.leftTag :
            (P ⊕ Tail i) → TaggedAmalgam.Carrier P (Tail i) (Tail j)) :=
        hValueL (eA x)
      _ = ((FiniteC0.canonicalValue G κA x).image eA).image
          (TaggedAmalgam.leftTag :
            (P ⊕ Tail i) → TaggedAmalgam.Carrier P (Tail i) (Tail j)) := by
        rw [FiniteC0.canonicalValue_relabel G L eA hAdjA κA x]
      _ = (FiniteC0.canonicalValue G κA x).image
          (fun y => TaggedAmalgam.leftTag (eA y)) := by
        rw [Finset.image_image]
        rfl
  · intro x
    calc
      FiniteC0.canonicalValue K θ
          (TaggedAmalgam.rightTag (eB x)) =
        (FiniteC0.canonicalValue R κR (eB x)).image
          (TaggedAmalgam.rightTag :
            (P ⊕ Tail j) → TaggedAmalgam.Carrier P (Tail i) (Tail j)) :=
        hValueR (eB x)
      _ = ((FiniteC0.canonicalValue H κB x).image eB).image
          (TaggedAmalgam.rightTag :
            (P ⊕ Tail j) → TaggedAmalgam.Carrier P (Tail i) (Tail j)) := by
        rw [FiniteC0.canonicalValue_relabel H R eB hAdjB κB x]
      _ = (FiniteC0.canonicalValue H κB x).image
          (fun y => TaggedAmalgam.rightTag (eB y)) := by
        rw [Finset.image_image]
        rfl

end FiniteSpan
end BigHrushovski
