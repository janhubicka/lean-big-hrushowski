import BigHrushovski.C0CoordinateFiniteStageSparsity
import BigHrushovski.C0TwoSidedEmbeddedAmalgam
import BigHrushovski.FiniteTwoFactorValueTransport

/-!
# A finite functional C₀ witness transported across a two-sided amalgam

The existing two-sided finite C₀ amalgamation theorem gives a tagged
free graph K with a canonical finite component index and the exact
whole C-values of both source factors.

Suppose the factor embeddings of a common finite base agree on graph
incidences and complete C-values, and the equivalence from the tagged
carrier to a target finite graph preserves/refects all graph pairs.
If the complete C-values of each source factor transport to the
target, the union has a genuine finite stage/value witness.

The proof uses the generic two-factor coverage theorem to transport
the COMPLETE C-operation at every tagged vertex. The empty-or-minimal
stage certificates and two-sparseness of the factors come from their
actual canonical finite witnesses. No new predimension lemma is added.

The theorem is a conditional finite transport result. The next
Track D step must discharge its graph and C-transport hypotheses for
the literal union of two C-closed raw-host substructures.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {P A B Y : Type*}
variable [Fintype P] [DecidableEq P]
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

/-- A pair of finite canonical functional C₀ presentations admits a
finite canonical stage/value witness on ANY induced finite graph
equivalent to their two-sided free amalgam, provided its entire unary
C-operation agrees with the transported complete C-values on both
factor images. No agreement of numerical component indices across
the base is required. -/
theorem hasCanonicalC0StageValues_of_twoSidedAmalgamEquiv
    (G : GraphOn A) (H : GraphOn B)
    (CA : A → Finset A) (CB : B → Finset B)
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (F : P → Finset P)
    (hBaseA : ∀ p : P, CA (i p) = (F p).image i)
    (hBaseB : ∀ p : P, CB (j p) = (F p).image j)
    (hA : HasCanonicalC0StageValues G CA)
    (hB : HasCanonicalC0StageValues H CB)
    (GY : GraphOn Y) (CY : Y → Finset Y)
    (e : TaggedAmalgam.Carrier P
      (FiniteSpan.Tail i) (FiniteSpan.Tail j) ≃ Y)
    (hGraph : ∀ x y : TaggedAmalgam.Carrier P
        (FiniteSpan.Tail i) (FiniteSpan.Tail j),
      (TaggedAmalgam.freeGraph
        (FiniteSpan.normalGraph G i hi)
        (FiniteSpan.normalGraph H j hj)).adj x y ↔
        GY.adj (e x) (e y))
    (hYLeft : ∀ a : A,
      (CA a).image (e ∘ FiniteSpan.leftAmalgamEmbedding i hi j) =
        CY (e (FiniteSpan.leftAmalgamEmbedding i hi j a)))
    (hYRight : ∀ b : B,
      (CB b).image (e ∘ FiniteSpan.rightAmalgamEmbedding i j hj) =
        CY (e (FiniteSpan.rightAmalgamEmbedding i j hj b))) :
    HasCanonicalC0StageValues GY CY := by
  classical
  have hSparseA : G.IsTwoSparse (Finset.univ : Finset A) :=
    hasCanonicalC0StageValues_twoSparse G CA hA
  have hSparseB : H.IsTwoSparse (Finset.univ : Finset B) :=
    hasCanonicalC0StageValues_twoSparse H CB hB
  obtain ⟨n,κA,hStepsA,hCA⟩ := hA
  obtain ⟨m,κB,hStepsB,hCB⟩ := hB
  have hNamedA : ∀ p : P,
      FiniteC0.canonicalValue G κA (i p) = (F p).image i := by
    intro p
    rw [hCA (i p)]
    exact hBaseA p
  have hNamedB : ∀ p : P,
      FiniteC0.canonicalValue H κB (j p) = (F p).image j := by
    intro p
    rw [hCB (j p)]
    exact hBaseB p
  let K : GraphOn (TaggedAmalgam.Carrier P
      (FiniteSpan.Tail i) (FiniteSpan.Tail j)) :=
    TaggedAmalgam.freeGraph
      (FiniteSpan.normalGraph G i hi)
      (FiniteSpan.normalGraph H j hj)
  let f : A → TaggedAmalgam.Carrier P
      (FiniteSpan.Tail i) (FiniteSpan.Tail j) :=
    FiniteSpan.leftAmalgamEmbedding i hi j
  let g : B → TaggedAmalgam.Carrier P
      (FiniteSpan.Tail i) (FiniteSpan.Tail j) :=
    FiniteSpan.rightAmalgamEmbedding i j hj
  obtain ⟨t,θ,_hSparse,_hStrongL,_hStrongR,hStages,
      _hInducedA,_hInducedB,_hBaseCoincides,_hIdentifiesOnlyBase,
      hCompleteA,hCompleteB⟩ :=
    FiniteSpan.exists_twoSidedCanonicalFunctionalAmalgam
      G H i j hi hj hAgree hSparseA hSparseB
      κA κB hStepsA hStepsB F hNamedA hNamedB
  have hYSourceA : ∀ a : A,
      (FiniteC0.canonicalValue G κA a).image (e ∘ f) =
        CY (e (f a)) := by
    intro a
    rw [hCA a]
    exact hYLeft a
  have hYSourceB : ∀ b : B,
      (FiniteC0.canonicalValue H κB b).image (e ∘ g) =
        CY (e (g b)) := by
    intro b
    rw [hCB b]
    exact hYRight b
  have hCompleteTransport : ∀ x : TaggedAmalgam.Carrier P
      (FiniteSpan.Tail i) (FiniteSpan.Tail j),
      (FiniteC0.canonicalValue K θ x).image e = CY (e x) := by
    exact FiniteFunctionalTransfer.completeValues_transport_of_two_factor_cover
      f g e (FiniteC0.canonicalValue G κA)
      (FiniteC0.canonicalValue H κB)
      (FiniteC0.canonicalValue K θ) CY
      (FiniteFunctionalTransfer.normalizedAmalgam_twoFactor_cover
        i j hi hj)
      hCompleteA hCompleteB hYSourceA hYSourceB
  exact hasCanonicalC0StageValues_equiv K GY
    (FiniteC0.canonicalValue K θ) CY e hGraph hCompleteTransport
    ⟨t, θ, hStages, fun _ => rfl⟩

end FiniteUnaryCoordinates
end BigHrushovski
