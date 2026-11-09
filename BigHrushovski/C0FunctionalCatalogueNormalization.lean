import BigHrushovski.C0FunctionalFairSuccessor
import BigHrushovski.C0FiniteEquivTransport
import BigHrushovski.CanonicalFinNumbering

/-!
# Encode arbitrary finite C₀ functional extensions in the fair catalogue

The scheduled functional requests are labelled finite structures on
finite ordinals. A finite extension of a current canonical stage may
instead have an arbitrary finite carrier W, and its given source
embedding need not preserve numerical component ranks.

Transport the entire target graph and canonical minimal-component
index along one equivalence W ≃ Fin(card W), then use the induced
source map in those coordinates. The resulting catalogue diagram
has exactly the prescribed old canonical functional presentation
as source. It preserves all target graph nonedges and all complete
unary values, not merely local neighbour records.

This is a FINITE normalization lemma, without a countable generic
structure, fair scheduler or existentially chosen new stage.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- An arbitrary finite canonical functional extension of the
current stage can be encoded as one concrete labelled catalogue
diagram. The target may have an arbitrary finite carrier and its
component index may use a different chronology from the source.

The named source presentation is literally the current finite
model, its new embedding is exactly the original source map
followed by the finite target equivalence, and full target unary
values are transported for every vertex of the target. -/
theorem exists_catalogue_diagram_of_functional_extension
    (s : FiniteFunctionalNatStage)
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : GraphOn W) {r : ℕ} (κ : W → Fin r)
    (hSteps : ∀ j : ℕ, j < r →
      FiniteC0.oldStage κ j = FiniteC0.oldStage κ (j+1) ∨
      K.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ j) (FiniteC0.oldStage κ (j+1)))
    (f : Fin s.size → W)
    (hf : Function.Injective f)
    (hAdj : ∀ x y : Fin s.size,
      s.model.graph.adj x y ↔ K.adj (f x) (f y))
    (hValues : ∀ x : Fin s.size,
      FiniteC0.canonicalValue K κ (f x) =
        (s.model.unaryValue x).image f) :
    ∃ (D : FunctionalC0Diagram
        s.size s.blocks (Fintype.card W) r)
      (e : W ≃ Fin (Fintype.card W)),
      D.source = s.model ∧
      (∀ x : Fin s.size, D.embedding x = e (f x)) ∧
      (∀ x y : W,
        K.adj x y ↔ D.target.graph.adj (e x) (e y)) ∧
      (∀ x : W,
        D.target.unaryValue (e x) =
          (FiniteC0.canonicalValue K κ x).image e) := by
  classical
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let H : GraphOn (Fin (Fintype.card W)) :=
    K.pullback e.symm
  have hAdjE : ∀ x y : W,
      K.adj x y ↔ H.adj (e x) (e y) := by
    intro x y
    change K.adj x y ↔
      K.adj (e.symm (e x)) (e.symm (e y))
    simp
  let κ' := FiniteC0.relabelIndex κ e
  have hStepE : ∀ j : ℕ, j < r →
      FiniteC0.oldStage κ' j =
        FiniteC0.oldStage κ' (j+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ' j)
        (FiniteC0.oldStage κ' (j+1)) :=
    FiniteC0.minimalSteps_relabel K H e hAdjE κ hSteps
  let T : FiniteFunctionalC0 (Fintype.card W) r :=
    ⟨H, κ', hStepE⟩
  let D : FunctionalC0Diagram
      s.size s.blocks (Fintype.card W) r :=
    { source := s.model
      target := T
      embedding := e ∘ f
      inj := e.injective.comp hf
      induced := by
        intro x y
        exact (hAdj x y).trans (hAdjE (f x) (f y))
      values := by
        intro x
        change FiniteC0.canonicalValue H κ' (e (f x)) =
          (s.model.unaryValue x).image (e ∘ f)
        calc
          FiniteC0.canonicalValue H κ' (e (f x)) =
              (FiniteC0.canonicalValue K κ (f x)).image e :=
                FiniteC0.canonicalValue_relabel
                  K H e hAdjE κ (f x)
          _ = ((s.model.unaryValue x).image f).image e := by
                rw [hValues x]
          _ = (s.model.unaryValue x).image (e ∘ f) := by
                rw [Finset.image_image] }
  refine ⟨D, e, rfl, (fun _ => rfl), hAdjE, ?_⟩
  intro x
  exact FiniteC0.canonicalValue_relabel
    K H e hAdjE κ x

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
