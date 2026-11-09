import BigHrushovski.C0FunctionalFairResponseLimit
import BigHrushovski.C0FunctionalCatalogueNormalization

/-!
# Functional extension property of the actual fair countable C₀ limit

The fair finite recursion has been constructed, its finite graph and
complete unary operations form a coherent countable limit, and every
catalogued request applicable at one finite stage is eventually
answered in that limit.

We now normalize an *arbitrary* finite canonical functional extension
over a literal stage of the countable limit to one catalogue request.
The source component index used in that extension need not agree
with the index chosen by the construction. They induce the same
complete unary operation, so their one-generated values agree
exactly; an injective literal subtype map reflects this equality.

The finite target's arbitrary carrier is relabelled to a finite
ordinal by the certified request-normalization theorem. Fair
recurrence supplies the exact target embedding into the countable
limit, retaining every old numeric label, all induced edges and
nonedges and all complete unary values.

This should discharge the last genuine functional Fraïssé
extension-property premise and identify the graph reduct with M₀.
This lemma has a separate role-separated adversarial review in
`docs/C0_UNCONDITIONAL_FUNCTIONAL_GENERIC_ADVERSARIAL_20261108.md`.
The result is not to be marked verified before the full exact
Lean kernel and adversarial audits pass.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- Any finite canonical functional extension of a literal stage of
the constructed coherent limit is realized over precisely the given
stage vertices. The source may be presented by a different
minimal-component chronology, provided the complete unary values
agree with the actual limit function. -/
theorem exists_functionalStageExtension_in_fair_limit
    (n p : ℕ)
    (κOld : {v : ℕ // v ∈ fairGraphStages.stage n} → Fin p)
    (hOldValues : ∀ v : {v : ℕ // v ∈ fairGraphStages.stage n},
      fairUnaryStages.limitValue v.val =
        (FiniteC0.canonicalValue
          (fairGraphStages.limitGraph.pullback
            (Subtype.val :
              {v : ℕ // v ∈ fairGraphStages.stage n} → ℕ))
          κOld v).image
            (Subtype.val :
              {v : ℕ // v ∈ fairGraphStages.stage n} → ℕ))
    {W : Type} [Fintype W] [DecidableEq W]
    (K : GraphOn W) {q : ℕ} (κ : W → Fin q)
    (hNewStages : ∀ j : ℕ, j < q →
      FiniteC0.oldStage κ j = FiniteC0.oldStage κ (j+1) ∨
      K.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ j)
        (FiniteC0.oldStage κ (j+1)))
    (f : {v : ℕ // v ∈ fairGraphStages.stage n} → W)
    (hf : Function.Injective f)
    (hAdj : ∀ u v : {v : ℕ // v ∈ fairGraphStages.stage n},
      fairGraphStages.limitGraph.adj u.val v.val ↔
        K.adj (f u) (f v))
    (hOldFullValues : ∀ u : {v : ℕ // v ∈ fairGraphStages.stage n},
      FiniteC0.canonicalValue K κ (f u) =
        (FiniteC0.canonicalValue
          (fairGraphStages.limitGraph.pullback
            (Subtype.val :
              {v : ℕ // v ∈ fairGraphStages.stage n} → ℕ))
          κOld u).image f) :
    ∃ g : W → ℕ,
      Function.Injective g ∧
      (∀ x y : W,
        K.adj x y ↔ fairGraphStages.limitGraph.adj (g x) (g y)) ∧
      (∀ u : {v : ℕ // v ∈ fairGraphStages.stage n},
        g (f u) = u.val) ∧
      (∀ x : W,
        fairUnaryStages.limitValue (g x) =
          (FiniteC0.canonicalValue K κ x).image g) := by
  classical
  let s := fairStages n
  let T := {v : ℕ // v ∈ fairGraphStages.stage n}
  let e : Fin s.size ≃ T := finRangeEquiv s.size
  let G : GraphOn T :=
    fairGraphStages.limitGraph.pullback (Subtype.val : T → ℕ)
  have hOldGraph : ∀ x y : Fin s.size,
      s.model.graph.adj x y ↔
        K.adj (f (e x)) (f (e y)) := by
    intro x y
    calc
      s.model.graph.adj x y ↔
          s.natGraph.adj x.val y.val :=
            s.natGraph_induced x y
      _ ↔ fairGraphStages.limitGraph.adj
          (e x).val (e y).val := by
            have hx : x.val ∈ fairGraphStages.stage n :=
              Finset.mem_range.mpr x.isLt
            have hy : y.val ∈ fairGraphStages.stage n :=
              Finset.mem_range.mpr y.isLt
            exact (fairGraphStages.limitGraph_induced n hx hy).symm
      _ ↔ K.adj (f (e x)) (f (e y)) := hAdj (e x) (e y)
  have hOldComplete : ∀ x : Fin s.size,
      FiniteC0.canonicalValue G κOld (e x) =
        (s.model.unaryValue x).image e := by
    intro x
    have hxValue :
        fairUnaryStages.limitValue x.val =
          (s.model.unaryValue x).image
            (fun z : Fin s.size => z.val) := by
      calc
        fairUnaryStages.limitValue x.val = s.natValue x.val :=
          fairUnaryStages.limitValue_eq_stage n x.val x.isLt
        _ = (s.model.unaryValue x).image
            (fun z : Fin s.size => z.val) :=
          s.natValue_inside x.val x.isLt
    have hOtherImage :
        ((s.model.unaryValue x).image e).image
            (Subtype.val : T → ℕ) =
          (s.model.unaryValue x).image
            (fun z : Fin s.size => z.val) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro y hy
      rfl
    have hImage :
        (FiniteC0.canonicalValue G κOld (e x)).image
            (Subtype.val : T → ℕ) =
        ((s.model.unaryValue x).image e).image
            (Subtype.val : T → ℕ) := by
      calc
        (FiniteC0.canonicalValue G κOld (e x)).image
            (Subtype.val : T → ℕ) =
          fairUnaryStages.limitValue (e x).val :=
            (hOldValues (e x)).symm
        _ = (s.model.unaryValue x).image
            (fun z : Fin s.size => z.val) := hxValue
        _ = ((s.model.unaryValue x).image e).image
            (Subtype.val : T → ℕ) := hOtherImage.symm
    exact (Finset.image_injective
      (Subtype.val_injective : Function.Injective (Subtype.val : T → ℕ)))
        hImage
  let fFin : Fin s.size → W := f ∘ e
  have hfFin : Function.Injective fFin := hf.comp e.injective
  have hValuesFin : ∀ x : Fin s.size,
      FiniteC0.canonicalValue K κ (fFin x) =
        (s.model.unaryValue x).image fFin := by
    intro x
    calc
      FiniteC0.canonicalValue K κ (fFin x) =
        (FiniteC0.canonicalValue G κOld (e x)).image f :=
          hOldFullValues (e x)
      _ = ((s.model.unaryValue x).image e).image f := by
            rw [hOldComplete x]
      _ = (s.model.unaryValue x).image fFin := by
            rw [Finset.image_image]
  obtain ⟨D, label, hSource, hEmbed, hTargetGraph, hTargetValues⟩ :=
    exists_catalogue_diagram_of_functional_extension
      s K κ hNewStages fFin hfFin hOldGraph hValuesFin
  let req : FunctionalC0RequestCatalogue :=
    ⟨s.size, s.blocks, Fintype.card W, q,
      (D, (fun x : Fin s.size => x.val))⟩
  have hApp : s.Applies req := by
    refine ⟨(fun x : Fin s.size => x),
      (fun _ _ h => h), ?_, ?_, ?_⟩
    · intro x
      rfl
    · intro x y
      change D.source.graph.adj x y ↔
        s.model.graph.adj x y
      rw [hSource]
    · intro x
      change s.model.unaryValue x =
        (D.source.unaryValue x).image (fun y : Fin s.size => y)
      rw [hSource]
      simp
  obtain ⟨answer, hAnswerInj, hAnswerGraph,
      hAnswerValues, hAnswerBase⟩ :=
    eventually_answered_in_fair_limit req n hApp
  let g : W → ℕ := answer ∘ label
  refine ⟨g, hAnswerInj.comp label.injective,
    ?_, ?_, ?_⟩
  · intro x y
    exact (hTargetGraph x y).trans
      (hAnswerGraph (label x) (label y))
  · intro u
    let x : Fin s.size := e.symm u
    have he : e x = u := e.apply_symm_apply u
    calc
      g (f u) = answer (label (f (e x))) := by
        rw [he]
        rfl
      _ = answer (D.embedding x) :=
        congrArg answer (hEmbed x).symm
      _ = req.labels x := hAnswerBase x
      _ = u.val := by
        have hv := congrArg Subtype.val he
        change x.val = u.val at hv
        exact hv
  · intro x
    calc
      fairUnaryStages.limitValue (g x) =
          (D.target.unaryValue (label x)).image answer :=
            hAnswerValues (label x)
      _ = ((FiniteC0.canonicalValue K κ x).image label).image
          answer := by
            rw [hTargetValues x]
      _ = (FiniteC0.canonicalValue K κ x).image g := by
            rw [Finset.image_image]

/-- All finite functional extensions over literal canonical
stages of the actually constructed countable C₀ presentation
are realized over their given old labels. No independent
functional Fraïssé limit is assumed. -/
theorem fairLimit_hasFunctionalStageExtension :
    FiniteC0.HasCanonicalStageExtensionProperty
      fairGraphStages.limitGraph
      fairUnaryStages.limitValue
      fairGraphStages.stage := by
  classical
  intro n p κOld hOldStages hOldValues
  intro W _ _ K q κ hNewStages f hf hAdj hOldFullValues
  exact exists_functionalStageExtension_in_fair_limit
    n p κOld hOldValues K κ hNewStages f hf hAdj hOldFullValues

/-- The graph reduct of the actually constructed countable
functional C₀ Fraïssé limit is induced-isomorphic to the
already verified countable strong generic M₀. -/
theorem fairLimitReduct_isomorphic_M0 :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      FiniteCatalogue.genericTwoSparseGraph.adj x y ↔
        fairGraphStages.limitGraph.adj (e x) (e y) := by
  exact fairCoherentC0Stages.limit_reduct_iso_generic_of_functionalExtension
    fairLimit_hasFunctionalStageExtension

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
