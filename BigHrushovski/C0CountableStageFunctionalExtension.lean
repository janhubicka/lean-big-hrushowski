import BigHrushovski.C0CountableFunctionalStrongImages
import BigHrushovski.C0FiniteStrongSpanFunctional
import BigHrushovski.GenericityCriterion

/-!
# From a countable C₀ functional extension property to strong graph genericity

The finite tagged strong-span lift works over any strongly embedded
graph base A, even when A is not closed under the unary function.
A functional extension property, however, must be applied over a
functionally closed finite source. We therefore choose a finite
canonical stage S containing the actual image of A, lift the graph
strong span A → S and A → B to a finite canonical functional
extension K of S, and realize K over S.

Exact preservation of complete unary values makes the realized
finite image functionally closed. Its graph reduct is consequently
globally strong, and so is the induced copy of B. The original
labelled graph map A→N is retained pointwise throughout.

The missing work for the final unconditional C₀ theorem is to
construct a countable functional Fraïssé limit with the stage
extension property below. That property is an EXPLICIT assumption
in this module, not a conclusion of finite amalgamation alone.
-/

namespace BigHrushovski
namespace FiniteC0

/-- Functional extension property over each literal canonical stage.
Every finite canonical extension preserving the original complete
unary values can be realized over the chosen stage, with the same
old vertices, graph edges and nonedges, and every complete new
unary value. This is the Fraïssé extension property restricted to
the cofinal finite canonical stages, not a graph extension axiom. -/
def HasCanonicalStageExtensionProperty
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ) : Prop :=
  ∀ (n p : ℕ)
    (κOld : {v : ℕ // v ∈ stage n} → Fin p)
    (hOldStages : ∀ k : ℕ, k < p →
      oldStage κOld k = oldStage κOld (k+1) ∨
      ((N.pullback (Subtype.val :
        {v : ℕ // v ∈ stage n} → ℕ)).toPredimension).IsMinimalStrongStep
        (oldStage κOld k) (oldStage κOld (k+1)))
    (hOldValues : ∀ v : {v : ℕ // v ∈ stage n},
      C v.val =
        (canonicalValue
          (N.pullback (Subtype.val : {v : ℕ // v ∈ stage n} → ℕ))
          κOld v).image
            (Subtype.val : {v : ℕ // v ∈ stage n} → ℕ)),
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (K : GraphOn W) (q : ℕ) (κ : W → Fin q)
      (hNewStages : ∀ k : ℕ, k < q →
        oldStage κ k = oldStage κ (k+1) ∨
        K.toPredimension.IsMinimalStrongStep
          (oldStage κ k) (oldStage κ (k+1)))
      (f : {v : ℕ // v ∈ stage n} → W)
      (hf : Function.Injective f)
      (hAdj : ∀ u v : {v : ℕ // v ∈ stage n},
        N.adj u.val v.val ↔ K.adj (f u) (f v))
      (hOldFullValues : ∀ u : {v : ℕ // v ∈ stage n},
        canonicalValue K κ (f u) =
          (canonicalValue
            (N.pullback (Subtype.val :
              {v : ℕ // v ∈ stage n} → ℕ)) κOld u).image f),
      ∃ g : W → ℕ,
        Function.Injective g ∧
        (∀ x y : W, K.adj x y ↔ N.adj (g x) (g y)) ∧
        (∀ u : {v : ℕ // v ∈ stage n}, g (f u) = u.val) ∧
        (∀ x : W, C (g x) = (canonicalValue K κ x).image g)

/-- A functional extension over one finite canonical stage is
sufficient to answer any finite *graph-strong* diagram over a
prescribed graph-strong source map. The source map need not be
closed under the unary operation. -/
theorem exists_strongGraphResponse_of_stageFunctionalExtension
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStages : HasCanonicalFiniteStages N C stage)
    (hFunctionalExt : HasCanonicalStageExtensionProperty N C stage)
    {P B : Type*} [Fintype P] [Fintype B]
    [DecidableEq P] [DecidableEq B]
    (H : GraphOn B)
    (i : P → ℕ) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      N.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (hGlobal : N.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset P).image i))
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset B))
    (hStrongH : H.toPredimension.IsStrong
      ((Finset.univ : Finset P).image j) Finset.univ) :
    ∃ g : B → ℕ,
      Function.Injective g ∧
      (∀ x y : B, H.adj x y ↔ N.adj (g x) (g y)) ∧
      (∀ p : P, g (j p) = i p) ∧
      N.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset B).image g) := by
  classical
  let a : Finset ℕ := (Finset.univ : Finset P).image i
  obtain ⟨n, hStageContains⟩ := hCover a
  let T := {v : ℕ // v ∈ stage n}
  let G : GraphOn T := N.pullback (Subtype.val : T → ℕ)
  let iT : P → T := fun p =>
    ⟨i p, hStageContains (Finset.mem_image.mpr
      ⟨p, Finset.mem_univ _, rfl⟩)⟩
  have hiT : Function.Injective iT := by
    intro p q hpq
    exact hi (congrArg Subtype.val hpq)
  obtain ⟨k, κOld, hOldStages, hOldValues⟩ := hStages n
  have hImageT :
      (Finset.univ : Finset T).image (Subtype.val : T → ℕ) =
        stage n := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, _, hEq⟩ := Finset.mem_image.mp hx
      exact hEq ▸ u.property
    · intro hx
      exact Finset.mem_image.mpr
        ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have hImageiT :
      (((Finset.univ : Finset P).image iT).image
        (Subtype.val : T → ℕ)) = a := by
    simp [a, Finset.image_image, Function.comp_def, iT]
  have hAdjT : ∀ u v : T,
      G.adj u v ↔ N.adj u.val v.val := by
    intro u v
    rfl
  have hStageSparse : N.IsTwoSparse (stage n) := by
    intro s _
    exact sparse_of_canonicalFiniteStages
      N C stage hCover hStages s
  have hSparseG : G.IsTwoSparse (Finset.univ : Finset T) := by
    apply (G.twoSparse_image_iff N
      (Subtype.val : T → ℕ) Subtype.val_injective
      hAdjT Finset.univ).mp
    rw [hImageT]
    exact hStageSparse
  have hStrongN : N.toPredimension.IsStrong a (stage n) :=
    hGlobal (stage n) hStageContains
  have hStrongG : G.toPredimension.IsStrong
      ((Finset.univ : Finset P).image iT) Finset.univ := by
    apply (G.strong_image_iff N
      (Subtype.val : T → ℕ) Subtype.val_injective hAdjT
      ((Finset.univ : Finset P).image iT) Finset.univ
      (Finset.subset_univ _)).mp
    rw [hImageiT, hImageT]
    exact hStrongN
  have hAgreeG : ∀ p q : P,
      G.adj (iT p) (iT q) ↔ H.adj (j p) (j q) :=
    fun p q => hAgree p q
  obtain ⟨K, f, g, m, κK, hf, hg,
    hAdjF, hAdjG, hBase, _, hSparseK, hStrongF,
    hStrongB, hStepsK, hValuesK⟩ :=
    FiniteSpan.exists_canonical_functional_strong_amalgam
      G H iT j hiT hj hAgreeG hSparseG hSparseH
      hStrongG hStrongH κOld hOldStages
  have hAdjOld : ∀ u v : T,
      N.adj u.val v.val ↔ K.adj (f u) (f v) :=
    fun u v => hAdjF u v
  obtain ⟨e, he, hAdjE, hOnOld, hValuesE⟩ :=
    hFunctionalExt n k κOld hOldStages hOldValues
      K m κK hStepsK f hf hAdjOld hValuesK
  let result : B → ℕ := e ∘ g
  have hResultStrong : N.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset B).image result) := by
    have hCopyStrong :=
      globallyStrong_image_of_completeFunctionalEmbedding
        N C stage hCover hStages K κK e he hAdjE
        hValuesE ((Finset.univ : Finset B).image g) hStrongB
    simpa [result, Finset.image_image, Function.comp_def]
      using hCopyStrong
  refine ⟨result, he.comp hg, ?_, ?_, hResultStrong⟩
  · intro x y
    exact (hAdjG x y).trans (hAdjE (g x) (g y))
  · intro p
    change e (g (j p)) = i p
    calc
      e (g (j p)) = e (f (iT p)) :=
        congrArg e (hBase p).symm
      _ = (iT p).val := hOnOld (iT p)
      _ = i p := rfl

/-- Strong graph extension of every labelled finite request follows
from the *functional* extension property over canonical stages.
The starting graph base is only strong, not functionally closed. -/
theorem strongExtension_of_canonicalStageFunctionalExtension
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStages : HasCanonicalFiniteStages N C stage)
    (hFunctionalExt : HasCanonicalStageExtensionProperty N C stage) :
    FiniteCatalogue.HasStrongExtensionProperty N := by
  intro req hApplicable
  obtain ⟨hInj, hInd, hGlob⟩ := hApplicable
  let D := req.2.2.1
  let i := req.2.2.2
  have hAgree : ∀ p q : Fin req.1,
      N.adj (i p) (i q) ↔
        D.target.adj (D.embedding p) (D.embedding q) := by
    intro p q
    exact (hInd p q).symm.trans (D.induced p q)
  obtain ⟨g, hg, hAdj, hOld, hStrong⟩ :=
    exists_strongGraphResponse_of_stageFunctionalExtension
      N C stage hCover hStages hFunctionalExt
      D.target i D.embedding hInj D.inj
      hAgree hGlob D.sparseTarget D.strong
  exact ⟨g, hg, hAdj, hOld, hStrong⟩

/-- Countable C₀ reduct recognition from the finite canonical
stages and the genuine functional Fraïssé extension property.
The latter still has to be constructed: this theorem proves
the exact transfer to the strong graph generic M₀. -/
theorem graphReduct_iso_generic_of_functionalStageExtension
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStages : HasCanonicalFiniteStages N C stage)
    (hFunctionalExt : HasCanonicalStageExtensionProperty N C stage) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      FiniteCatalogue.genericTwoSparseGraph.adj x y ↔
        N.adj (e x) (e y) := by
  exact graphReduct_iso_generic_of_canonicalStages_and_extension
    N C stage hCover hStages
    (strongExtension_of_canonicalStageFunctionalExtension
      N C stage hCover hStages hFunctionalExt)

end FiniteC0
end BigHrushovski
