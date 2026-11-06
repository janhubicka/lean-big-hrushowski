import BigHrushovski.CFPublishedFraisseRecognition
import BigHrushovski.CFStrongFraisseLimitPresentation

/-!
# The published C_F finite-level graph is the strong Fraisse limit

This theorem combines the *actual* published growth function, the
canonical birth-labelled graph, and the native model-theoretic
characterization of the published countable strong Fraisse limit.

The comparison graph need not be numbered by ℕ. It is given with:
* a countably infinite vertex carrier, witnessed by an enumeration;
* the hereditary finite C_F age condition;
* an increasing covering chain of finite strictly d-closed subgraphs;
* the complete finite strict d-closed induced extension property,
  including the prescribed old image.

These are precisely the limit properties stated in the manuscript
introduction. They do NOT include an isomorphism to the birth graph.
The proof derives the finite strict genericity criterion from them
and invokes the verified birth-graph recognition theorem under the
manuscript's class-level free-amalgamation, empty-base and singleton
hypotheses.

No analytic condition beyond monotone unbounded F with F(0)=0 is
added. Continuity is part of the manuscript's standing assumptions
but not needed in these particular finite numerical inequalities.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- The final published-domain, arbitrary-carrier version of
`M_F^dagger ≅ M_F`:

For every countable strong Fraisse limit of the finite growth class,
specified on its actual vertex type by its finite age, covering
strict d-closed chain and prescribed finite strong extension
property, the birth-labelled canonical level construction is
induced-isomorphic to it.

No reference to the desired isomorphism occurs in any hypothesis.
The only assumptions on the finite class are exactly those in
the manuscript's introduction: restricted d-closed free
amalgamation, strictly closed empty base in each member and
membership of the one-vertex graph. -/
theorem publishedBirth_iso_nativeStrongFraisseLimit
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : HasFiniteClassDClosedFreeJoins
      (publishedCardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass
      (publishedCardinalGrowth F))
    (hSingleton : (F ⟨(1 : ℝ), by norm_num⟩).val ≤ 2)
    {V : Type*} [DecidableEq V]
    (M_F : GraphOn V)
    (hFraisse : StrongFraisseLimitPresentation
      (publishedCardinalGrowth F) M_F) :
    ∃ φ : PublishedBirthVertex F hMono hUnbounded ≃ V,
      ∀ x y : PublishedBirthVertex F hMono hUnbounded,
        (publishedCountableGraph F hMono hUnbounded).adj x y ↔
          M_F.adj (φ x) (φ y) := by
  have hEmptyFinite :
      HasClassDClosedEmpty (publishedCardinalGrowth F) := by
    intro W _ _ H hGrowth
    exact hEmptyClass W H hGrowth
  let hPresented : PresentedStrictGeneric
      (publishedCardinalGrowth F) M_F :=
    (hFraisse.toPresentedFraisseData
      (publishedCardinalGrowth F) M_F).toPresentedStrictGeneric
        (publishedCardinalGrowth F) M_F hEmptyFinite
  exact publishedBirth_iso_presentedStrictGeneric
    F hZero hMono hUnbounded
    hFree hEmptyClass hSingleton M_F hPresented

end CFCoherentTower
end BigHrushovski
