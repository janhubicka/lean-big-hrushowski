import BigHrushovski.CFPublishedStrongFraisseIdentification
import BigHrushovski.CFStandardFraisseExtension

/-!
# The complete manuscript-level C_F generic identification

The paper's countable M_F is a Fraisse limit for the finite
growth class with strictly d-closed embeddings. Its defining
properties are the finite age, a covering chain of finite
strictly d-closed subgraphs and the *standard arbitrary-finite*
strong extension property. No numerical re-labelling, new
semantic extension axiom or pre-existing isomorphism to the
canonical birth graph is needed.

The singleton and empty-base assumptions ensure the canonical
birth construction is infinite, and the finite d-closed
free-amalgamation property ensures every finite stage is in C_F.
The standard finite extension property is converted to the
literal Nat-interval interface by the separately verified
finite-subtype transport, then the strict countable
back-and-forth theorem yields the required isomorphism.

This theorem is conditional only on the **defining**
Fraisse-limit properties of its comparison graph, precisely
as the paper describes M_F. Constructing that Fraisse limit
is not repeated here: the manuscript takes its existence
from the earlier sparse graphs paper.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- Let M_F be any countably infinite strong Fraisse limit of
the published C_F class, on its original vertex type and
with its standard finite strong extension property. Then
the actual canonical birth-labelled C_F graph is induced-
isomorphic to M_F, under exactly the paper's assumptions.

There is **no** hypothesis referring to the desired
isomorphism, the constructed birth graph, an independently
chosen generalized inverse, or nonempty requests at each
stage. -/
theorem publishedBirth_iso_standardStrongFraisseLimit
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
    (hFraisse : StandardStrongFraisseLimitPresentation
      (publishedCardinalGrowth F) M_F) :
    ∃ φ : PublishedBirthVertex F hMono hUnbounded ≃ V,
      ∀ x y : PublishedBirthVertex F hMono hUnbounded,
        (publishedCountableGraph F hMono hUnbounded).adj x y ↔
          M_F.adj (φ x) (φ y) := by
  exact publishedBirth_iso_nativeStrongFraisseLimit
    F hZero hMono hUnbounded hFree hEmptyClass
    hSingleton M_F
    (hFraisse.toNative (publishedCardinalGrowth F) M_F)

end CFCoherentTower
end BigHrushovski
