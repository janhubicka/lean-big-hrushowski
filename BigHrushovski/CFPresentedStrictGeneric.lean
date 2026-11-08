import BigHrushovski.CFStrictGenericCharacterization
import BigHrushovski.CFRealBirthRecognition

/-!
# Strict C_F Fraisse genericity on an arbitrary countable carrier

The published countable strong Fraisse limit M_F is not intrinsically
presented on ℕ, whereas the verified countable strict genericity
criterion is. Rather than introduce an unrelated fixed vertex
numbering or a new Fraisse-limit constant, this module packages a
genuine enumeration and the finite characterization of the induced
Nat presentation.

The resulting isomorphism is between the actual labelled birth
carrier and the original comparison graph on its given vertex type.
It is not obtained by presupposing a graph isomorphism.

Infinitude is encoded exactly by the carrier equivalence, not by
mere countability. Under the published class assumptions, the
remaining task is to instantiate the comparison model M_F with this
strict finite recognition data, and derive the singleton level
requests from the C_F hypotheses.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

/-- A countable strict C_F generic on its actual carrier, described
by an enumeration together with the complete finite induced
strict d-closed genericity criterion. All countably infinite
presentations of the published Fraisse limit may be encoded this way,
but the structure does not assume a pre-existing isomorphism with
the canonical birth graph. -/
structure PresentedStrictGeneric
    (F : ℕ → ℝ) {V : Type*} (G : GraphOn V) where
  enumerate : ℕ ≃ V
  finite_data : HasCountableStrictGenericity F (G.pullback enumerate)

/-- For the chosen enumeration, the full finite strict genericity
criterion on the comparison graph is definitionally available. -/
theorem PresentedStrictGeneric.nat_characterization
    (F : ℕ → ℝ) {V : Type*} (G : GraphOn V)
    (h : PresentedStrictGeneric F G) :
    HasCountableStrictGenericity F (G.pullback h.enumerate) :=
  h.finite_data

end CFDClosedBackAndForth

namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- The actual birth graph is induced-isomorphic to every presented
countable strict C_F generic, on the latter's **original** carrier.
The singleton request and free-join assumptions remain explicit;
the comparison graph is not assumed isomorphic to the birth graph. -/
theorem realBirth_iso_presentedStrictGeneric
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hRequests : ∀ n : ℕ,
      Nonempty (CFStageCatalogue.StageRequest
        (stage (cardinalGrowth F)
          (cardinalGrowthBound F hMono hUnbounded) n).graph
        (CFStageCatalogue.GrowthAllowedLocal (cardinalGrowth F))
        (fun P => (cardinalGrowthBound F hMono hUnbounded) P.card)))
    {V : Type*} (G : GraphOn V)
    (hGeneric : PresentedStrictGeneric (cardinalGrowth F) G) :
    ∃ φ : RealBirthVertex F hMono hUnbounded ≃ V,
      ∀ x y : RealBirthVertex F hMono hUnbounded,
        (realCountableGraph F hMono hUnbounded).adj x y ↔
          G.adj (φ x) (φ y) := by
  obtain ⟨φ, hAdj⟩ :=
    realBirth_unique_of_requests_hasStrictGenericity
      F hZero hMono hUnbounded hFree hRequests
      (G.pullback hGeneric.enumerate) hGeneric.finite_data
  refine ⟨φ.trans hGeneric.enumerate, ?_⟩
  intro x y
  change (realCountableGraph F hMono hUnbounded).adj x y ↔
    (G.pullback hGeneric.enumerate).adj (φ x) (φ y)
  exact hAdj x y

end CFCoherentTower
end BigHrushovski
