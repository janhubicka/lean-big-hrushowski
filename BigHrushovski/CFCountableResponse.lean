import BigHrushovski.CFCountableDClosedChain
import BigHrushovski.CFOneLevelResponse

/-!
# Global d-closed responses for the actual countable C_F tower

A finite d-closed subset of a stage remains d-closed in the
entire countable birth graph. Indeed, the finite stage is induced
in the countable graph and globally d-closed there.

Consequently the actual tagged request for any admissible ordered
minimal local extension over a named support P can be used to
produce a *globally* d-closed response over any old d-closed
set A containing P. The complete code, including its nonedges,
is preserved in the countable graph.

The theorem is an exact conditional local-response endpoint.
It does not assert that an arbitrary minimal extension has
already been normalized to one of these codes: adequacy of the
finite size bound K, and transport of a prescribed arbitrary
finite extension into the named local code, remain necessary.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every d-closed subset of a finite stage is globally
strictly d-closed in the countable birth graph. In particular
the result does not depend on a choice of a later stage. -/
theorem finiteClosedPart_global
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (a : Finset (stage F K n).carrier)
    (ha : (stage F K n).graph.toPredimension.IsDClosed
      a Finset.univ) :
    (countableGraph F K).toPredimension.IsGloballyDClosed
      (a.image (toVertex F K n)) := by
  classical
  have hFinite :
      (countableGraph F K).toPredimension.IsDClosed
        (a.image (toVertex F K n)) (stageImage F K n) := by
    exact (((stage F K n).graph).dClosed_image_iff
      (countableGraph F K)
      (toVertex F K n) (toVertex_injective F K n)
      (fun x y => (countableGraph_stage_induced F K n x y).symm)
      a Finset.univ (Finset.subset_univ _)).mpr ha
  exact (countableGraph F K).toPredimension
    |>.globallyDClosed_of_dClosed_in_global
      hFinite (stageImage_global_dClosed F K n)

/-- In the countable graph the precise fresh block for a
permitted named-support local type produces a globally
strictly d-closed extension of the chosen old d-closed A.

The second conclusion gives the full induced adjacency
equivalence on the local code (hence also preserves nonedges).
The conclusion is *not* yet the global extension property
for arbitrary finite diagrams: those first need to be
normalized, shown admissible, and bounded by K. -/
theorem orderedCode_globalResponse
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (a P : Finset (stage F K n).carrier)
    (ha : (stage F K n).graph.toPredimension.IsDClosed
      a Finset.univ)
    (hP : (stage F K n).graph.toPredimension.IsDClosed
      P Finset.univ)
    (hPA : P ⊆ a)
    (m : ℕ) (hm : m ≤ K P.card)
    (t : CFLocalCatalogue.OrderedLocalType
      (SupportCarrier (stage F K n).carrier P)
      (supportGraph (stage F K n).graph P)
      (GrowthAllowedLocal F P) m) :
    let G := (stage F K n).graph
    let allowed := GrowthAllowedLocal F
    let bound : Finset (stage F K n).carrier → ℕ :=
      fun Q => K Q.card
    let r := requestOfOrderedLocal G allowed bound
      P hP m hm t
    (countableGraph F K).toPredimension.IsGloballyDClosed
      ((a.image Sum.inl ∪ taggedBlock G allowed bound r).image
        (toVertex F K (n + 1))) ∧
      (∀ x y :
          Sum (SupportCarrier (stage F K n).carrier P) (Fin m),
        t.graph.adj x y ↔
          (countableGraph F K).adj
            (toVertex F K (n + 1)
              (localTag G allowed bound r x))
            (toVertex F K (n + 1)
              (localTag G allowed bound r y))) := by
  classical
  dsimp only
  let G := (stage F K n).graph
  let allowed := GrowthAllowedLocal F
  let bound : Finset (stage F K n).carrier → ℕ :=
    fun Q => K Q.card
  let r := requestOfOrderedLocal G allowed bound
    P hP m hm t
  have hFinite := orderedCode_oneLevelResponse
    G allowed bound a P ha hP hPA m hm t
  have hClosed :
      (stage F K (n + 1)).graph.toPredimension.IsDClosed
        (a.image Sum.inl ∪ taggedBlock G allowed bound r)
        Finset.univ := hFinite.1
  constructor
  · exact finiteClosedPart_global F K (n + 1)
      (a.image Sum.inl ∪ taggedBlock G allowed bound r) hClosed
  · intro x y
    exact (hFinite.2 x y).trans
      (countableGraph_stage_induced F K (n + 1)
        (localTag G allowed bound r x)
        (localTag G allowed bound r y)).symm

end CFCoherentTower
end BigHrushovski
