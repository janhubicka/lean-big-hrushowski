import BigHrushovski.CountableStrongLimit
import BigHrushovski.GenericityCriterion

/-!
# Fair responses pass from coherent finite graph stages to their union

The existing genericity criterion is stated for the direct-limit graph.
A recursive construction naturally tests applicability and realizes an
extension request in the *finite graph at the current stage*.

For coherent finite graph stages, induced adjacency agrees with the
limit on every finite stage, and the finite strongness predicate is
invariant under that agreement. We therefore transport applicability
from the limit to a finite stage and a finite-stage response back to
the limit. Combining this with the already verified fair-request
criterion yields the labelled strong extension property.

This is a conditional bridge. It does not construct the coherent
fair-response stages, whose finite recursive choice is still required.
-/

namespace BigHrushovski
namespace CoherentNatGraphStages

open FiniteCatalogue

variable (S : CoherentNatGraphStages)

/-- A request applicable in the union is also applicable when tested
against the finite stage that contains its source. -/
theorem appliesAt_stage_of_limit
    (n : ℕ) (req : ExtensionRequestCatalogue)
    (hApp : AppliesAt S.limitGraph (S.stage n) req) :
    AppliesAt (S.graph n) (S.stage n) req := by
  obtain ⟨hfInj, hfInd, hfStrong⟩ := hApp
  let source : Finset ℕ :=
    (Finset.univ : Finset (Fin req.1)).image req.2.2.2
  have hSource : source ⊆ S.stage n := hfStrong.1
  refine ⟨hfInj, ?_, ?_⟩
  · intro x y
    have hx : req.2.2.2 x ∈ S.stage n :=
      hSource (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    have hy : req.2.2.2 y ∈ S.stage n :=
      hSource (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
    exact (hfInd x y).trans (S.limitGraph_induced n hx hy)
  · exact
      (S.limitGraph.isStrong_iff_of_agreeOn (S.graph n)
        source (S.stage n) hSource
        (by
          intro x hx y hy
          exact S.limitGraph_induced n hx hy)).mp hfStrong

/-- A response strong in the next finite graph is a response in the
union, because the target lies entirely inside that next stage. -/
theorem respondsAt_limit_of_stage
    (n : ℕ) (req : ExtensionRequestCatalogue)
    (hAnswer : RespondsAt (S.graph n) (S.stage n) req) :
    RespondsAt S.limitGraph (S.stage n) req := by
  obtain ⟨g, hgInj, hgInd, hgBase, hgStrong⟩ := hAnswer
  let target : Finset ℕ :=
    (Finset.univ : Finset (Fin req.2.1)).image g
  have hTarget : target ⊆ S.stage n := hgStrong.1
  refine ⟨g, hgInj, ?_, hgBase, ?_⟩
  · intro x y
    have hx : g x ∈ S.stage n :=
      hTarget (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    have hy : g y ∈ S.stage n :=
      hTarget (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
    exact (hgInd x y).trans (S.limitGraph_induced n hx hy).symm
  · exact
      (S.limitGraph.isStrong_iff_of_agreeOn (S.graph n)
        target (S.stage n) hTarget
        (by
          intro x hx y hy
          exact S.limitGraph_induced n hx hy)).mpr hgStrong

/-- Local responses in each finite successor graph suffice for the
strong extension property of the countable coherent union. -/
theorem strongExtensionProperty_of_stageResponses
    (hStrong : S.HasStrongSteps)
    (hRespond : ∀ n : ℕ, ∀ req : ExtensionRequestCatalogue,
      fairRequest n = some req →
      AppliesAt (S.graph n) (S.stage n) req →
      RespondsAt (S.graph (n + 1)) (S.stage (n + 1)) req) :
    HasStrongExtensionProperty S.limitGraph := by
  apply strongExtensionProperty_of_fairResponses
    S.limitGraph (S.asStrongChain hStrong)
  intro n req hFair hApp
  have hStage := S.appliesAt_stage_of_limit n req hApp
  exact S.respondsAt_limit_of_stage (n + 1) req
    (hRespond n req hFair hStage)

end CoherentNatGraphStages
end BigHrushovski
