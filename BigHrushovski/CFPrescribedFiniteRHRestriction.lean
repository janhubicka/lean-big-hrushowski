import BigHrushovski.CFPrescribedFiniteRHComposition
import BigHrushovski.CFPrescribedFiniteLiftRestriction

/-!
# Restriction of prescribed finite C_F lifts in the R,H language

The already verified finite b-functional restriction theorem
identifies the restriction of a prescribed lift to a smaller
b-closed finite source with the independently constructed lift
of that source. The latter is an actual R,H-embedding, including
reflection of the domain of the partial hull operation H.

This is an immediate formal consequence of the two established
finite results; the proof does not replay the recursive lifting
construction or add a global level assignment.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Restricting a prescribed finite lift along the literal
inclusion s ⊆ t of finite b-closed sources preserves exact
R-values, all defined partial H-values, and reflects H's
domain on s.

Different finite stage covers may be chosen for s and t. The
proof identifies the restricted map with the canonical lift
of s by arbitrary-map finite uniqueness and applies the
verified R,H properties of that canonical lift. -/
theorem finiteSourcePrescribedLift_restriction_RHValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (ht : IsBirthBlockClosed F K t)
    (hst : s ⊆ t)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K t level)
    (nS nT : ℕ)
    (hCoverS : s ⊆ stageImage F K nS)
    (hCoverT : t ⊆ stageImage F K nT) :
    FiniteSourceRHValues F K s
      (fun x : SupportCarrier (Vertex F K) s =>
        finiteSourcePrescribedLift F K t ht level hStrict nT hCoverT
          (finiteClosedSourceInclusion F K s t hst x)) := by
  let hStrictS :=
    strictOnRepresented_of_subset F K s t hst level hStrict
  have hEq :
      (fun x : SupportCarrier (Vertex F K) s =>
        finiteSourcePrescribedLift F K t ht level hStrict nT hCoverT
          (finiteClosedSourceInclusion F K s t hst x)) =
      finiteSourcePrescribedLift F K s hs level hStrictS nS hCoverS :=
    finiteSourcePrescribedLift_restriction
      F K s t hs ht hst level hStrict nS nT hCoverS hCoverT
  rw [hEq]
  exact finiteSourcePrescribedLift_has_RHValues
    F K s hs level hStrictS nS hCoverS

end CFCoherentTower
end BigHrushovski
