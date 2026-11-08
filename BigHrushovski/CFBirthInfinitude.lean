import BigHrushovski.CFBirthCarrier
import Mathlib.Basic.Denumerable

/-!
# Infinitude and natural-number enumeration of the C_F birth carrier

The birth-labelled carrier is a sigma of finite fresh layers. Its
countability is already proved by CFBirthCarrier. Infinitude requires
more: the standing paper hypotheses must supply a nonempty request
at every level. The proof below isolates the exact remaining
finite-stage obligation instead of silently inferring infinitude
from countability.

Every actual StageRequest has a strictly positive fresh-block size,
by the verified minimal d-closed step condition. Consequently one
request per level supplies a distinct vertex born at that level.
Under this hypothesis the birth carrier is countably infinite and
admits a genuine equivalence with ℕ, as needed by the already
verified Nat-based strict d-closed back-and-forth theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Each actual finite-level request introduces at least one
fresh vertex. The size is positive because its local extension
is a *proper minimal* strict d-closed step. -/
theorem request_has_fresh_vertex
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : StageRequest (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)) :
    Nonempty (FreshAt F K n) := by
  exact ⟨⟨r, ⟨0, r.code.2.fresh_pos⟩⟩⟩

/-- If every stage has at least one actual permitted request,
the birth-labelled carrier contains a distinct vertex from
each level and is infinite. This statement does not replace
the separate paper assumptions ensuring that the singleton
request is present at every stage. -/
theorem birthVertex_infinite_of_requests
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hRequests : ∀ n : ℕ,
      Nonempty (StageRequest (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card))) :
    Infinite (Vertex F K) := by
  classical
  letI : ∀ n : ℕ, Nonempty (FreshAt F K n) := fun n =>
    request_has_fresh_vertex F K n (Classical.choice (hRequests n))
  infer_instance

/-- The exact precondition for identifying the C_F birth carrier
with ℕ: verified countability and conditional infinitude.
No dummy vertex or arbitrary extension of a partial map is used. -/
theorem natEquivBirth_nonempty_of_requests
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hRequests : ∀ n : ℕ,
      Nonempty (StageRequest (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card))) :
    Nonempty (ℕ ≃ Vertex F K) := by
  letI : Infinite (Vertex F K) :=
    birthVertex_infinite_of_requests F K hRequests
  infer_instance

/-- A selected global carrier equivalence, conditional on
actual requests at every finite level. -/
noncomputable def natEquivBirth_of_requests
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hRequests : ∀ n : ℕ,
      Nonempty (StageRequest (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card))) :
    ℕ ≃ Vertex F K :=
  Classical.choice (natEquivBirth_nonempty_of_requests F K hRequests)

end CFCoherentTower
end BigHrushovski
