import BigHrushovski.HrushovskiEllentuckGeneratedSupport
import BigHrushovski.CFBirthTopBlock

/-!
# Actual finite level supports on the C_F birth-labelled graph

For the constructed countable birth carrier the manuscript's support is
the set of birth levels of the complete finite generated b-closure.
The operation is not replaced by a vertex's own birth level.

All closure premises of the generic Track E support calculus follow
from the already kernel-verified least finite b-closed hull. Thus the
resulting support domains are really closed under the complete b-values.

We do not assert that every infinite support-saturated domain is the
range of a functional self-embedding, or that arbitrary increasing level
maps admit unique lifts. Those are separate Track B conclusions.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The original complete finite generated closure of a birth vertex. -/
noncomputable def birthSingletonClosure (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) : Finset (Vertex F K) :=
  birthGeneratedClosure F K ({v} : Finset (Vertex F K))

theorem birthSingletonClosure_self (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) : v ∈ birthSingletonClosure F K v := by
  exact (birthGeneratedClosure_contains F K ({v} : Finset (Vertex F K)))
    (Finset.mem_singleton_self v)

/-- Transitivity of the *complete* finite birth closure, derived from
minimality among finite b-closed sets, not imposed as a new assumption. -/
theorem birthSingletonClosure_trans (F : ℕ → ℝ) (K : ℕ → ℕ)
    {v w : Vertex F K} (hw : w ∈ birthSingletonClosure F K v) :
    birthSingletonClosure F K w ⊆ birthSingletonClosure F K v := by
  exact birthGeneratedClosure_le_of_closed F K
    ({w} : Finset (Vertex F K))
    (birthSingletonClosure F K v)
    (by simpa only [Finset.singleton_subset_iff] using hw)
    (birthGeneratedClosure_closed F K ({v} : Finset (Vertex F K)))

/-- Birth levels represented in the *whole* generated b-closure. -/
noncomputable def birthLevelSupport (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) : Finset ℕ :=
  Ellentuck.generatedSupport (birthSingletonClosure F K)
    (fun x : Vertex F K => x.1) v

theorem birthLevelSupport_mem_iff (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) (n : ℕ) :
    n ∈ birthLevelSupport F K v ↔
      ∃ w ∈ birthSingletonClosure F K v, w.1 = n := by
  exact Ellentuck.mem_generatedSupport (birthSingletonClosure F K)
    (fun x : Vertex F K => x.1) v n

theorem birthLevelSupport_self (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) :
    v.1 ∈ birthLevelSupport F K v :=
  Ellentuck.own_level_mem_generatedSupport
    (birthSingletonClosure F K)
    (fun x : Vertex F K => x.1)
    (birthSingletonClosure_self F K) v

theorem birthLevelSupport_subset_of_closure
    (F : ℕ → ℝ) (K : ℕ → ℕ) {v w : Vertex F K}
    (hw : w ∈ birthSingletonClosure F K v) :
    birthLevelSupport F K w ⊆ birthLevelSupport F K v :=
  Ellentuck.generatedSupport_subset_of_closure
    (birthSingletonClosure F K)
    (fun x : Vertex F K => x.1)
    (birthSingletonClosure_trans F K) hw

/-- The complete-support range for a selected set of birth levels. -/
def birthLevelDomain (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : Set ℕ) : Set (Vertex F K) :=
  Ellentuck.supportDomain (birthLevelSupport F K) S

/-- Supported vertex sets really are closed under the full generated
b-closure in the *actual* countable C_F birth construction. -/
theorem birthLevelDomain_generatedClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S : Set ℕ) :
    Ellentuck.IsUnaryClosed
      (fun x : Vertex F K => (↑(birthSingletonClosure F K x) : Set (Vertex F K)))
      (birthLevelDomain F K S) := by
  exact Ellentuck.generatedSupport_domain_closed
    (birthSingletonClosure F K)
    (fun x : Vertex F K => x.1)
    (birthSingletonClosure_trans F K) S

/-- Consequently the supported domain is closed under every complete
auxiliary b-value, not merely the immediate old-neighbour list. -/
theorem birthLevelDomain_bValueClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : Set ℕ) {v w : Vertex F K}
    (hv : v ∈ birthLevelDomain F K S)
    (hw : w ∈ birthBValue F K v) :
    w ∈ birthLevelDomain F K S := by
  have hb :
      birthBValue F K v ⊆ birthSingletonClosure F K v :=
    birthBValue_subset_of_closed F K
      (birthSingletonClosure F K v)
      (birthGeneratedClosure_closed F K ({v} : Finset (Vertex F K)))
      (birthSingletonClosure_self F K v)
  exact birthLevelDomain_generatedClosed F K S hv (hb hw)

/-- Empty represented level sets contain no birth vertices: every
vertex's own birth level is already in its complete support. -/
theorem birthLevelDomain_empty
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    birthLevelDomain F K (∅ : Set ℕ) = ∅ := by
  exact Ellentuck.generatedSupport_empty_domain
    (birthSingletonClosure F K)
    (fun x : Vertex F K => x.1)
    (birthSingletonClosure_self F K)

end CFCoherentTower
end BigHrushovski
