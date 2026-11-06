import BigHrushovski.C0FunctionalFairSuccessor
import BigHrushovski.TrivialStrongRequest
import BigHrushovski.NatStageCoverage

/-!
# Recursive finite functional C₀ stages answering fair requests

The finite predecessor module supplies a strictly growing
functional successor for every finite canonical stage and every
schedule index. Starting from the actual empty canonical finite
structure, choose a successor at each step by ordinary Nat recursion.

No countable generic or functional Fraïssé limit is assumed as
input. We retain the precise successor certificates, prove
unbounded stage sizes and exact response to every applicable
request at its scheduled step. Passing these finite certificates
to coherent countable graph and unary operations is separate.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- The empty graph with the unique empty component index is a
genuine finite canonical C₀ presentation. -/
def empty : FiniteFunctionalNatStage where
  size := 0
  blocks := 0
  model :=
    { graph := emptyFinGraph
      index := fun x : Fin 0 => Fin.elim0 x
      minimal := by
        intro j hj
        omega }

/-- Choose each next finite canonical stage by the previously
certified existence theorem. This is a genuine definition of
a Nat-indexed sequence, not an assumed fair-response chain. -/
noncomputable def chooseFairSuccessor
    (step : ℕ) (s : FiniteFunctionalNatStage) :
    Σ t : FiniteFunctionalNatStage,
      IsFairFunctionalSuccessor step s t :=
  Classical.choice (exists_fairFunctionalSuccessor step s)

noncomputable def fairStages : ℕ → FiniteFunctionalNatStage :=
  Nat.rec empty
    (fun step s => (chooseFairSuccessor step s).1)

/-- The recursively chosen successor retains every exact
finite response, growth and old-value certificate. The witness
is the one used in the actual recursive sequence. -/
noncomputable def fairStages_step (step : ℕ) :
    IsFairFunctionalSuccessor step
      (fairStages step) (fairStages (step+1)) := by
  change IsFairFunctionalSuccessor step (fairStages step)
    (chooseFairSuccessor step (fairStages step)).1
  exact (chooseFairSuccessor step (fairStages step)).2

/-- Every chosen stage is strictly larger than its predecessor. -/
theorem fairStages_grows (step : ℕ) :
    (fairStages step).size < (fairStages (step+1)).size :=
  (fairStages_step step).grows

/-- The stage sizes tend to infinity; all natural coordinates
eventually occur in the finite initial-segment carriers. -/
theorem fairStages_covers (x : ℕ) :
    ∃ step : ℕ, x ∈
      Finset.range (fairStages step).size := by
  exact FiniteSpan.initialSegment_stages_cover
    (fun n => (fairStages n).size)
    fairStages_grows x

/-- Every finite set of numeric vertices is contained in a
single finite canonical stage. -/
theorem fairStages_contains_finite (s : Finset ℕ) :
    ∃ step : ℕ, s ⊆
      Finset.range (fairStages step).size := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, Finset.empty_subset _⟩
  | @insert x s _ ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, hj⟩ := fairStages_covers x
      let size : ℕ → ℕ := fun k => (fairStages k).size
      have hMono : ∀ a b : ℕ, a ≤ b → size a ≤ size b := by
        intro a b hab
        induction b with
        | zero =>
            have ha : a = 0 := by omega
            subst a
            exact le_refl _
        | succ b hb =>
            by_cases hle : a ≤ b
            · exact (hb hle).trans
                (Nat.le_of_lt (fairStages_grows b))
            · have ha : a = b + 1 := by omega
              subst a
              exact le_refl _
      refine ⟨max i j, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with hyx | hys
      · subst y
        exact Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hj)
            (hMono j (max i j) (Nat.le_max_right i j)))
      · exact Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp (hi hys))
            (hMono i (max i j) (Nat.le_max_left i j)))

/-- A scheduled request is actually answered at the next finite
stage whenever its entire source embeds functionally at this step. -/
theorem fairStages_responds
    (step : ℕ) (req : FunctionalC0RequestCatalogue)
    (hFair : fairFunctionalC0Request step = some req)
    (hApp : (fairStages step).Applies req) :
    (fairStages (step+1)).Responds req :=
  (fairStages_step step).responds req hFair hApp

/-- The selected finite old stage is strong in its successor.
It is not necessary to infer this from countable genericity. -/
theorem fairStages_old_strong (step : ℕ) :
    (fairStages (step+1)).model.graph.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin (fairStages step).size)).image
        (fairStages_step step).old)
      Finset.univ :=
  (fairStages_step step).old_strong

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
