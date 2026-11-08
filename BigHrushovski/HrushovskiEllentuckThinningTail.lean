import BigHrushovski.HrushovskiEllentuckSplicingTail
import BigHrushovski.HrushovskiEllentuckThinning

/-!
# One-component tail extensions after the C₀ A.4 thinning

In the manuscript's relative pigeonhole argument, the nonselected
candidates of one *exact* local type are removed together with every
vertex depending on them. The remaining closed set must still have
arbitrarily late realizations of every permitted one-component type.

There are exactly two sources of realizations. For the selected local
type, the monochromatic infinite set H provides arbitrarily late
components avoiding the deleted set. For every other local type,
uniqueness of the complete ordered local type guarantees that each
ambient realization is disjoint from the deleted candidates.

The present theorem isolates this transfer without claiming the
infinite pigeonhole step, uniqueness of C₀ component types, or the
countable functional extension property. Those remain explicit
assumptions to be supplied in the concrete instance.
-/

namespace BigHrushovski.Ellentuck

universe u v
variable {Vertex : Type u} {Request : Type v}

/-- A component with full closure Γ(b) = P ∪ B is retained by the
dependency-thinning core whenever P was retained and no vertex of
B was deleted. The assumption b∈Γ(b) is needed to keep P disjoint
from deleted vertices without silently assuming an irrefl. closure. -/
theorem component_subset_thinningCore
    (Γ : Vertex → Set Vertex)
    {Y U P B : Set Vertex}
    (hrefl : ∀ v, v ∈ Γ v)
    (hPV : P ⊆ thinningCore Γ Y U)
    (hBY : B ⊆ Y)
    (hBU : Disjoint B U)
    (hClosure : ∀ b ∈ B, Γ b = P ∪ B) :
    B ⊆ thinningCore Γ Y U := by
  intro b hb
  refine ⟨hBY hb, ?_⟩
  intro w hw hwU
  rw [hClosure b hb] at hw
  rcases hw with hwP | hwB
  · exact (hPV hwP).2 w (hrefl w) hwU
  · exact (Set.disjoint_left.mp hBU) hwB hwU

/-- The relative A.4 thinning retains every permitted one-component
extension, provided that (i) the infinitely selected candidates supply
the distinguished exact local type and (ii) realizations of every
other local type avoid the deleted candidates. These two requirements
are the actual infinitary pigeonhole and uniqueness inputs of the
manuscript, not consequences of the elementary closure calculation. -/
theorem thinningCore_hasOneComponentTails
    (Γ : Vertex → Set Vertex)
    (permitted : Set Vertex → Request → Prop)
    (realizes : Set Vertex → Request → Set Vertex → Prop)
    (selectedType : Set Vertex → Request → Prop)
    {Y U : Set Vertex}
    (hrefl : ∀ v, v ∈ Γ v)
    (hYtail : HasOneComponentTails Γ permitted realizes Y)
    (hSelectedTail :
      ∀ (P : Set Vertex) (t : Request),
        P.Finite →
        IsUnaryClosed Γ P →
        P ⊆ thinningCore Γ Y U →
        permitted P t →
        selectedType P t →
        ∃ B : Set Vertex,
          B.Finite ∧
          B.Nonempty ∧
          B ⊆ Y ∧
          realizes P t B ∧
          (∀ b ∈ B, Γ b = P ∪ B) ∧
          Disjoint B U)
    (hOtherAvoid :
      ∀ (P : Set Vertex) (t : Request) (B : Set Vertex),
        realizes P t B →
        ¬ selectedType P t →
        Disjoint B U) :
    HasOneComponentTails Γ permitted realizes
      (thinningCore Γ Y U) := by
  intro P t hFinite hClosed hPV hPermit
  by_cases hSelected : selectedType P t
  · obtain ⟨B, hBFinite, hBNonempty, hBY, hReal, hClosure, hBU⟩ :=
      hSelectedTail P t hFinite hClosed hPV hPermit hSelected
    have hBV : B ⊆ thinningCore Γ Y U :=
      component_subset_thinningCore Γ hrefl hPV hBY hBU hClosure
    exact ⟨B, hBFinite, hBNonempty, hBV, hReal, hClosure⟩
  · have hPY : P ⊆ Y := by
      intro p hp
      exact (hPV hp).1
    obtain ⟨B, hBFinite, hBNonempty, hBY, hReal, hClosure⟩ :=
      hYtail P t hFinite hClosed hPY hPermit
    have hBU : Disjoint B U :=
      hOtherAvoid P t B hReal hSelected
    have hBV : B ⊆ thinningCore Γ Y U :=
      component_subset_thinningCore Γ hrefl hPV hBY hBU hClosure
    exact ⟨B, hBFinite, hBNonempty, hBV, hReal, hClosure⟩

end BigHrushovski.Ellentuck
