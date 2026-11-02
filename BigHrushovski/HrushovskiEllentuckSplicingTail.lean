import BigHrushovski.HrushovskiEllentuckSplicing

/-!
# Tail-extension transfer through the C₀ closure-splicing core

This is the remaining *structural* calculation in the manuscript's
A.3(2) argument. The closure-splicing core V need not be an arbitrary
copy of the entire structure; nevertheless it retains the ability
to realize every permitted ordered one-component type arbitrarily far
out, provided both X and Y have the prescribed extension property.

The abstract predicate `permitted P t` describes allowed component
extensions over the actual closed set P. The predicate `realizes P t B`
records the full ordered local type and the desired finite cutoff; in
concrete applications these must include all required adjacency,
function-value, nonedge and order conditions. Neither is silently
replaced by a finite-age Ramsey property.

The same closure equation Γ(b)=P∪B is used in the manuscript, with B
a nonempty finite component. A result for the actual C₀ functional
generic requires the separate Track A proof of its extension property.
-/

namespace BigHrushovski.Ellentuck

universe u v

variable {Vertex : Type u} {Request : Type v}

/-- Every finite closed lower set P in Z realizes all its permitted
ordered component requests t. A request can encode a cutoff, so the
same property expresses arbitrarily late extension types. -/
def HasOneComponentTails
    (Γ : Vertex → Set Vertex)
    (permitted : Set Vertex → Request → Prop)
    (realizes : Set Vertex → Request → Set Vertex → Prop)
    (Z : Set Vertex) : Prop :=
  ∀ (P : Set Vertex) (t : Request),
    P.Finite →
    IsUnaryClosed Γ P →
    P ⊆ Z →
    permitted P t →
    ∃ B : Set Vertex,
      B.Finite ∧
      B.Nonempty ∧
      B ⊆ Z ∧
      realizes P t B ∧
      (∀ b ∈ B, Γ b = P ∪ B)

/-- The C₀ A.3(2) spliced core retains the full extension property.
No component is constructed by a Ramsey theorem: according as P
avoids or meets D, we take an already available component in X or Y. -/
theorem splicedCore_hasOneComponentTails
    (Γ : Vertex → Set Vertex)
    (permitted : Set Vertex → Request → Prop)
    (realizes : Set Vertex → Request → Set Vertex → Prop)
    {X Y D : Set Vertex}
    (hrefl : ∀ v, v ∈ Γ v)
    (hXclosed : IsUnaryClosed Γ X)
    (hXY : X ⊆ Y)
    (hXtail : HasOneComponentTails Γ permitted realizes X)
    (hYtail : HasOneComponentTails Γ permitted realizes Y) :
    HasOneComponentTails Γ permitted realizes
      (splicedCore Γ Y X D) := by
  intro P t hPfinite hPclosed hPV hPermitted
  by_cases hMeet : ∃ d, d ∈ P ∧ d ∈ D
  · rcases hMeet with ⟨d, hdP, hdD⟩
    have hPY : P ⊆ Y := by
      intro p hp
      exact (hPV hp).1
    rcases hYtail P t hPfinite hPclosed hPY hPermitted with
      ⟨B, hBfinite, hBnonempty, hBY, hRealizes, hClosure⟩
    have hPW : P ⊆ forcedBody Γ Y X D := by
      intro p hp
      exact (hPV hp).2 (hrefl p)
    have hBW : B ⊆ forcedBody Γ Y X D := by
      intro b hb
      right
      refine ⟨hBY hb, d, ?_, hdD⟩
      rw [hClosure b hb]
      exact Or.inl hdP
    have hUnionW : P ∪ B ⊆ forcedBody Γ Y X D :=
      Set.union_subset hPW hBW
    have hBV : B ⊆ splicedCore Γ Y X D := by
      intro b hb
      refine ⟨hBY hb, ?_⟩
      rw [hClosure b hb]
      exact hUnionW
    exact ⟨B, hBfinite, hBnonempty, hBV, hRealizes, hClosure⟩
  · have hPD : Disjoint P D := by
      apply Set.disjoint_left.mpr
      intro d hdP hdD
      exact hMeet ⟨d, hdP, hdD⟩
    have hPX : P ⊆ X :=
      closed_subset_splicedCore_subset_X Γ hrefl hPclosed hPV hPD
    rcases hXtail P t hPfinite hPclosed hPX hPermitted with
      ⟨B, hBfinite, hBnonempty, hBX, hRealizes, hClosure⟩
    have hXV : X ⊆ splicedCore Γ Y X D :=
      subset_splicedCore_of_closed Γ hXclosed hXY
    exact ⟨B, hBfinite, hBnonempty,
      hBX.trans hXV, hRealizes, hClosure⟩

end BigHrushovski.Ellentuck
