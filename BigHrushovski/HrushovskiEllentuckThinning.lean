import BigHrushovski.HrushovskiEllentuckSplicing

/-!
# Closure thinning used by the relative A.4 argument for C₀

The manuscript deletes the nonselected one-component candidates, together
with every vertex whose complete unary closure meets the deleted set.

The resulting set-theoretic construction is closed, retains every closed
prefix disjoint from the deleted set, and excludes all vertices with a
deleted dependency. This is the closure half of A.4, *not* its infinite
pigeonhole or tail-extension argument.
-/

namespace BigHrushovski.Ellentuck

universe u

variable {Vertex : Type u} (Γ : Vertex → Set Vertex)

/-- Keep only vertices belonging to Y whose complete closure avoids U. -/
def thinningCore (Y U : Set Vertex) : Set Vertex :=
  {v | v ∈ Y ∧ ∀ w ∈ Γ v, w ∉ U}

theorem thinningCore_subset_ambient (Y U : Set Vertex) :
    thinningCore Γ Y U ⊆ Y :=
  fun _ hv => hv.1

/-- Deleting all vertices dependent on U preserves unary closedness. -/
theorem thinningCore_closed
    {Y U : Set Vertex}
    (hY : IsUnaryClosed Γ Y)
    (htrans : ∀ v w, w ∈ Γ v → Γ w ⊆ Γ v) :
    IsUnaryClosed Γ (thinningCore Γ Y U) := by
  intro v hv w hw
  refine ⟨hY hv.1 hw, ?_⟩
  intro t ht htU
  exact hv.2 t (htrans v w hw ht) htU

/-- The retained core avoids all deleted vertices (reflexivity is needed). -/
theorem thinningCore_disjoint
    {Y U : Set Vertex} (hrefl : ∀ v, v ∈ Γ v) :
    Disjoint (thinningCore Γ Y U) U := by
  apply Set.disjoint_left.mpr
  intro v hv hvU
  exact hv.2 v (hrefl v) hvU

/-- Every closed subset disjoint from U remains in the core; this is
the part of the relative A.4 proof that retains the entire depth prefix. -/
theorem closed_subset_thinningCore
    {Y U C : Set Vertex}
    (hC : IsUnaryClosed Γ C)
    (hCY : C ⊆ Y)
    (hCU : Disjoint C U) :
    C ⊆ thinningCore Γ Y U := by
  intro v hv
  refine ⟨hCY hv, ?_⟩
  intro w hw hwU
  exact (Set.disjoint_left.mp hCU) (hC hv hw) hwU

/-- Every vertex whose full closure meets U is excluded. -/
theorem thinningCore_rejects_dependency
    {Y U : Set Vertex} {v w : Vertex}
    (hw : w ∈ Γ v) (hwU : w ∈ U) :
    v ∉ thinningCore Γ Y U := by
  intro hv
  exact hv.2 w hw hwU

end BigHrushovski.Ellentuck
