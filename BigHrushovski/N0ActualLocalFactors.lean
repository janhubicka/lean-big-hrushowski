import BigHrushovski.N0ComponentLinearExtensions
import BigHrushovski.OrientationInducedFinite
import BigHrushovski.N0LocalCodeFibre
import Mathlib.Tactic

/-!
# The actual local factors in the finite N₀ count

Let B be a strongly connected component of a finite orientation.
The factor g_A(B) is the number of automorphisms of the *induced*
orientation on C_B = scl(B) fixing P_B = C_B \ B pointwise.
It is not the number of automorphisms of the ambient orientation.

We define this factor and identify it with the cardinality of a
complete local adjacency-code fibre. This is independent of the
choice of the vertex representing B.

The resulting product is a count of finite component-order data.
Identifying those data with the complete permitted vertex orders,
and the infinite big Ramsey theorem, remain separate obligations.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The orientation induced by O on the complete successor
closure of the strongly connected component containing x. -/
noncomputable def inducedComponentOrientation (x : V) :
    FiniteOrientation (O.componentClosure x) :=
  O.inducedFinite (O.componentClosure x)

/-- The actual strict lower part P_B, regarded as a vertex set
of the induced orientation on C_B. -/
noncomputable def inducedLowerPart (x : V) :
    Finset (O.componentClosure x) := by
  classical
  exact Finset.univ.filter
    (fun y : O.componentClosure x => y.val ∈ O.lowerPart x)

theorem mem_inducedLowerPart_iff (x : V)
    (y : O.componentClosure x) :
    y ∈ O.inducedLowerPart x ↔ y.val ∈ O.lowerPart x := by
  classical
  simp [inducedLowerPart]

/-- The complete component closure is successor-closed
in the original finite orientation. -/
theorem componentClosure_isSuccessorClosed (x : V) :
    O.IsSuccessorClosed (O.componentClosure x) :=
  O.successorClosure_isClosed (O.component x)

/-- Inducing on a closed component closure retains every
outgoing-neighbour value, not merely induced positive edges. -/
theorem inducedComponentOrientation_full_out
    (x : V) (u : O.componentClosure x) (v : V)
    (hv : v ∈ O.out u.val) :
    ∃ w : O.componentClosure x,
      w.val = v ∧ w ∈ (O.inducedComponentOrientation x).out u := by
  exact O.inducedFinite_full_out_of_closed
    (O.componentClosure x)
    (O.componentClosure_isSuccessorClosed x) u v hv

/-- The lower part is successor-closed in the *induced*
orientation on its complete one-component closure. -/
theorem inducedLowerPart_isSuccessorClosed (x : V) :
    (O.inducedComponentOrientation x).IsSuccessorClosed
      (O.inducedLowerPart x) := by
  intro u hu v hv
  have huP : u.val ∈ O.lowerPart x :=
    (O.mem_inducedLowerPart_iff x u).mp hu
  have hvO : v.val ∈ O.out u.val :=
    (O.inducedFinite_out_iff (O.componentClosure x) u v).mp hv
  exact (O.mem_inducedLowerPart_iff x v).mpr
    (O.lowerPart_isSuccessorClosed x u.val huP hvO)

/-- The finite pointwise stabilizer in the **induced closure**,
with all arrows preserved and every vertex of P_B fixed. -/
noncomputable def actualLocalStabilizer (x : V) :
    Finset (Equiv.Perm (O.componentClosure x)) :=
  (O.inducedComponentOrientation x).pointwiseLowerAutomorphisms
    (O.inducedLowerPart x)

/-- The actual local multiplicity of the component containing x. -/
noncomputable def actualLocalFactor (x : V) : ℕ :=
  (O.actualLocalStabilizer x).card

theorem actualLocalFactor_pos (x : V) :
    0 < O.actualLocalFactor x := by
  have h : (O.actualLocalStabilizer x).Nonempty :=
    (O.inducedComponentOrientation x).pointwiseLowerAutomorphisms_nonempty
      (O.inducedLowerPart x)
  exact Finset.card_pos.mpr h

/-- The local multiplicity depends only on the SCC, not on
the choice of a generator in that component. -/
theorem actualLocalFactor_eq_of_stronglyConnected
    {x y : V} (hxy : O.StronglyConnected x y) :
    O.actualLocalFactor x = O.actualLocalFactor y := by
  have hc : O.componentClosure x = O.componentClosure y :=
    O.componentClosure_eq_of_stronglyConnected hxy
  have hp : O.lowerPart x = O.lowerPart y :=
    O.lowerPart_eq_of_stronglyConnected hxy
  simp only [actualLocalFactor, actualLocalStabilizer,
    inducedComponentOrientation, inducedLowerPart]
  rw [← hc, ← hp]

/-- Every component has an actual generator. -/
theorem exists_component_generator (B : O.ComponentObject) :
    ∃ x : V, O.component x = B.val := by
  have hB : B.val ∈ O.components := B.property
  change B.val ∈ (Finset.univ : Finset V).image O.component at hB
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hB
  exact ⟨x, hx⟩

/-- Choose a component representative for defining g_A(B);
its choice does not affect the resulting number. -/
noncomputable def componentGenerator (B : O.ComponentObject) : V :=
  Classical.choose (O.exists_component_generator B)

theorem componentGenerator_spec (B : O.ComponentObject) :
    O.component (O.componentGenerator B) = B.val :=
  Classical.choose_spec (O.exists_component_generator B)

/-- The precise finite local stabilizer factor g_A(B). -/
noncomputable def componentLocalFactor (B : O.ComponentObject) : ℕ :=
  O.actualLocalFactor (O.componentGenerator B)

theorem componentLocalFactor_eq_of_generator
    (B : O.ComponentObject) {x : V}
    (hx : O.component x = B.val) :
    O.actualLocalFactor x = O.componentLocalFactor B := by
  have hsc : O.StronglyConnected x (O.componentGenerator B) :=
    (O.stronglyConnected_iff_component_eq
      x (O.componentGenerator B)).mpr
      (hx.trans (O.componentGenerator_spec B).symm)
  exact O.actualLocalFactor_eq_of_stronglyConnected hsc

/-- The local code fibre in the true induced orientation has
exactly the g-factor for the component of x. -/
theorem actualComponentCodeFibre_card
    (x : V) {n : ℕ}
    (e : Fin n ≃ O.componentClosure x) :
    ((O.inducedComponentOrientation x).localCodeFibre
      (O.inducedLowerPart x) e).card = O.actualLocalFactor x := by
  exact (O.inducedComponentOrientation x).localCodeFibre_card
    (O.inducedLowerPart x) e

/-- The finite product appearing in the manuscript's N₀ formula.
This is a combinatorial *candidate*, not a proven big Ramsey degree. -/
noncomputable def finiteComponentTypeCount : ℕ :=
  O.componentLinearExtensionCount *
    ∏ B : O.ComponentObject, O.componentLocalFactor B

/-- Independent finite choice sets with the correct local cardinalities.
The choices are numbers here; identification with permitted local
orders remains the missing bijection. -/
noncomputable def componentFactorChoiceSets
    (B : O.ComponentObject) : Finset ℕ :=
  Finset.range (O.componentLocalFactor B)

noncomputable def actualFiniteComponentData :
    Finset (O.ComponentRanking × O.ComponentAssignments ℕ) :=
  O.finiteOrderData O.componentFactorChoiceSets

/-- The exact finite factor product counts the data above. This
does not equate them with actual linear orders on the vertex set. -/
theorem actualFiniteComponentData_card :
    (O.actualFiniteComponentData).card =
      O.finiteComponentTypeCount := by
  have h := O.finiteOrderData_card O.componentFactorChoiceSets
  simpa [actualFiniteComponentData,
    finiteComponentTypeCount, componentFactorChoiceSets] using h

end FiniteOrientation
end BigHrushovski
