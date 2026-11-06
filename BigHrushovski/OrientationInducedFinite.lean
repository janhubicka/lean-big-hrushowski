import BigHrushovski.OrientationRelativeStrong
import Mathlib.Tactic

/-!
# Induced finite orientations and closed embeddings

The orientation on a finite vertex set s is given by retaining
exactly the arrows whose head and tail both lie in s. This gives
an orientation even when s is not successor-closed; in that case
it may lose outgoing neighbours of old vertices.

If s is successor-closed, the induced finite orientation records
the *complete* outgoing-neighbour set of each vertex. This is the
finite restriction needed for the actual pointwise stabilizers of
the one-component successor closures C_B in the N₀ degree formula.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The genuine induced orientation on the subtype of a finite
vertex set. No closure assumption is needed to form it. -/
noncomputable def inducedFinite (s : Finset V) : FiniteOrientation s where
  out := fun x =>
    Finset.univ.filter (fun y : s => y.val ∈ O.out x.val)
  noLoop := by
    intro x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (O.noLoop x.val)
  noOpposite := by
    intro x y hxy
    have hxyV : y.val ∈ O.out x.val := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hxy
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (O.noOpposite x.val y.val hxyV)
  outDegreeTwo := by
    intro x
    let T : Finset s :=
      Finset.univ.filter (fun y : s => y.val ∈ O.out x.val)
    have hSub : (T.image (fun y : s => (y : V))) ⊆ O.out x.val := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    have hInj : Set.InjOn (fun y : s => (y : V)) T := by
      intro a ha b hb hab
      exact Subtype.ext hab
    have hCard : (T.image (fun y : s => (y : V))).card = T.card :=
      Finset.card_image_iff.mpr hInj
    change T.card ≤ 2
    rw [← hCard]
    exact (Finset.card_le_card hSub).trans (O.outDegreeTwo x.val)

/-- Directed adjacency is preserved and reflected by induced
substructures, including nonedges and loops (which are absent). -/
theorem inducedFinite_out_iff (s : Finset V)
    (x y : s) :
    y ∈ (O.inducedFinite s).out x ↔ y.val ∈ O.out x.val := by
  simp [inducedFinite]

theorem inducedFinite_adj_iff (s : Finset V)
    (x y : s) :
    (O.inducedFinite s).Adjacent x y ↔ O.Adjacent x.val y.val := by
  change (y ∈ (O.inducedFinite s).out x ∨
    x ∈ (O.inducedFinite s).out y) ↔
    (y.val ∈ O.out x.val ∨ x.val ∈ O.out y.val)
  exact or_congr
    (O.inducedFinite_out_iff s x y)
    (O.inducedFinite_out_iff s y x)

/-- In a successor-closed set every old outgoing arrow is
represented in the induced orientation, with its actual head. -/
theorem inducedFinite_full_out_of_closed
    (s : Finset V) (hs : O.IsSuccessorClosed s)
    (x : s) (y : V) (hy : y ∈ O.out x.val) :
    ∃ z : s, z.val = y ∧ z ∈ (O.inducedFinite s).out x := by
  have hyS : y ∈ s := hs x.val x.property hy
  refine ⟨⟨y, hyS⟩, rfl, ?_⟩
  exact (O.inducedFinite_out_iff s x ⟨y, hyS⟩).mpr hy

/-- The induced orientation always retains each outgoing arrow
which ends inside the selected vertex set. -/
theorem inducedFinite_out_of_ambient
    (s : Finset V) (x y : s)
    (h : y.val ∈ O.out x.val) :
    y ∈ (O.inducedFinite s).out x :=
  (O.inducedFinite_out_iff s x y).mpr h

end FiniteOrientation
end BigHrushovski
