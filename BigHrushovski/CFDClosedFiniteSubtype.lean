import BigHrushovski.CFDClosedTransport
import BigHrushovski.CFGrowthClass

/-!
# Finite induced subtypes of countable C_F graphs

A prescribed finite strict d-closed extension a ≤d b inside a graph
on ℕ is a genuinely finite graph on the subtype {v // v∈b}.
The old set a is represented by its literal filter in that subtype.

This file identifies the entire original finite target graph, its
growth inequality and the strict d-closed inclusion without any
arbitrary numbering. It is the source-restriction component needed
to apply the already proved arbitrary-finite response theorem to
finite intervals in a countable graph.
-/

namespace BigHrushovski
namespace CFDClosedFiniteSubtype

/-- The actual finite vertex type of an induced graph on b. -/
abbrev Carrier (b : Finset ℕ) := {v : ℕ // v ∈ b}

/-- The literal induced graph on b, with no fresh numbering. -/
noncomputable def graph (M : GraphOn ℕ) (b : Finset ℕ) :
    GraphOn (Carrier b) :=
  M.pullback (Subtype.val : Carrier b → ℕ)

/-- The literal old set a, represented inside the finite carrier b. -/
noncomputable def base (b a : Finset ℕ) : Finset (Carrier b) := by
  classical
  exact Finset.univ.filter (fun x : Carrier b => x.val ∈ a)

/-- The complete induced finite carrier maps back onto b. -/
theorem univ_image (b : Finset ℕ) :
    (Finset.univ : Finset (Carrier b)).image Subtype.val = b := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    exact x.property
  · intro hv
    exact Finset.mem_image.mpr
      ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

/-- The old set is exactly a, not an arbitrary isomorphic copy. -/
theorem base_image (b a : Finset ℕ) (hab : a ⊆ b) :
    (base b a).image (Subtype.val : Carrier b → ℕ) = a := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, hv⟩ := Finset.mem_image.mp hv
    have hxa : x.val ∈ a := (Finset.mem_filter.mp hx).2
    simpa [hv] using hxa
  · intro hv
    exact Finset.mem_image.mpr
      ⟨⟨v, hab hv⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩,
       rfl⟩

/-- Strict d-closedness is reflected and preserved by passage to
the whole finite induced subtype, including every intermediate
finite set of the original interval. -/
theorem dClosed_iff
    (M : GraphOn ℕ) (a b : Finset ℕ) (hab : a ⊆ b) :
    M.toPredimension.IsDClosed a b ↔
      (graph M b).toPredimension.IsDClosed
        (base b a) (Finset.univ : Finset (Carrier b)) := by
  classical
  have h :=
    (graph M b).dClosed_image_iff M
      (Subtype.val : Carrier b → ℕ)
      Subtype.val_injective
      (fun _ _ => Iff.rfl)
      (base b a) Finset.univ (Finset.subset_univ _)
  rw [base_image b a hab, univ_image b] at h
  exact h

/-- The finite growth inequality on b is exactly membership
of the whole induced finite-subtype graph in C_F. -/
theorem growthSparse_iff
    (M : GraphOn ℕ) (F : ℕ → ℝ) (b : Finset ℕ) :
    M.IsGrowthSparse F b ↔
      (graph M b).IsGrowthSparse F
        (Finset.univ : Finset (Carrier b)) := by
  classical
  have h :=
    (graph M b).growthSparse_image_iff M F
      (Subtype.val : Carrier b → ℕ)
      Subtype.val_injective
      (fun _ _ => Iff.rfl) Finset.univ
  rw [univ_image b] at h
  exact h

end CFDClosedFiniteSubtype
end BigHrushovski
