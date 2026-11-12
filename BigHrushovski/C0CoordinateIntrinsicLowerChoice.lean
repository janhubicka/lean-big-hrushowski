import BigHrushovski.C0CoordinateLocalOrderChoice

/-!
# The lower part is intrinsic to complete unary values

The lower part in a rootless one-generated local representative
need not be retained as independent comparison data. The defining
conditions (complete C-closedness of the lower part, nonempty top,
and generation of the whole local carrier by every top vertex)
force exactly:

    u in lower  iff  C(u) is not the whole local carrier.

Consequently any bijection preserving and reflecting ALL complete
unary-value memberships between two local representatives already
preserves and reflects the lower part. This can shorten the
hereditary catalogue interface; it is not true for a positive-edge
map or a map preserving only inclusions of unary values.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U V : Type*}
variable [Fintype U] [DecidableEq U] [LinearOrder U]
variable [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The lower part is determined solely by the complete unary
function. No arbitrary point of the top component is named. -/
theorem LocalOrderedRepresentative.mem_lower_iff_value_ne_univ
    (r : LocalOrderedRepresentative U) (u : U) :
    u ∈ r.lower ↔ r.value u ≠ Finset.univ := by
  constructor
  · intro hu hAll
    obtain ⟨w, hw⟩ := r.top_nonempty
    have hwNot : w ∉ r.lower := (Finset.mem_sdiff.mp hw).2
    apply hwNot
    apply r.lower_closed u hu
    rw [hAll]
    exact Finset.mem_univ w
  · intro hNot
    by_contra hu
    exact hNot (r.top_generates u hu)

/-- Every bijection preserving the COMPLETE set-valued unary
structure between two local representatives automatically preserves
the intrinsic lower parts. No separate lower-compatibility hypothesis
or automorphism-invariance convention is necessary. -/
theorem LocalOrderedRepresentative.lower_iff_of_complete_values
    (r : LocalOrderedRepresentative U)
    (s : LocalOrderedRepresentative V)
    (e : U ≃ V)
    (hC : ∀ u v : U,
      v ∈ r.value u ↔ e v ∈ s.value (e u))
    (u : U) :
    u ∈ r.lower ↔ e u ∈ s.lower := by
  rw [r.mem_lower_iff_value_ne_univ u,
    s.mem_lower_iff_value_ne_univ (e u)]
  constructor
  · intro hNot hAll
    apply hNot
    ext v
    simp only [Finset.mem_univ, iff_true]
    apply (hC u v).mpr
    rw [hAll]
    exact Finset.mem_univ (e v)
  · intro hNot hAll
    apply hNot
    ext w
    simp only [Finset.mem_univ, iff_true]
    have hMem : e.symm w ∈ r.value u := by
      rw [hAll]
      exact Finset.mem_univ _
    have hw := (hC u (e.symm w)).mp hMem
    simpa only [e.apply_symm_apply] using hw

end FiniteUnaryCoordinates
end BigHrushovski
