import BigHrushovski.C0CoordinateNestedLocalOrders

/-!
# The hereditary family of actual finite C₀ local occurrences

Fix a single finite canonical C₀ presentation (G, κ), with its
inherited vertex order. For each a, its literal finite one-generated
closure C(a) is a local occurrence. Whenever b belongs to C(a), the
inclusion C(b) -> C(a) is uniquely determined by the vertices
themselves. It preserves and reflects the induced graph and inherited
order, and carries the COMPLETE C and J values exactly.

The inclusions compose strictly: restricting first to C(b) and then
to C(c) is the same as restricting directly to C(c). Consequently
all actual local occurrences within one finite presentation form a
hereditary family without any representative choices.

This does NOT prove that orders selected independently for the same
unordered type in DIFFERENT presentations agree. A uniform coherent
catalogue for the entire finite C₀ age remains a separate obligation.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {n : ℕ}

/-- Any map to a larger one-generated closure that is literally
the identity on underlying vertices is the canonical inclusion. -/
theorem canonicalLocalInclusion_unique
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a)
    (f : FiniteC0.canonicalValue G κ b.val →
      FiniteC0.canonicalValue G κ a)
    (hf : ∀ u, (f u).val = u.val) :
    f = canonicalLocalInclusion G κ a b := by
  funext u
  exact Subtype.ext (hf u)

/-- Two successive local restrictions equal the direct one, with
literal equality of subtype elements and without re-numbering the
ambient graph or components. -/
theorem canonicalLocalInclusion_comp
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a)
    (c : FiniteC0.canonicalValue G κ b.val)
    (u : FiniteC0.canonicalValue G κ c.val) :
    canonicalLocalInclusion G κ a b
      (canonicalLocalInclusion G κ b.val c u) =
      canonicalLocalInclusion G κ a
        ⟨c.val, FiniteC0.canonicalValue_mem_trans
          G κ b.property c.property⟩ u := by
  exact Subtype.ext rfl

/-- A single finite canonical presentation gives a hereditary family
of actual local ordered occurrences. Every relevant property is an
equivalence or an equality, not merely positive preservation.

The lower part of C(b) is characterized intrinsically using the
complete C-values inside C(a), so no chosen component numbering is
used in the comparison statement. -/
theorem canonicalLocalOccurrence_hereditary
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a) :
    (∀ u v : FiniteC0.canonicalValue G κ b.val,
      u < v ↔ canonicalLocalInclusion G κ a b u <
        canonicalLocalInclusion G κ a b v) ∧
    (∀ u v : FiniteC0.canonicalValue G κ b.val,
      (restrictGraph G (FiniteC0.canonicalValue G κ b.val)).adj u v ↔
      (restrictGraph G (FiniteC0.canonicalValue G κ a)).adj
        (canonicalLocalInclusion G κ a b u)
        (canonicalLocalInclusion G κ a b v)) ∧
    (∀ u : FiniteC0.canonicalValue G κ b.val,
      (restrictValue (FiniteC0.canonicalValue G κ)
        (FiniteC0.canonicalValue G κ b.val) u).image
          (canonicalLocalInclusion G κ a b) =
      restrictValue (FiniteC0.canonicalValue G κ)
        (FiniteC0.canonicalValue G κ a)
        (canonicalLocalInclusion G κ a b u)) ∧
    (∀ u : FiniteC0.canonicalValue G κ b.val,
      ((GraphOn.backAdjacencyValue
        (restrictGraph G (FiniteC0.canonicalValue G κ b.val))
        (restrictValue (FiniteC0.canonicalValue G κ)
          (FiniteC0.canonicalValue G κ b.val)) u).image
          (canonicalLocalInclusion G κ a b)) =
      GraphOn.backAdjacencyValue
        (restrictGraph G (FiniteC0.canonicalValue G κ a))
        (restrictValue (FiniteC0.canonicalValue G κ)
          (FiniteC0.canonicalValue G κ a))
        (canonicalLocalInclusion G κ a b u)) ∧
    (∀ u : FiniteC0.canonicalValue G κ b.val,
      u ∈ canonicalLocalLower G κ b.val ↔
      restrictValue (FiniteC0.canonicalValue G κ)
        (FiniteC0.canonicalValue G κ a)
        (canonicalLocalInclusion G κ a b u) ≠
      restrictValue (FiniteC0.canonicalValue G κ)
        (FiniteC0.canonicalValue G κ a) b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact (canonicalLocalInclusion_lt_iff G κ a b u v).symm
  · intro u v
    exact canonicalLocalInclusion_adj_iff G κ a b u v
  · intro u
    exact canonicalLocalInclusion_C_image G κ a b u
  · intro u
    exact canonicalLocalInclusion_J_image G κ a b u
  · intro u
    exact canonicalLocalInclusion_lower_iff G κ a b u

end FiniteUnaryCoordinates
end BigHrushovski
